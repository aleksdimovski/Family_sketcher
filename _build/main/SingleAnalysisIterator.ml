(***************************************************)
(*                                                 *)
(*    Forward/Backward Single Analysis Iterator    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Iterator
open Partition

module SingleAnalysisIterator (B: PARTITION) =
struct

  module B = B

  let fwdInvMap = ref InvMap.empty

  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap

  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  let result = ref "assert CORRECT"

  (* Forward Iterator *)

  let rec fwdStm funcs env vars config p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env vars
    | A_assign ((l,_),(e,_)) -> B.fwdAssignSingle p (l,e) config
    | A_assert (b,ba) ->
	      let p2' = (B.filterSingle p b config) in
      	  let p2 = B.filterSingle p (fst (negBExp (b,ba))) config in 
		  if ((B.isLeq p p2') && not (B.isBot p)) then (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; result:="assert CORRECT"; p2')
		  else (if (B.isBot p2') then (Format.fprintf !fmt "\nassert (%a) ERROR:\n %a\n" bExp_print_aux b B.print p2; result:="assert ERROR"; p2') 
				else (if (not (B.isBot p2)) then (Format.fprintf !fmt "\nassert (%a) ERROR:\n %a\n" bExp_print_aux b B.print p2; result:="assert ERROR"; p2') 
		  			  else (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; result:="assert CORRECT"; p2') ) )
    | A_if ((b,ba),s1,s2) ->
	  let p1 = B.filterSingle p b config in 
      let p1' = fwdBlk funcs env vars config p1 s1 in
      let p2 = B.filterSingle p (fst (negBExp (b,ba))) config in
      let p2' = fwdBlk funcs env vars config p2 s2 in 
	  (*Format.fprintf !fmt "\n filter(%a,%a) p1 = (%a), p1' = (%a), p2 = (%a), p2' = (%a):\n" B.print p bExp_print_aux b B.print p1 B.print p1' B.print p2 B.print p2';*)
      B.join p1' p2'
    | A_ifdef ((b,ba),s1,s2) -> p  
    | A_while (l,(b,ba),s) ->
      let rec aux i p2 n =
        let i' = B.join p p2 in
        if !tracefwd && not !minimal then begin
          Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
          Format.fprintf !fmt "p1: %a\n" B.print p;
          Format.fprintf !fmt "i: %a\n" B.print i;
          Format.fprintf !fmt "p2: %a\n" B.print p2;
          Format.fprintf !fmt "i': %a\n" B.print i'
        end;
        if B.isLeq i' i then i else
          let i'' = if n <= !joinfwd then i' else 
              B.widen i (B.join i i') in
          if !tracefwd && not !minimal then
            Format.fprintf !fmt "i'': %a\n" B.print i'';
          aux i'' (fwdBlk funcs env vars config (B.filterSingle i'' b config) s) (n+1)
      in
      let i = B.bot env vars in
      let p2 = fwdBlk funcs env vars config (B.filterSingle i b config) s in
      let p = aux i p2 1 in 
	  let p_down = fwdBlk funcs env vars config (B.filterSingle p b config) s in   (* this line is added additionally: performs narrowing  *)
      addFwdInv l p_down; B.filterSingle p_down (fst (negBExp (b,ba))) config 	  	  
      (* addFwdInv l p; B.filterSingle p (fst (negBExp (b,ba))) config *)
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env vars config p s) p ss in
      fwdBlk funcs env vars config p f.funcBody
    | A_recall (f,ss) -> B.top env vars (* TODO *)

  and fwdBlk funcs env vars config (p:B.t) (b:block) : B.t =
    let result_print l p =
      Format.fprintf !fmt "### %a ###: %a\n" label_print l B.print p
    in
    match b with
    | A_empty l ->
      if !tracefwd && not !minimal then result_print l p;
      addFwdInv l p; p
    | A_block (l,(s,_),b) ->
      if !tracefwd && not !minimal then result_print l p;
      addFwdInv l p; 
      fwdBlk funcs env vars config (fwdStm funcs env vars config p s) b


  (* Analyzer *)


(* IMPORTANT FUNCTION THAT DOES THE ANALYSIS*)
  let analyze (vars,stmts,funcs) main config (* determines the current configuration *)=
    let rec aux xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux xs (Environment.add env [|(Var.of_string x.varId)|] [||])
    in
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars = List.append v1 v2 in
    let env = aux vars (Environment.make [||] [||]) in
    let s = f.funcBody in
    (*initBlk env vars stmts; initBlk env vars s; *)
    (* TODO: handle functions calls *)
    (* Forward Analysis *)
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
    let state = fwdBlk funcs env vars config (fwdBlk funcs env vars config (B.top env vars) stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\nForward Analysis:\n";
        fwdMap_print !fmt !fwdInvMap;
      end;
	  !result

end

(***************************************************)
(*                                                 *)
(*    Forward/Backward DT Analysis Iterator        *)
(*            Program Sketcher                     *)
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
open DTDomain
open ItoA

module DTAnalysisIterator (B: DTDomain) =
struct

  module B = B
  module P = B.P

  let fwdInvMap = ref InvMap.empty
  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap
  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  module ExpMap = Map.Make(struct type t=bExp let compare=compare end)

  let assertExpMap = ref ExpMap.empty
  let addAssertInv (b:bExp) ((a1,a2,a3):B.t*B.t*bool) = assertExpMap := ExpMap.add b (a1,a2,a3) !assertExpMap
  let assertMap_print fmt m = ExpMap.iter (fun b (a1,a2,a3) -> 
      (*Format.fprintf fmt "\nAssertion (%a): %a\n" bExp_print_aux b *)
	  B.print_assert fmt a1 a2 a3) m


  (* Forward Iterator *)

  let rec fwdStm funcs env_vars env_feats vars feats p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env_vars env_feats vars feats
    | A_assign ((l,la),(e,ea)) -> let featsIn = (AbstractSyntax.aExp_hasNoFeat e feats true) in 
								if ((List.length featsIn) > 0) then 
									(let pin = ref (B.bot env_vars env_feats vars feats) in
									 let pout = ref (B.bot env_vars env_feats vars feats) in 
									 let cons_list = ref [[]] in 
									 let pin_list = ref [p] in 
									 List.iter (fun (x,y) -> (*Format.fprintf !fmt "Feature %s isLin %b \n" x.varName y; *)
									 				if (y==false) then (
													let cons_temp = ref [] in 
													let pin_temp = ref [] in 
									 				let fm = StringMap.find x.varName !ItoA.features in 
									 				let dom = fm.featDom in 
									 				for i = 0 to (List.length dom)-1 do
														let b1 = 
														if (i==0) then (A_rbinary (A_LESS_EQUAL,(A_var x,(Lexing.dummy_pos,Lexing.dummy_pos)),(A_const (List.nth dom i), (Lexing.dummy_pos,Lexing.dummy_pos))) (*in 
																	    pin := B.config_filter p b1; *)																																
																		(*Format.fprintf !fmt "Exp R %a" aExp_print (e,ea); 
																		Format.fprintf !fmt "Exp L %a" aExp_print (l,la); 
																		Format.fprintf !fmt "\n p = : %a \n" B.print p;
																		Format.fprintf !fmt "\n p2 = : %a \n" B.print p2; *)
																		)
														else if (i==(List.length dom)-1) then (A_rbinary (A_GREATER_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)) (*in 
																	    					   pin := B.config_filter p b1; *)
																		)
															 else (A_bbinary (A_AND, (A_rbinary (A_LESS_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)), ea), (A_rbinary (A_GREATER_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)), ea)) (*in 
																   pin := B.config_filter p b1; *)
																		) in 
														(*pin_temp := !pin_temp@List.map (fun el -> B.config_filter el b1) !pin_list; 	PRESENT*)																	
														pin_temp := !pin_temp@List.map (fun el -> el) !pin_list; 
														let cons = Lincons1.make (Linexpr1.make env_vars) Lincons1.EQ in
  											   			Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string x.varId)) |] (Some (Coeff.s_of_int (-(List.nth dom i))));
														(*cons_temp := !cons_temp@List.map (fun el -> el@[cons]) !cons_list; PRESENT *)
														cons_temp := !cons_temp@[[cons]]; 
														
														(*let p_cons = P.inner env_vars vars [cons] in 
														let p2 = B.add_constraint !pin p_cons in 	
														let p2' = B.fwdAssign p2 (l,e) in 
														let p2'' = B.remove_constraint p2' (Var.of_string x.varId) (Coeff.s_of_int (-(List.nth dom i))) in 
														(*Format.fprintf !fmt "\n assign p2' %a :\n p2'' %a \n" B.print p2' B.print p2''; *)
														pout := B.join p2'' !pout; *)
													done; cons_list := !cons_temp; pin_list := !pin_temp )
													) featsIn; 
													List.iter (fun el -> Format.fprintf !fmt "\n Constraint: %a " P.print (P.inner env_vars vars el); Format.fprintf !fmt "\n" ) !cons_list;
													List.iter (fun el -> Format.fprintf !fmt "\n Pin Trees: %a " B.print el; Format.fprintf !fmt "\n" ) !pin_list; 
													pin_list := List.map2 (fun x y -> B.add_constraint x (P.inner env_vars vars y)) !pin_list !cons_list;
													List.iter (fun el -> let p2' = B.fwdAssign el (l,e) in pout := B.join p2' !pout) !pin_list;
													(*Format.fprintf !fmt "\n assign pout: %a \n" B.print !pout;*) (*B.compress*) !pout)
								 else B.fwdAssign p (l,e)
    | A_assert (b,ba) -> (*B.filter p b*)
		  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
		  let hasFeat = ref false in 
	  	  let p2' = if ((List.length featsIn) > 0) then (hasFeat:=true; B.general_filter p b)
	      			else (B.filter p b) in
		  (*Format.fprintf !fmt "\nassert (%a) \n %a\n" B.print p B.print p2';*)
		  addAssertInv b (p,p2',!hasFeat); p2'
		  (* if (not (B.isBot p2)) then (Format.fprintf !fmt "\nassert (%a) \n %a\n" bExp_print_aux b B.print_assert p2; p2') 
		  else (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; p2') *)	
    | A_if ((b,ba),s1,s2) -> 
	  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  if ((List.length featsIn) > 0) then (
	  	let p1 = B.general_filter p b in Format.fprintf !fmt "\n p1: %a \n" B.print p1;
      	let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in
      	let p2 = B.general_filter p (fst (negBExp (b,ba))) in Format.fprintf !fmt "\n p2: %a \n" B.print p2;
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
      	B.compress (B.join p1' p2')	  
	  )
	  else (
	  	let p1 = B.filter p b in 
      	let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in
      	let p2 = B.filter p (fst (negBExp (b,ba))) in
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
      	B.compress (B.join p1' p2') )
    | A_ifdef ((b,ba),s1,s2) ->	  
	  (*Format.fprintf !fmt "\n config-filter anal %d\n" 1;*)
	  let p1 = B.config_filter p b in 
      let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in 
	  (*let cst = (match b with | A_bvar v -> 0 | _ -> 1) in *)
	  let b_neg = fst (negBExp (b,ba)) in 
      let p2 = B.config_filter p b_neg in (*!AbstractSyntax.cst in AbstractSyntax.cst:=1; *)
      let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
	  let pp = B.compress (B.join p1' p2') in 
	  (*Format.fprintf !fmt "\n ifdef p1=%a p1'=%a\n p2=%a p2'=%a \n" B.print p1 B.print p1' B.print p2 B.print p2';*) (*Format.fprintf !fmt "\n ifdef join %a \n" B.print (B.join p1' p2');
	  Format.fprintf !fmt "\n ifdef compress %a \n" B.print pp; *)
      pp		  
    | A_while (l,(b,ba),s) ->
      let rec aux i p2 n has =
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
		  let b' = if (has) then B.general_filter i'' b else B.filter i'' b in 
          aux i'' (fwdBlk funcs env_vars env_feats vars feats b' s) (n+1) has
      in
	  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  let hasFeat = ref false in 
	  if ((List.length featsIn) > 0) then hasFeat:=true; 
      let i = B.bot env_vars env_feats vars feats in
      let p2 = fwdBlk funcs env_vars env_feats vars feats (B.filter i b) s in 
      let p = aux i p2 1 !hasFeat in 
	  let p_down = fwdBlk funcs env_vars env_feats vars feats (if (!hasFeat) then B.general_filter p b else B.filter p b) s in   (* this line is added additionally: performs narrowing  *)
	  Format.fprintf !fmt "narrow p_down: %a\n" B.print p_down; 
	  (*let pp = if (!hasFeat) then B.general_filter2 p (fst (negBExp (b,ba))) else B.filter p (fst (negBExp (b,ba))) in 
	  Format.fprintf !fmt "pp: %a\n" B.print pp; *)
	  let p_down' = B.merge p_down (if (!hasFeat) then B.general_filter p (fst (negBExp (b,ba))) else B.filter p (fst (negBExp (b,ba)))) in 
	  (*let p_down' = p_down in *)
	  Format.fprintf !fmt "after narrow p_down': %a\n" B.print p_down'; 
	  addFwdInv l p_down'; 
	  let p_end = if (!hasFeat) then B.general_filter p_down' (fst (negBExp (b,ba))) else B.filter p_down' (fst (negBExp (b,ba))) in 
	  Format.fprintf !fmt "p_end: %a\n" B.print p_end;
	  B.compress (p_end)
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env_vars env_feats vars feats p s) p ss in
      fwdBlk funcs env_vars env_feats vars feats p f.funcBody
    | A_recall (f,ss) -> B.top env_vars env_feats vars feats (* TODO *) 
	| _ -> raise (Invalid_argument "\n Unhandled Statement\n")

  and fwdBlk funcs env_vars env_feats vars feats (p:B.t) (b:block) : B.t =
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
      fwdBlk funcs env_vars env_feats vars feats (fwdStm funcs env_vars env_feats vars feats p s) b


  (* Analyzer *)

(* this function generates all configurations *)
let rec process list = 
	if List.length list = 0 then [[]]
	else match list with
		| [] -> []
		| hd :: tl -> 
			let tmp = ref [] in
			let dom = hd.featDom in
			for i = 0 to (List.length dom)-1 do
				let tmp1 = List.map (fun l -> (hd.featName,List.nth dom i) :: l) (process tl) in 
				tmp := !tmp @ tmp1
			done;
			!tmp;;

(* this function generates all implicit constraints \Kk for features taking into account their domains *)
let rec process_cons feats_list env_feats ll = 
		match feats_list with
		| [] -> ll
		| hd :: tl ->
			let tmp = ref [] in
			let typ = hd.featTyp in
			if (typ <> A_BOOL) then (
				let dom = hd.featDom in
				let cons1 = Lincons1.make (Linexpr1.make env_feats) Lincons1.SUPEQ in
  				Lincons1.set_array cons1 [| ((Coeff.s_of_int 1), (Var.of_string hd.featId)) |] (Some (Coeff.s_of_int (-(List.nth dom 0))));
				let cons2 = Lincons1.make (Linexpr1.make env_feats) Lincons1.SUPEQ in
  				Lincons1.set_array cons2 [| ((Coeff.s_of_int (-1)), (Var.of_string hd.featId)) |] (Some (Coeff.s_of_int (List.nth dom ((List.length dom)-1))));				
				tmp := cons1::cons2::!tmp
			); 
			process_cons tl env_feats (!tmp @ ll)


	(*let result = ref [] in 
	List.iter (fun hd -> List.iter (fun vl -> (Format.fprintf !fmt "%s{%d}" hd.featName vl); let tmp = List.map (fun I -> (hd.featName,vl)::I) !result) hd.featDom) lista; 
	!result;;*)
			
let print_configs l =
  print_endline ""; Format.fprintf !fmt "Configurations: ";
  List.iter (fun el -> print_endline ""; List.iter (fun (key,v) -> Format.fprintf !fmt "% s{%d}, " key v) el) l;;  			

(* IMPORTANT FUNCTION THAT DOES THE ANALYSIS*)
  let analyze (vars,stmts,funcs) main =
    let rec aux xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux xs (Environment.add env [|(Var.of_string x.varId)|] [||])
    in
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars1 = List.append v1 v2 in
    (*let env_vars = aux vars (Environment.make [||] [||]) in*)
    let s = f.funcBody in
    (*initBlk env vars stmts; initBlk env vars s; *)
    (* TODO: handle functions calls *)
    (* Forward Analysis *)
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
	let feats = ref [] in
	let feats_feat = ref [] in
	let env_feats = ref (Environment.make [||] [||]) in 
	StringMap.iter (fun key value -> feats_feat := value :: !feats_feat; feats := {varId = value.featId; varName = value.featName; varTyp = value.featTyp} :: !feats; 
									env_feats :=  Environment.add !env_feats [|(Var.of_string value.featId)|] [||]) !ItoA.features; 
	(*let configs = process !feats_feat in print_configs configs; *)
	let vars = List.append vars1 !feats in 
    let env_vars = aux vars (Environment.make [||] [||]) in 	
	let constraints_list = process_cons !feats_feat !env_feats [] in 
	let part_list = P.inner !env_feats !feats constraints_list in (*print_string "GOO"; P.print !fmt part_list;*)
	let leaf_list = P.inner env_vars vars (process_cons !feats_feat env_vars []) in
    let state = fwdBlk funcs env_vars !env_feats vars !feats (fwdBlk funcs env_vars !env_feats vars !feats (B.initial ~domain:part_list leaf_list env_vars !env_feats vars !feats) stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\nForward Analysis:\n";
        fwdMap_print !fmt !fwdInvMap;
      end;
	  if (!assertExpMap != ExpMap.empty) then 
	  	begin
			Format.fprintf !fmt "\nAssertion Analysis:\n"; 
			assertMap_print !fmt !assertExpMap;
		end;
	  true

end

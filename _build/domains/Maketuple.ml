(***************************************************)
(*                                                 *)
(*                 MakeTuple.ml                    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open Partition
open Tuple
open Constraints


(** Creates a tuple abstract domain parameterized by a Partition. *)
module Maketuple(P: PARTITION): TUPLE  = struct

  (** The partition represents a value of one component of a tuple. *)
  module P = P 
  module C = P.C 
  module N = P.N   

  let manager = N.manager (*Box.manager_alloc ()*)
  (** An element of the tuple. *)
  type t = { 
    elems : P.t list; (* representation as list of Partition elements *)
    env : Environment.t; (* APRON environment *)
    vars : var list; (* list of variables in the APRON environment *)	
    configs : (string*int) list list (* list of configurations *)
  }


  (** The current representation as list of Partition components. *)
  let elems u: P.t list = u.elems

  (** The current APRON environment. *)
  let env u = u.env

  (** The current list of variables in the APRON environment. *)
  let vars u = u.vars
  
  (** The current configurations. *)
  let configs u = u.configs
  

  (**)

  let bot e vs c = {
    elems = (let l = ref [] in List.iter (fun key -> l := (P.bot e vs) :: !l ) c; !l);
    env = e;
    vars = vs;	
    configs = c
  }

  let inner e vs c el = {
    elems = el;
    env = e;
    vars = vs; 
	configs = c
  }

  let top e vs c = {
    elems = (let l = ref [] in List.iter (fun key -> l := (P.top e vs) :: !l ) c; !l);
    env = e;
    vars = vs;
	configs = c
  }

  (*  *)
  

  let isBot u =
  	let b = ref true in List.iter (fun elem -> if (not (P.isBot elem)) then b := false ) u.elems; !b


  let isLeq u1 u2 = 
    let b = ref true in List.iter (fun key -> if (not key) then b:=false) (List.map2 (fun e1 e2 -> (P.isLeq e1 e2) ) u1.elems u2.elems); !b

  (**)


  (* let to_apron_t (u:t) : apron_t list = 
    let l = ref [] in List.iter (fun elem -> l := (P.to_apron_t elem) :: !l ) u; !l

  let of_apron_t env vars configs (a:apron_t list) : t = 
    let elems = ref [] in 
		List.iter (fun elem -> elems := (P.of_apron_t elem) :: !elems ) a; 
		{ elems = !elems; env = env; vars = vars; configs = configs }  *)

  let join u1 u2 = 
    let elems = List.map2 (fun e1 e2 -> (P.join e1 e2)) u1.elems u2.elems in 
	let env = u1.env in
    let vars = u1.vars in 
	let configs = u1.configs in 
	{ elems = elems; env = env; vars = vars; configs = configs}	


  let widen u1 u2 = 
    let elems = List.map2 (fun e1 e2 -> (P.widen e1 e2)) u1.elems u2.elems in
	let env = u1.env in
    let vars = u1.vars in 
	let configs = u1.configs in 
	{ elems = elems; env = env; vars = vars; configs = configs}		

  let meet u1 u2 = 
    let elems = List.map2 (fun e1 e2 -> (P.meet e1 e2)) u1.elems u2.elems in
	let env = u1.env in
    let vars = u1.vars in 
	let configs = u1.configs in 
	{ elems = elems; env = env; vars = vars; configs = configs}		

  (*  *)



  let fwdAssign u (x,e) = match x with
    | A_var x ->
      let elems = List.map (fun b -> (P.fwdAssign b (A_var x,e))) u.elems in 
	  let env = u.env in
      let vars = u.vars in 
	  let configs = u.configs in 
	  { elems = elems; env = env; vars = vars; configs = configs}		  
    | _ -> raise (Invalid_argument "fwdAssign: unexpected lvalue")


(*  let bwdAssign_underapprox (u:t) ((x,e): aExp * aExp) : t = match x with
    | A_var x ->
      	if not P.supports_underapproximation then
        	raise (Invalid_argument "Underapproximation not supported by this abstract domain, use polyhedra instead");	
		let elems = List.map (fun b -> P.bwdAssign_underapprox b (A_var x,e)) u.elems in 
		let env = u.env in
        let vars = u.vars in 
		let configs = u.configs in 
		{ elems = elems; env = env; vars = vars; configs = configs}
    | _ -> raise (Invalid_argument "bwdAssign_underapprox: unexpected lvalue")   *)

  let bwdAssign u (x,e) = match x with
    | A_var x ->
      let elems = List.map (fun b -> P.bwdAssign b (A_var x,e)) u.elems in 
	  let env = u.env in
      let vars = u.vars in 
	  let configs = u.configs in 
	  { elems = elems; env = env; vars = vars; configs = configs}		  
    | _ -> raise (Invalid_argument "bwdAssign: unexpected lvalue")


  (* we are here *)
  
(*  let filter_underapprox (u:t) (e:bExp) : t = 
    if not P.supports_underapproximation then
        raise (Invalid_argument "Underapproximation not supported by this abstract domain, use polyhedra instead");  
	let elems = List.map (fun b -> P.filter_underapprox b e) u.elems in 
	let env = u.env in
    let vars = u.vars in 
	let configs = u.configs in 
	{ elems = elems; env = env; vars = vars; configs = configs}  *)


  let rec filter u e =
    let elems = List.map (fun b -> P.filter b e) u.elems in 
	let env = u.env in
    let vars = u.vars in 
	let configs = u.configs in 
	{ elems = elems; env = env; vars = vars; configs = configs}	

	let rec mem x = function 
		| [] -> false
		| hd :: tl -> if (hd = x) then true else (mem x tl)
	
  let rec config_filter env_feat u e =
    match e with
    | A_TRUE -> u
    | A_MAYBE -> u
    | A_FALSE -> bot u.env u.vars u.configs
	| A_bvar v -> 
		let elems = List.map2 (fun el1 el2 -> if (el1) then el2 else (P.bot u.env u.vars)) (List.map (fun el -> mem (v.varName,1) el) u.configs) u.elems in 
		let env = u.env in
    	let vars = u.vars in 
		let configs = u.configs in 
		{ elems = elems; env = env; vars = vars; configs = configs}
    | A_bunary (o,e) ->
      (match o with
       | A_NOT -> let (e,_) = e in let b = config_filter env_feat u e in {elems = List.map2 (fun el1 el2 -> if (P.isBot el1) then el2 else (P.bot u.env u.vars)) b.elems u.elems; env = u.env; vars = u.vars; configs = u.configs})
    | A_bbinary (o,(e1,_),(e2,_)) ->
      let b1 = config_filter env_feat u e1 and b2 = config_filter env_feat u e2 in
      (match o with
       | A_AND -> meet b1 b2
       | A_OR -> join b1 b2)
    | A_rbinary (o,(e1,e1a),(e2,e2a)) ->  (*WORK OUT THIS CASE*)
      (match o with
     	| A_LESS -> let ems = ref [] in 
					let e = Texpr1.of_expr env_feat (aExp_to_apron (A_abinary (A_MINUS,(e2,e2a),(e1,e1a)))) in
         			let c = Tcons1.make e Tcons1.SUP in
         			let a = Tcons1.array_make env_feat 1 in
         			Tcons1.array_set a 0 c; (*Tcons1.print Format.std_formatter c;*)
					for k = (List.length u.configs)-1 downto 0 do
						let config_elem = List.nth u.configs k in
      					let aa = Lincons1.array_make env_feat (List.length config_elem) in
      					let i = ref 0 in
      					List.iter (fun c -> let feat1 = StringMap.find (fst c) !ItoA.features in let val1 = - (snd c) in
											let cons = Lincons1.make (Linexpr1.make env_feat) Lincons1.EQ in
  											Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string feat1.featId)) |] (Some (Coeff.s_of_int val1)); 
											(*Lincons1.print Format.std_formatter cons;*) Lincons1.array_set aa !i cons; i := !i + 1) config_elem;
      					let b = Abstract1.of_lincons_array manager env_feat aa in 				
						let b = Abstract1.meet_tcons_array manager b a in
						if (Abstract1.is_bottom manager b) then ((*Format.fprintf Format.std_formatter " IS bottom";*) ems:=(P.bot u.env u.vars)::!ems)
															else ((*Format.fprintf Format.std_formatter " NOT bottom ";*) ems:=(List.nth u.elems k)::!ems)
					done; {elems = !ems; env = u.env; vars = u.vars; configs = u.configs}
	 	| A_LESS_EQUAL -> let ems = ref [] in 
					let e = Texpr1.of_expr env_feat (aExp_to_apron (A_abinary (A_MINUS,(e2,e2a),(e1,e1a)))) in
         			let c = Tcons1.make e Tcons1.SUPEQ in
         			let a = Tcons1.array_make env_feat 1 in
         			Tcons1.array_set a 0 c; (*Tcons1.array_print Format.std_formatter a;*)
					for k = (List.length u.configs)-1 downto 0 do
						let config_elem = List.nth u.configs k in
      					let aa = Lincons1.array_make env_feat (List.length config_elem) in
      					let i = ref 0 in
      					List.iter (fun c -> let feat1 = StringMap.find (fst c) !ItoA.features in let val1 = - (snd c) in
											let cons = Lincons1.make (Linexpr1.make env_feat) Lincons1.EQ in
  											Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string feat1.featId)) |] (Some (Coeff.s_of_int val1)); 
											(*Lincons1.print Format.std_formatter cons;*) Lincons1.array_set aa !i cons; i := !i + 1) config_elem;
      					let b = Abstract1.of_lincons_array manager env_feat aa in 				
						let b = Abstract1.meet_tcons_array manager b a in
						if (Abstract1.is_bottom manager b) then ((*Format.fprintf Format.std_formatter " IS bottom";*) ems:=(P.bot u.env u.vars)::!ems)
															else ((*Format.fprintf Format.std_formatter " NOT bottom ";*) ems:=(List.nth u.elems k)::!ems)
					done; {elems = !ems; env = u.env; vars = u.vars; configs = u.configs}
	 	| A_GREATER -> let ems = ref [] in 
					let e = Texpr1.of_expr env_feat (aExp_to_apron (A_abinary (A_MINUS,(e1,e1a),(e2,e2a)))) in
         			let c = Tcons1.make e Tcons1.SUP in
         			let a = Tcons1.array_make env_feat 1 in
         			Tcons1.array_set a 0 c; (*Tcons1.array_print Format.std_formatter a;*)
					for k = (List.length u.configs)-1 downto 0 do
						let config_elem = List.nth u.configs k in
      					let aa = Lincons1.array_make env_feat (List.length config_elem) in
      					let i = ref 0 in
      					List.iter (fun c -> let feat1 = StringMap.find (fst c) !ItoA.features in let val1 = - (snd c) in
											let cons = Lincons1.make (Linexpr1.make env_feat) Lincons1.EQ in
  											Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string feat1.featId)) |] (Some (Coeff.s_of_int val1)); 
											(*Lincons1.print Format.std_formatter cons;*) Lincons1.array_set aa !i cons; i := !i + 1) config_elem;
      					let b = Abstract1.of_lincons_array manager env_feat aa in 				
						let b = Abstract1.meet_tcons_array manager b a in
						if (Abstract1.is_bottom manager b) then ((*Format.fprintf Format.std_formatter " IS bottom";*) ems:=(P.bot u.env u.vars)::!ems)
															else ((*Format.fprintf Format.std_formatter " NOT bottom ";*) ems:=(List.nth u.elems k)::!ems)
					done; {elems = !ems; env = u.env; vars = u.vars; configs = u.configs}
	 	| A_GREATER_EQUAL -> let ems = ref [] in 
					let e = Texpr1.of_expr env_feat (aExp_to_apron (A_abinary (A_MINUS,(e1,e1a),(e2,e2a)))) in
         			let c = Tcons1.make e Tcons1.SUPEQ in
         			let a = Tcons1.array_make env_feat 1 in
         			Tcons1.array_set a 0 c; (*Tcons1.array_print Format.std_formatter a;*)
					for k = (List.length u.configs)-1 downto 0 do
						let config_elem = List.nth u.configs k in
      					let aa = Lincons1.array_make env_feat (List.length config_elem) in
      					let i = ref 0 in
      					List.iter (fun c -> let feat1 = StringMap.find (fst c) !ItoA.features in let val1 = - (snd c) in
											let cons = Lincons1.make (Linexpr1.make env_feat) Lincons1.EQ in
  											Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string feat1.featId)) |] (Some (Coeff.s_of_int val1)); 
											(*Lincons1.print Format.std_formatter cons;*) Lincons1.array_set aa !i cons; i := !i + 1) config_elem;
      					let b = Abstract1.of_lincons_array manager env_feat aa in 				
						let b = Abstract1.meet_tcons_array manager b a in
						if (Abstract1.is_bottom manager b) then ((*Format.fprintf Format.std_formatter " IS bottom";*) ems:=(P.bot u.env u.vars)::!ems)
															else ((*Format.fprintf Format.std_formatter " NOT bottom ";*) ems:=(List.nth u.elems k)::!ems)
					done; {elems = !ems; env = u.env; vars = u.vars; configs = u.configs}	)
	
  let rec config_filter_not env_feat u u' =	
		{elems = List.map2 (fun el1 el2 -> if (P.isBot el1) then el2 else (P.bot u.env u.vars)) u'.elems u.elems; env = u.env; vars = u.vars; configs = u.configs}
(**)

  let print fmt u =
    Format.fprintf fmt "{ ";
	List.iter (fun el -> P.print fmt el; Format.fprintf fmt "; ") u.elems;
	Format.fprintf fmt " }"

  let print_assert fmt u =
    Format.fprintf fmt "{ ";
	List.iter2 (fun el cf -> (if (P.isBot el) then (Format.fprintf fmt "CORRECT; config = "; List.iter (fun (key,v) -> Format.fprintf fmt "% s{%d}, " key v) cf) else (Format.fprintf fmt "ERROR: "; P.print fmt el; Format.fprintf fmt "; "))) u.elems u.configs;
	Format.fprintf fmt " }"

end

(** Single Tuple domain parameterized by the boxes numerical abstract domain. *)
 module TB = Maketuple(Numerical.B)

(** Single Tuple domain parameterized by the octagons abstract domain. *)
module TO = Maketuple(Numerical.O)

(** Single Tuple domain parameterized by the polyhedra abstract domain. *)
module TP = Maketuple(Numerical.P)

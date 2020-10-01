(***************************************************)
(*                                                 *)
(*               Domain Partition                  *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open Constraints

module type NUMERICAL = sig 
  type lib
  val manager: lib Manager.t 
  val supports_underapproximation: bool
end


(** Signature for a single partition of the domain of a ranking function. *)
module type PARTITION = sig
  module C : CONSTRAINT
  module N : NUMERICAL

  type t
  val constraints : t -> C.t list
  val env : t -> Environment.t
  val vars : t -> var list

  val bot : Environment.t -> var list -> t
  val inner : Environment.t -> var list -> C.t list -> t
  val top : Environment.t -> var list -> t
  
  val supports_underapproximation: bool 
  val isBot : t -> bool
  val isTop : t -> bool  
  val isLeq : t -> t -> bool

  val join : t -> t -> t
  val widen : t -> t -> t
  val meet : t -> t -> t

  val fwdAssign : t -> aExp * aExp -> t
  val fwdAssignSingle : t -> aExp * aExp -> (string*int) list -> t  
  val fwdAssign_project : t -> aExp * aExp -> Environment.t -> var list -> t
  val bwdAssign : t -> aExp * aExp -> t
(*  val bwdAssign_underapprox : t -> aExp * aExp -> t *)
  val filter : t -> bExp -> t
  val filterSingle : t -> bExp -> (string*int) list -> t
(*  val filter_underapprox : t -> bExp -> t  *)
  val project : t -> Environment.t -> var list -> t
  val remove_cons : t -> Apron.Var.t -> Apron.Coeff.t -> t

  val print : Format.formatter -> t -> unit

end

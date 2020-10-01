(***************************************************)
(*                                                 *)
(*                   Tuple.ml                      *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open Partition
open Constraints
open Numerical 

(** Signature for a single partition of the domain of a ranking function. *)
module type TUPLE = sig
  module P : PARTITION

  type t
  val elems : t -> P.t list
  val env : t -> Environment.t
  val vars : t -> var list  
  val configs : t -> (string * int) list list

  val bot :  Environment.t -> var list -> (string * int) list list -> t
  val inner : Environment.t -> var list -> (string * int) list list -> P.t list -> t
  val top : Environment.t -> var list -> (string * int) list list -> t

  val isBot : t -> bool
  val isLeq : t -> t -> bool

  val join : t -> t -> t
  val widen : t -> t -> t
  val meet : t -> t -> t

  val fwdAssign : t -> aExp * aExp -> t
  val bwdAssign : t -> aExp * aExp -> t
(*  val bwdAssign_underapprox : t -> aExp * aExp -> t  *)
  val filter : t -> bExp -> t
  val config_filter : Environment.t -> t -> bExp -> t  
  val config_filter_not : Environment.t -> t -> t -> t   
(*  val filter_underapprox : t -> bExp -> t  *)


  val print : Format.formatter -> t -> unit
  val print_assert : Format.formatter -> t -> unit

end

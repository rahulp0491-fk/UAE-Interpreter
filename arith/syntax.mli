(* module Syntax: syntax trees and associated support functions *)

open Support.Pervasive
open Support.Error

(* Data type definitions *)
type term =
    TmTrue of info
  | TmFalse of info
  | TmIf of info * term * term * term
  | TmZero of info
  | TmSucc of info * term
  | TmPred of info * term
  | TmIsZero of info * term
  | TmNot of info * term                    (* --------------NODE FOR NOT--------------- *)
  | TmIncr of info * term                   (* --------------NODE FOR INCR-------------- *)
  | TmAnd of info * term * term             (* --------------NODE FOR AND--------------- *)
  | TmSwitch of info * term * term * term   (* --------------NODE FOR SWITCH------------ *)

type command =
  | Eval of info * term



(* Printing *)
val printtm: term -> unit
val printtm_ATerm: bool -> term -> unit

(* Misc *)
val tmInfo: term -> info


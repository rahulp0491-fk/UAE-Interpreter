open Format
open Syntax
open Support.Error
open Support.Pervasive

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval t1
  | TmPred(_,t1) -> isnumericval t1
  | _ -> false

let rec isval t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | t when isnumericval t  -> true
  | _ -> false

let rec eval1 t = match t with
(*-----------REMOVED E-IFTRUE AND E-IFFALSE-----------------------------------------------------)
    TmIf(_,TmTrue(_),t2,t3) ->
      t2
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3
*)
(* -------------NEW OPTIONS TO EVALUATE THE TERMS BEFORE THE GUARD IN TmIf------------------ *)
    TmIf(_,TmTrue(_),v1,v2) when (isval v1=true||isval v1=false)&&(isval v2=true||isval v2=false) ->
      v1
  | TmIf(_,TmFalse(_),v1,v2) when (isval v1=true||isval v1=false)&&(isval v2=true||isval v2=false) ->
      v2
  | TmIf(fi,t1,v1,v2) when (isval v1=true||isval v1=false)&&(isval v2=true||isval v2=false) ->
      let t1' = eval1 t1 in 
      TmIf(fi,t1',v1,v2)
  | TmIf(fi,t1,t2,t3) ->
      let t2' = eval1 t2 and t3' = eval1 t3 in
      TmIf(fi, t1, t2', t3')
(* ----------------------------------------------------------------------------------------- *)

(* -----------------------------EVALUATION FOR NOT--------------------------------- *)
  | TmNot(_, TmTrue(_)) ->
      TmFalse(dummyinfo)
  | TmNot(_, TmFalse(_)) ->
      TmTrue(dummyinfo)
  | TmNot(fi, t1) ->
      let t1' = eval1 t1 in
      TmNot(fi, t1')
(* ------------------------------------------------------------------------------- *)

  | TmSucc(fi,t1) ->
      let t1' = eval1 t1 in
      TmSucc(fi, t1')
(* -----------------------------REMOVED E-PREDZERO---------------------------------- )
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
*)

  | TmPred(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 t1 in
      TmIsZero(fi, t1')
  | _ -> 
      raise NoRuleApplies

let rec eval t =
  try let t' = eval1 t
      in eval t'
  with NoRuleApplies -> t

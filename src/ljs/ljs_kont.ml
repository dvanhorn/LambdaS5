open Prelude
open Store
open Ljs_values
module S = Ljs_syntax

type id = string

(* when I write "we'll have n cases for this...", it means we'll match the
   expressions to see if they're values, if they are we just move on to the
   next (immediately right) exp, if there are no more exps, we move on. *)

type kont =
  | SetBang of loc * kont
(*  | Object of S.exp list * S.exp list * (string * S.exp) list * (string * S.exp) list * kont *)
  | GetAttr of S.pattr * value option * S.exp option * kont
  | SetAttr of S.pattr * value option * S.exp option * value option * S.exp option * kont
  | GetObjAttr of S.oattr * kont
  | SetObjAttr of S.oattr * value option * S.exp option * kont
  (* obj_value option * Field * field_value option * args * args_value option *)
  | GetField of Pos.t * value option * S.exp option * value option * S.exp option * kont
  | SetField of Pos.t * value option * S.exp option * value option * S.exp option * value option * S.exp option * kont
  | OwnFieldNames of kont
  | DeleteField of Pos.t * value option * S.exp option * kont
  | Mt
  | If of env * S.exp * S.exp * kont
  | App of Pos.t * value option * env * value list * S.exp list * kont
  | Seq of S.exp * kont
  | Let of id * S.exp * kont
  | Rec of loc * S.exp * kont
  | Break of id * kont
  | TryCatch of Pos.t * S.exp * env * value * kont
  | TryFinally of S.exp option * env * exn option * kont
  | Throw
  | Eval of Pos.t * value option * S.exp option * store * kont
  | Hint

open Prelude
open Store
open Ljs_values
module S = Ljs_syntax

type id = string

type kont =
(* exp type continuations *)
  | SetBang of loc * kont
  (* primval * codexp opt * codeval opt * protoexp opt * protoval opt *  *)
2  | GetAttr of S.pattr * value option * S.exp option * kont
2  | SetAttr of S.pattr * value option * S.exp option * value option * S.exp option * kont
  | GetObjAttr of S.oattr * kont
2  | SetObjAttr of S.oattr * value option * S.exp option * kont
3  | GetField of Pos.t * value option * S.exp option * value option * S.exp option * env * bool * kont
4  | SetField of Pos.t * value option * S.exp option * value option * S.exp option * value option * S.exp option * env * bool * kont
  | OwnFieldNames of kont
2  | DeleteField of Pos.t * value option * S.exp option * kont
  | Op1 of string * kont
2  | Op2 of string * value option * S.exp option * kont
  | Mt
  | If of env * S.exp * S.exp * kont
  | App of Pos.t * value option * env * value list * S.exp list * bool * kont
  | Seq of S.exp * kont
  | Let of id * S.exp * kont
  | Rec of loc * S.exp * kont
  | Break of id * kont
  | Label of id * env * kont
  | TryCatch of Pos.t * S.exp option * env * value option * kont
  | TryFinally of S.exp option * env * exn option * kont
  | Throw of kont
2  | Eval of Pos.t * value option * S.exp option * store * kont
  | Hint of kont
  | Object of attrsv option * (string * S.prop) list * (string * propv) list * kont
(* attr continuation *)
  | Attrs of string * (string * S.exp) list * (string * value) list * string * bool * kont
(* property continuation *)
  | DataProp of string * bool * bool * bool * kont
  | AccProp of string * value option * S.exp option * bool * bool * kont

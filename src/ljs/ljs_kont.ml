open Prelude
open Store
open Ljs_values

module S = Ljs_syntax

type id = string

type kont =
  | Mt
  | SetBang of loc * kont
  | GetAttr  of S.pattr * S.exp * kont
  | GetAttr2 of S.pattr * value * kont
  | SetAttr  of S.pattr * S.exp * S.exp * kont
  | SetAttr2 of S.pattr * S.exp * value * kont
  | SetAttr3 of S.pattr * value * value * kont
  | GetObjAttr of S.oattr * kont
  | SetObjAttr  of S.oattr * S.exp * kont
  | SetObjAttr2 of S.oattr * value * kont
  | GetField  of Pos.t * S.exp * S.exp * env * kont
  | GetField2 of Pos.t * S.exp * value * env * kont
  | GetField3 of Pos.t * value * value * env * kont
  | GetField4 of env * kont
  | SetField  of Pos.t * S.exp * S.exp * S.exp * env * kont
  | SetField2 of Pos.t * S.exp * S.exp * value * env * kont
  | SetField3 of Pos.t * S.exp * value * value * env * kont
  | SetField4 of Pos.t * value * value * value * env * kont
  | SetField5 of env * kont
  | OwnFieldNames of kont
  | DeleteField  of Pos.t * S.exp * kont
  | DeleteField2 of Pos.t * value * kont
  | OpOne of string * kont
  | OpTwo  of string * S.exp * kont
  | OpTwo2 of string * value * kont
  | If of env * S.exp * S.exp * kont
  | App  of Pos.t * env * S.exp list * kont
  | App2 of Pos.t * value * env * value list * S.exp list * kont
  | App3 of env * kont
  | Seq of S.exp * kont
  | Let of id * S.exp * kont
  | Rec of loc * S.exp * kont
  | Label of id * env * kont
  | Break of id * kont
  | TryCatch  of Pos.t * S.exp * env * kont
  | TryCatch2 of Pos.t * value * env * kont
  | TryCatch3 of env * kont
  | TryFinally  of S.exp * env * kont
  | TryFinally2 of exn * env * kont
  | Throw of kont
  | Eval  of Pos.t * S.exp * store * kont
  | Eval2 of Pos.t * value * store * kont
  | Eval3 of store * kont
  | Hint of kont
  | Object  of (string * S.prop) list * kont
  | Object2 of attrsv * (string * S.prop) list *
      (string * propv) list * kont
  | Attrs of string * (string * S.exp) list * (string * value) list *
      string * bool * kont
  | DataProp of string * bool * bool * bool * kont
  | AccProp  of string * S.exp * bool * bool * kont
  | AccProp2 of string * value * bool * bool * kont

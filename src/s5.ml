open List
open Prelude
open Ljs
open Ljs_eval
open Ljs_cesk
open Ljs_syntax
open Ljs_pretty_html
open Reachability

type node =
  | Js of Js_syntax.program
  | Ejs of IdSet.t * Exprjs_syntax.expr
  | Ljs of Ljs_syntax.exp
  | Cps of Ljs_cps.cps_exp
  | Env of (Ljs_syntax.exp -> Ljs_syntax.exp)
  | Answer of answer

type nodeType = JsT | EjsT | LjsT | CpsT | EnvT | AnswerT

let nodeType (node : node) : nodeType =
  match node with
  | Js _ -> JsT
  | Ejs _ -> EjsT
  | Ljs _ -> LjsT
  | Cps _ -> CpsT
  | Env _ -> EnvT
  | Answer _ -> AnswerT


let showNodeType (nodeType : nodeType) : string =
  match nodeType with
  | JsT -> "JS"
  | EjsT -> "ExprJS"
  | LjsT -> "S5"
  | CpsT -> "S5-cps"
  | EnvT -> "S5-env"
  | AnswerT -> "Snapshot"


module S5 = struct

  open Format
  open Js_to_exprjs
  open Exprjs_to_ljs
  open Exprjs_syntax
  open Js_syntax
  open Ljs_desugar
  open Ljs_pretty_value
  open Format
  open FormatExt
  open Ljs_gc

  module LocSet = Store.LocSet
  module LocMap = Store.LocMap

  let json_path = ref "../tests/desugar.sh"
  let p = Pos.dummy

  let fact =
    (S.Rec (p, "fact",
            S.Lambda (p, ["n"],
                      (S.If (p, (S.Op2 (p, "sameValue", S.Id (p, "n"), S.Num (p, 0.))),
                             (S.Num (p, 1.)),
                             (S.Op2 (p, "*", S.Id (p, "n"),
                                     (S.App (p, S.Id (p, "fact"), [(S.Op2 (p, "-", S.Id (p, "n"), S.Num (p, 1.)))]))))))),
            S.App (p, S.Id (p, "fact"), [(S.Num (p, 4.))])))

  let main () : unit =
    let value, store = eval_cesk (desugar !json_path) (ExpClosure (fact, IdMap.empty)) (Store.empty, Store.empty) K.Mt in
    print_string ("Result: "^(string_of_value value store)) ;

end;;
S5.main ()

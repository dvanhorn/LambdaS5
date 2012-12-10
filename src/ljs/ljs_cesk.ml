open Ljs_delta
open Ljs_gc
open Ljs_pretty
open Ljs_pretty_value
open Ljs_values
open Prelude

module S = Ljs_syntax
module K = Ljs_kont
module L = Ljs_eval
module LocSet = Store.LocSet
module LocMap = Store.LocMap

(* from ljs_eval, let's move these to a util file eventuallly *)
let interp_error pos message =
  raise (PrimErr ([], String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))

let rec get_attr store attr obj field = match obj, field with
  | ObjLoc loc, String s ->
    let (attrs, props) = get_obj store loc in
    if (not (IdMap.mem s props)) then
      undef
    else
      begin match (IdMap.find s props), attr with
      | Data (_, _, config), S.Config
      | Accessor (_, _, config), S.Config -> bool config
      | Data (_, enum, _), S.Enum
      | Accessor (_, enum, _), S.Enum -> bool enum
      | Data ({ writable = b; }, _, _), S.Writable -> bool b
      | Data ({ value = v; }, _, _), S.Value -> v
      | Accessor ({ getter = gv; }, _, _), S.Getter -> gv
      | Accessor ({ setter = sv; }, _, _), S.Setter -> sv
      | _ -> interp_error Pos.dummy "bad access of attribute"
      end
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

let unbool b = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (pretty_value b))

let rec set_attr (store : store) attr obj field newval = match obj, field with
  | ObjLoc loc, String f_str -> begin match get_obj store loc with
    | ({ extensible = ext; } as attrsv, props) ->
      if not (IdMap.mem f_str props) then
        if ext then
          let newprop = match attr with
            | S.Getter ->
              Accessor ({ getter = newval; setter = Undefined; },
                        false, false)
            | S.Setter ->
              Accessor ({ getter = Undefined; setter = newval; },
                        false, false)
            | S.Value ->
              Data ({ value = newval; writable = false; }, false, false)
            | S.Writable ->
              Data ({ value = Undefined; writable = unbool newval },
                    false, false)
            | S.Enum ->
              Data ({ value = Undefined; writable = false },
                    unbool newval, true)
            | S.Config ->
              Data ({ value = Undefined; writable = false },
                    true, unbool newval) in
          let store = set_obj store loc
            (attrsv, IdMap.add f_str newprop props) in
          true, store
        else
          failwith "[interp] Extending inextensible object ."
      else
        (* 8.12.9: "If a field is absent, then its value is considered
           to be false" -- we ensure that fields are present and
           (and false, if they would have been absent). *)
        let newprop = match (IdMap.find f_str props), attr, newval with
          (* S.Writable true -> false when configurable is false *)
          | Data ({ writable = true } as d, enum, config), S.Writable, new_w ->
            Data ({ d with writable = unbool new_w }, enum, config)
          | Data (d, enum, true), S.Writable, new_w ->
            Data ({ d with writable = unbool new_w }, enum, true)
          (* Updating values only checks writable *)
          | Data ({ writable = true } as d, enum, config), S.Value, v ->
            Data ({ d with value = v }, enum, config)
          (* If we had a data property, update it to an accessor *)
          | Data (d, enum, true), S.Setter, setterv ->
            Accessor ({ getter = Undefined; setter = setterv }, enum, true)
          | Data (d, enum, true), S.Getter, getterv ->
            Accessor ({ getter = getterv; setter = Undefined }, enum, true)
          (* Accessors can update their getter and setter properties *)
          | Accessor (a, enum, true), S.Getter, getterv ->
            Accessor ({ a with getter = getterv }, enum, true)
          | Accessor (a, enum, true), S.Setter, setterv ->
            Accessor ({ a with setter = setterv }, enum, true)
          (* An accessor can be changed into a data property *)
          | Accessor (a, enum, true), S.Value, v ->
            Data ({ value = v; writable = false; }, enum, true)
          | Accessor (a, enum, true), S.Writable, w ->
            Data ({ value = Undefined; writable = unbool w; }, enum, true)
          (* enumerable and configurable need configurable=true *)
          | Data (d, _, true), S.Enum, new_enum ->
            Data (d, unbool new_enum, true)
          | Data (d, enum, true), S.Config, new_config ->
            Data (d, enum, unbool new_config)
          | Data (d, enum, false), S.Config, False ->
            Data (d, enum, false)
          | Accessor (a, enum, true), S.Config, new_config ->
            Accessor (a, enum, unbool new_config)
          | Accessor (a, enum, true), S.Enum, new_enum ->
            Accessor (a, unbool new_enum, true)
          | Accessor (a, enum, false), S.Config, False ->
            Accessor (a, enum, false)
          | _ -> raise (PrimErr ([], String ("[interp] bad property set "
                                             ^ (pretty_value obj) ^ " " ^ f_str ^ " " ^
                                               (S.string_of_attr attr) ^ " " ^ (pretty_value newval))))
        in begin
          let store = set_obj store loc
            (attrsv, IdMap.add f_str newprop props) in
          true, store
        end
  end
  | _ -> failwith ("[interp] set-attr didn't get an object and a string")

let get_obj_attr attrs attr = match attrs, attr with
  | { proto=proto }, S.Proto -> proto
  | { extensible=extensible} , S.Extensible -> bool extensible
  | { code=Some code}, S.Code -> code
  | { code=None}, S.Code -> Null
  | { primval=Some primval}, S.Primval -> primval
  | { primval=None}, S.Primval ->
    failwith "[interp] Got Primval attr of None"
  | { klass=klass }, S.Klass -> String klass

let rec get_prop p store obj field =
  match obj with
  | Null -> None
  | ObjLoc loc -> begin match get_obj store loc with
    | { proto = pvalue; }, props ->
      try Some (IdMap.find field props)
      with Not_found -> get_prop p store pvalue field
  end
  | _ -> failwith (interp_error p
                     "get_prop on a non-object.  The expression was (get-prop "
                   ^ (*pretty_value obj*) "obj"
                   ^ " " ^ field ^ ")")

let envstore_of_obj p (_, props) store =
  IdMap.fold (fun id prop (env, store) -> match prop with
  | Data ({value=v}, _, _) ->
    let new_loc, store = add_var store v in
    let env = IdMap.add id new_loc env in
    env, store
  | _ -> interp_error p "Non-data value in env_of_obj")
    props (IdMap.empty, store)

let arity_mismatch_err p xs args = interp_error p ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ ". Arg names were: " ^ (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (map (fun v -> " " ^ pretty_value v ^ " ") args) ""))

let err show_stack trace message =
  if show_stack then begin
    eprintf "%s\n" (string_stack_trace trace);
    eprintf "%s\n" message;
    failwith "Runtime error"
  end
  else
    eprintf "%s\n" message;
  failwith "Runtime error"

(* modified from ljs_eval to add the arguments to the environment and store,
   then a triple of the body of the function, the updated env, and the
   updated store. *)
let rec apply p store func args = match func with
  | Closure (env, xs, body) ->
    let alloc_arg argval argname (store, env) =
      let (new_loc, store) = add_var store argval in
      let env' = IdMap.add argname new_loc env in
      (store, env') in
    if (List.length args) != (List.length xs) then
      arity_mismatch_err p xs args
    else
      let (store, env) = (List.fold_right2 alloc_arg args xs (store, env)) in
      (body, env, store)
  | ObjLoc loc -> begin match get_obj store loc with
    | ({ code = Some f }, _) -> apply p store f args
    | _ -> failwith "Applied an object without a code attribute"
  end
  | _ -> failwith (interp_error p
                     ("Applied non-function, was actually " ^
                         pretty_value func))

(* end borrowed ljs_eval helpers *)

(* Machine-specific closures *)
type closure =
| ExpClosure of S.exp * env
| ValClosure of value * env
| AEClosure of S.attrs * env
| AVClosure of attrsv * env
| PEClosure of (string * S.prop) * env
| PVClosure of (string * propv) * env
| LobClosure of exn

(* accessors and helpers *)
let exp_of clos = match clos with
  | ExpClosure (expr, _) -> Some expr
  | _ -> None
let env_of clos = match clos with
  | ExpClosure (_, env) -> Some env
  | _ -> None
let env_of_any clos = match clos with
  | ExpClosure (_, env) -> env
  | ValClosure (_, env) -> env
  | AEClosure  (_, env) -> env
  | AVClosure  (_, env) -> env
  | PEClosure  (_, env) -> env
  | PVClosure  (_, env) -> env
  | LobClosure  _ -> IdMap.empty
let add_opt clos xs f = match f clos with
  | Some x -> x::xs
  | None -> xs

(* for printing *)
let rec string_of_expr expr = match expr with
  | S.Null _ -> "null"
  | S.Undefined _ -> "undef"
  | S.String (_, s) -> "\""^s^"\""
  | S.Num (_, f) -> string_of_float f
  | S.True _ -> "true"
  | S.False _ -> "false"
  | S.Id (_, name) -> "id(\""^name^"\")"
  | S.Object (_, _, _) -> "objlit"
  | S.GetAttr (_, _, obj, field) -> "getattr(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^")"
  | S.SetAttr (_,_,obj, field, newv) -> "setattr(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^", "^(string_of_expr newv)^")"
  | S.GetObjAttr (_,_,obj) -> "getobjattr(_,_, "^(string_of_expr obj)^")"
  | S.SetObjAttr (_,_,_,obj) -> "setobjattr(_,_,_, "^(string_of_expr obj)^")"
  | S.GetField (_,_,obj,field) -> "getfield(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^")"
  | S.SetField (_,_,obj,field,newv) -> "setfield(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^", "^(string_of_expr newv)^")"
  | S.DeleteField (_,obj,field) -> "deletefield(_, "^(string_of_expr obj)^", "^(string_of_expr field)^")"
  | S.OwnFieldNames (_,obj) -> "ownfieldnames(_, "^(string_of_expr obj)^")"
  | S.SetBang (_,name,valu) -> "setbang(_, "^name^", "^(string_of_expr valu)^")"
  | S.Op1 (_,op,arg) -> "op1(_, "^op^", "^(string_of_expr arg)^")"
  | S.Op2 (_,op,arg1,arg2) -> "op2(_, "^op^", "^(string_of_expr arg1)^", "^(string_of_expr arg2)^")"
  | S.If (_,p,t,e) -> "if(_, "^(string_of_expr p)^", "^(string_of_expr t)^", "^(string_of_expr e)^")"
  | S.App (_,_,_) -> "app"
  | S.Seq (_,_,_) -> "seq"
  | S.Let (_,n,b,bod) -> "let(_, "^n^", "^(string_of_expr b)^", "^(string_of_expr bod)^")"
  | S.Rec (_,_,_,_) -> "letrec"
  | S.Label (_,_,_) -> "label"
  | S.Break (_,_,_) -> "break"
  | S.TryCatch (_,_,_) -> "trycatch"
  (** Catch block must be an [ELambda] *)
  | S.TryFinally (_,_,_) -> "tryfinally"
  | S.Throw (_,_) -> "throw"
  | S.Lambda (_,_,_) -> "lambda"
  | S.Eval (_,_,_) -> "eval"
  | S.Hint (_,_,_) -> "hint"
let string_of_clos clos store = match clos with
  | ExpClosure (e, env) -> "Exp("^(string_of_expr e)^", "^(string_of_env env)^")"
  | ValClosure (v, env) ->  "Val("^(string_of_value v store)^", "^(string_of_env env)^")"
  | AEClosure  (_, _) ->  "ae"
  | AVClosure  (_, _) ->  "av"
  | PEClosure  (_, _) ->  "pe"
  | PVClosure  (_, _) ->  "pv"
  | LobClosure _ -> "lob"
let string_of_kont k = match k with
  | K.SetBang (_, _) -> "k.setbang"
  | K.GetAttr (_, _, _) -> "k.getattr"
  | K.GetAttr2 (_, _, _) -> "k.getattr2"
  | K.SetAttr (_, _, _, _) -> "k.setattr"
  | K.SetAttr2 (_, _, _, _) -> "k.setattr2"
  | K.SetAttr3 (_, _, _, _) -> "k.setattr3"
  | K.GetObjAttr (_, _) -> "k.getobjattr"
  | K.SetObjAttr (_, _, _) -> "k.setobjattr"
  | K.SetObjAttr2 (_, _, _) -> "k.setobjattr2"
  | K.GetField (_, _, _, _, _) -> "k.getfield"
  | K.GetField2 (_, _, _, _, _) -> "k.getfield2"
  | K.GetField3 (_, _, _, _, _) -> "k.getfield3"
  | K.GetField4 (_, _) -> "k.getfield4"
  | K.SetField (_, _, _, _, _, _) -> "k.setfield"
  | K.SetField2 (_, _, _, _, _, _) -> "k.setfield2"
  | K.SetField3 (_, _, _, _, _, _) -> "k.setfield3"
  | K.SetField4 (_, _, _, _, _, _) -> "k.setfield4"
  | K.SetField5 (_, _) -> "k.setfield5"
  | K.OwnFieldNames _ -> "k.ownfieldnames"
  | K.DeleteField (_, _, _) -> "k.deletefield"
  | K.DeleteField2 (_, _, _) -> "k.deletefield2"
  | K.OpOne (_, _) -> "k.opone"
  | K.OpTwo (_, _, _) -> "k.optwo"
  | K.OpTwo2 (_, _, _) -> "k.optwo2"
  | K.Mt -> "k.mt"
  | K.If (_, _, _, _) -> "k.if"
  | K.App (_, _, _, _) -> "k.app"
  | K.App2 (_, _, _, _, _, _) -> "k.app2"
  | K.App3 (_, _) -> "k.app3"
  | K.Seq (_, _) -> "k.seq"
  | K.Let (_, _, _) -> "k.let"
  | K.Rec (_, _, _) -> "k.rec"
  | K.Break (label, _) -> "k.break: "^label
  | K.TryCatch (_, _, _, _) -> "k.trycatch"
  | K.TryCatch2 (_, _, _, _) -> "k.trycatch2"
  | K.TryCatch3 (_, _) -> "k.trycatch3"
  | K.TryFinally (_, _, _) -> "k.tryfinally"
  | K.TryFinally2 (_, _, _) -> "k.tryfinally2"
  | K.Throw _ -> "k.throw"
  | K.Eval (_, _, _, _) -> "k.eval"
  | K.Eval2 (_, _, _, _) -> "k.eval2"
  | K.Eval3 (_, _) -> "k.eval3"
  | K.Hint _ -> "k.hint"
  | K.Object (_, _) -> "k.object"
  | K.Object2 (_, _, _, _) -> "k.object2"
  | K.Attrs (_, _, _, _, _, _) -> "k.attrs"
  | K.DataProp (_, _, _, _, _) -> "k.dataprop"
  | K.AccProp (_, _, _, _, _) -> "k.accprop"
  | K.AccProp2 (_, _, _, _, _) -> "k.accprop2"
  | K.Label (_, _, _) -> "k.label"

(* for control flow *)
let shed k = match k with
  | K.SetBang (_, k) -> k
  | K.GetAttr (_, _, k) -> k
  | K.GetAttr2 (_, _, k) -> k
  | K.SetAttr (_, _, _, k) -> k
  | K.SetAttr2 (_, _, _, k) -> k
  | K.SetAttr3 (_, _, _, k) -> k
  | K.GetObjAttr (_, k) -> k
  | K.SetObjAttr (_, _, k) -> k
  | K.SetObjAttr2 (_, _, k) -> k
  | K.GetField (_, _, _, _, k) -> k
  | K.GetField2 (_, _, _, _, k) -> k
  | K.GetField3 (_, _, _, _, k) -> k
  | K.GetField4 (_, k) -> k
  | K.SetField (_, _, _, _, _, k) -> k
  | K.SetField2 (_, _, _, _, _, k) -> k
  | K.SetField3 (_, _, _, _, _, k) -> k
  | K.SetField4 (_, _, _, _, _, k) -> k
  | K.SetField5 (_, k) -> k
  | K.OwnFieldNames k -> k
  | K.DeleteField (_, _, k) -> k
  | K.DeleteField2 (_, _, k) -> k
  | K.OpOne (_, k) -> k
  | K.OpTwo (_, _, k) -> k
  | K.OpTwo2 (_, _, k) -> k
  | K.Mt -> k
  | K.If (_, _, _, k) -> k
  | K.App (_, _, _, k) -> k
  | K.App2 (_, _, _, _, _, k) -> k
  | K.App3 (_, k) -> k
  | K.Seq (_, k) -> k
  | K.Let (_, _, k) -> k
  | K.Rec (_, _, k) -> k
  | K.Break (_, k) -> k
  | K.TryCatch (_, _, _, k) -> k
  | K.TryCatch2 (_, _, _, k) -> k
  | K.TryCatch3 (_, k) -> k
  | K.TryFinally (_, _, k) -> k
  | K.TryFinally2 (_, _, k) -> k
  | K.Throw k -> k
  | K.Eval (_, _, _, k) -> k
  | K.Eval2 (_, _, _, k) -> k
  | K.Eval3 (_, k) -> k
  | K.Hint k -> k
  | K.Object (_, k) -> k
  | K.Object2 (_, _, _, k) -> k
  | K.Attrs (_, _, _, _, _, k) -> k
  | K.DataProp (_, _, _, _, k) -> k
  | K.AccProp (_, _, _, _, k) -> k
  | K.AccProp2 (_, _, _, _, k) -> k
  | K.Label (_, _, k) -> k

(* for garbage collection *)

let locs_of_closure clos = match clos with
  | ExpClosure (_, e) -> locs_of_env e
  | ValClosure (v, e) -> LocSet.union (locs_of_value v) (locs_of_env e)
  |  AEClosure (_, e) -> locs_of_env e
  |  AVClosure (_, e) -> locs_of_env e
  |  PEClosure (_, e) -> locs_of_env e
  |  PVClosure (_, e) -> locs_of_env e
  | LobClosure _      -> LocSet.empty

let locs_of_values vs a =
  List.fold_left (fun a n -> (locs_of_value n)::a) a vs

let locs_of_opt ox locs_of_x = match ox with
  | Some v -> locs_of_x v
  | None -> LocSet.empty

let locs_of_opt_val ov = locs_of_opt ov locs_of_value

let locs_of_propv pv = match pv with
  | Data ({ value=v }, _, _) -> locs_of_value v
  | Accessor ({ getter=gv; setter=sv }, _, _) -> LocSet.union (locs_of_value gv) (locs_of_value sv)

let locs_of_propvs pvs a = List.fold_left (fun a (_, n) -> (locs_of_propv n)::a) a pvs

let locs_of_attrsv av =
  let { code=ov; proto=v; primval=ov' } = av in
  LocSet.unions [locs_of_opt_val ov; locs_of_value v; locs_of_opt_val ov']

let rec locs_of_kont ko : LocSet.t = match ko with
  | K.SetBang (l, k) -> LocSet.union (LocSet.singleton l) (locs_of_kont k)
  | K.GetAttr (_, _, k) -> locs_of_kont k
  | K.GetAttr2 (_, v, k) -> LocSet.union (locs_of_value v) (locs_of_kont k)
  | K.SetAttr (_, _, _, k) -> locs_of_kont k
  | K.SetAttr2 (_, _, v, k) -> LocSet.union (locs_of_value v) (locs_of_kont k)
  | K.SetAttr3 (_, v1, v2, k) ->
    LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_kont k]
  | K.GetObjAttr (_, k) -> locs_of_kont k
  | K.SetObjAttr (_, _, k) -> locs_of_kont k
  | K.SetObjAttr2 (_, v, k) -> LocSet.union (locs_of_value v) (locs_of_kont k)
  | K.GetField (_, _, _, e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.GetField2 (_, _, v, e, k) -> LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kont k]
  | K.GetField3 (_, v1, v2, e, k) ->
    LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_env e; locs_of_kont k]
  | K.GetField4 (e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.SetField (_, _, _, _, e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.SetField2 (_, _, _, v, e, k) ->
    LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kont k]
  | K.SetField3 (_, _, v1, v2, e, k) ->
    LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_env e; locs_of_kont k]
  | K.SetField4 (_, v1, v2, v3, e, k) ->
    LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_value v3; locs_of_env e;
                   locs_of_kont k]
  | K.SetField5 (e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.OwnFieldNames k -> locs_of_kont k
  | K.DeleteField (_, _, k) -> locs_of_kont k
  | K.DeleteField2 (_, v, k) -> LocSet.union (locs_of_value v) (locs_of_kont k);
  | K.OpOne (_, k) -> locs_of_kont k
  | K.OpTwo (_, _, k) -> locs_of_kont k
  | K.OpTwo2 (_, v, k) -> LocSet.union (locs_of_value v) (locs_of_kont k)
  | K.If (e, _, _, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.App (_, e, _, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.App2 (_, v, e, vs, _, k) ->
    LocSet.unions (locs_of_values vs [locs_of_value v; locs_of_env e; locs_of_kont k])
  | K.App3 (e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.Seq (_, k) -> locs_of_kont k
  | K.Let (_, _, k) -> locs_of_kont k
  | K.Rec (l, _, k) -> LocSet.add l (locs_of_kont k)
  | K.Break (_, k) -> locs_of_kont k
  | K.TryCatch (_, _, e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.TryCatch2 (_, v, e, k) -> LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kont k]
  | K.TryCatch3 (e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.TryFinally (_, e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.TryFinally2 (_, e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.Throw k -> locs_of_kont k
  | K.Eval (_, _, _, k) -> locs_of_kont k
  | K.Eval2 (_, _, _, k) -> locs_of_kont k
  | K.Eval3 (_, k) -> locs_of_kont k
  | K.Hint k -> locs_of_kont k
  | K.Object (_, k) -> locs_of_kont k
  | K.Object2 (attrsv, _, propvs, k) ->
    LocSet.unions (locs_of_propvs propvs [locs_of_attrsv attrsv; locs_of_kont k])
  | K.Attrs (_, _, nvs, _, _, k) ->
    LocSet.unions (List.fold_left (fun a (_, n) -> (locs_of_value n)::a) [locs_of_kont k] nvs)
  | K.DataProp (_, _, _, _, k) -> locs_of_kont k
  | K.AccProp (_, _, _, _, k) -> locs_of_kont k
  | K.AccProp2 (_, v, _, _, k) -> LocSet.union (locs_of_value v) (locs_of_kont k)
  | K.Label (_, e, k) -> LocSet.union (locs_of_env e) (locs_of_kont k)
  | K.Mt -> LocSet.empty

let should_print = false
let store_gc_size = 1500
let gc_instr_count = 5000

let count ((obj_s, _), (val_s, _)) =
  let folder = (fun _ _ n -> n+1) in
  (LocMap.fold folder obj_s 0, LocMap.fold folder val_s 0)

let print_debug ce s k i = begin
  print_string ("\n$$"^(string_of_int i)^"\n") ;
  print_string (string_of_clos ce s) ;
  print_string "\nStore:\n" ;
  match (count s) with
  | obj_count, val_count -> print_string ((string_of_int obj_count)^" "^(string_of_int val_count)) ;
    print_string "\n" ;
    print_values s ;
    print_string "\n" ;
    print_objects s ;
    print_string "\n" ;
    print_string (string_of_kont k) ;
end

(* eval_cesk : (string -> Ljs_syntax.exp) clos (objectv Store.t * value Store.t) kont int bool ->
   value * store *)
let rec eval_cesk desugar clos store kont i debug =
  let store =
    if i mod gc_instr_count = 0 then
      match count store with
      | obj_count, val_count ->
        if obj_count > store_gc_size or val_count > store_gc_size then
          Ljs_gc.collect_garbage store (LocSet.union (locs_of_closure clos) (locs_of_kont kont))
        else store
    else store in
  begin
    if debug then print_debug clos store kont i ;
    let eval clos store kont = eval_cesk desugar clos store kont (i+1) debug in
    match clos, kont with
    | ValClosure (valu, env), K.Mt ->
      (valu, store)
    (* value cases *)
    | ExpClosure (S.Undefined _, env), _ ->
      eval (ValClosure (Undefined, env)) store kont
    | ExpClosure (S.Null _, env), _ ->
      eval (ValClosure (Null, env)) store kont
    | ExpClosure (S.String (_, s), env), _ ->
      eval (ValClosure (String s, env)) store kont
    | ExpClosure (S.Num (_, n), env), _ ->
      eval (ValClosure (Num n, env)) store kont
    | ExpClosure (S.True _, env), _ ->
      eval (ValClosure (True, env)) store kont
    | ExpClosure (S.False _, env), _ ->
      eval (ValClosure (False, env)) store kont
    | ExpClosure (S.Id (p, name), env), _ ->
      (match try get_maybe_var store (IdMap.find name env) with Not_found -> None with
      | Some valu -> eval (ValClosure (valu, env)) store kont
      | None      -> failwith ("[interp] Unbound identifier: " ^ name ^ " in identifier lookup at " ^
                                  (Pos.string_of_pos p)))
    | ExpClosure (S.Lambda (_, xs, body), env), k ->
      let free = S.free_vars body in
      let env' = IdMap.filter (fun var _ -> IdSet.mem var free) env in
      eval (ValClosure (Closure (env', xs, body), env)) store k
    (* S.SetBang (pos, name, next)
     * Set name to next. *)
    | ExpClosure (S.SetBang (p, x, new_val_exp), env), k ->
      (match try Some (IdMap.find x env) with Not_found -> None with
      | Some loc -> eval (ExpClosure (new_val_exp, env)) store (K.SetBang (loc, k))
      | None     -> failwith ("[interp] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^ (Pos.string_of_pos p)))
    | ValClosure (v, env), K.SetBang (loc, k) ->
      let store' = set_var store loc v in
      eval (ValClosure (v, env)) store' k
    (* S.Object (pos, attrs, props)
     * Evaluates the attrs, props, then adds the object to the
     * obj half of the store. *)
    | ExpClosure (S.Object (p, attrs, props), env), k ->
      eval (AEClosure (attrs, env)) store (K.Object (props, k))
    | AVClosure (valu, env), K.Object ([], k) -> (* empty props case *)
      let obj_loc, store = add_obj store (valu, IdMap.empty) in
      eval (ValClosure (ObjLoc obj_loc, env)) store k
    | AVClosure (attrsv, env), K.Object (prop::props, k) ->
      eval (PEClosure (prop, env)) store (K.Object2 (attrsv, props, [], k))
    | PVClosure (propv, env), K.Object2 (attrsv, prop::props, propvs, k) ->
      eval (PEClosure (prop, env)) store (K.Object2 (attrsv, props, propv::propvs, k))
    | PVClosure (propv, env), K.Object2 (attrsv, [], propvs, k) ->
      let add_prop acc (name, propv) = IdMap.add name propv acc in
      let propsv = List.fold_left add_prop IdMap.empty (propv::propvs) in
      let obj_loc, store = add_obj store (attrsv, propsv) in
      eval (ValClosure (ObjLoc obj_loc, env)) store k
    (* S.Data ({ exp; writable }, enum, config)
     * Evaluates exp, then continues with the propv to object creation.
     * S.Accessor ({ getter; setter }, enum, config)
     * Same as S.Data, but with getter and setter.  *)
    | PEClosure ((name, prop), env), k ->
      (match prop with
      | S.Data ({ S.value = valu; S.writable = writable; }, enum, config) ->
        eval (ExpClosure (valu, env)) store (K.DataProp (name, writable, enum, config, k))
      | S.Accessor ({ S.getter = getter; S.setter = setter; }, enum, config) ->
        eval (ExpClosure (getter, env)) store (K.AccProp (name, setter, enum, config, k)))
    | ValClosure (valu, env), K.DataProp (name, writable, enum, config, k) ->
      eval (PVClosure ((name, Data ({ value=valu; writable=writable; }, enum, config)), env)) store k
    | ValClosure (get_val, env), K.AccProp (name, setter, enum, config, k) ->
      eval (ExpClosure (setter, env)) store (K.AccProp2 (name, get_val, enum, config, k))
    | ValClosure (set_val, env), K.AccProp2 (name, get_val, enum, config, k) ->
      eval (PVClosure ((name, Accessor ({ getter=get_val; setter=set_val; }, enum, config)), env)) store k
    (* S.attrs : { primval; code; proto; class; extensible }
     * Evaluates optional exps primval, code, and proto, then continues
     * with an S.arrtsv. *)
    | AEClosure (attrs, env), k ->
      let { S.primval = pexp;
            S.code = cexp;
            S.proto = proexp;
            S.klass = kls;
            S.extensible = ext; } = attrs in
      let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
      let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
      (match aes with
      | [] ->
        let attrsv = { code=None; proto=Undefined; primval=None; klass=kls; extensible=ext } in
        eval (AVClosure (attrsv, env)) store k
      | (name, exp)::pairs -> eval (ExpClosure (exp, env)) store (K.Attrs (name, pairs, [], kls, ext, k)))
    | ValClosure (valu, env), K.Attrs (name, (name', exp)::pairs, valus, kls, ext, k) ->
      eval (ExpClosure (exp, env)) store (K.Attrs (name', pairs, (name, valu)::valus, kls, ext, k))
    | ValClosure (valu, env), K.Attrs (name, [], valus, kls, ext, k) ->
      let valus = (name, valu)::valus in
      let rec opt_get name xs = match xs with
        | [] -> None
        | (name', valu)::xs' -> if name = name' then Some valu else opt_get name xs' in
      let rec und_get name xs = match xs with
        | [] -> Undefined
        | (name', valu)::xs' -> if name = name' then valu else und_get name xs' in
      let attrsv = { code=(opt_get "code" valus);
                     proto=(und_get "proto" valus);
                     primval=(opt_get "primval" valus);
                     klass=kls;
                     extensible=ext; } in
      eval (AVClosure (attrsv, env)) store k
    (* S.GetAttr (pos, pattr, obj, field)
     * Get the pattr for the obj's field using Ljs_eval's get_attr. *)
    | ExpClosure (S.GetAttr (_, attr, obj, field), env), k ->
      eval (ExpClosure (obj, env)) store (K.GetAttr (attr, field, k))
    | ValClosure (obj_val, env), K.GetAttr (attr, field, k) ->
      eval (ExpClosure (field, env)) store (K.GetAttr2 (attr, obj_val, k))
    | ValClosure (field_val, env), K.GetAttr2 (attr, obj_val, k) ->
      eval (ValClosure (L.get_attr store attr obj_val field_val, env)) store k
    (* S.SetAttr (pos, pattr, obj, field, next)
     * The pattr for the obj's field is set to next, using Ljs_eval's
     * set_attr. *)
    | ExpClosure (S.SetAttr (_, pattr, obj, field, next), env), k ->
      eval (ExpClosure (obj, env)) store (K.SetAttr (pattr, field, next, k))
    | ValClosure (obj_val, env), K.SetAttr (pattr, field, next, k) ->
      eval (ExpClosure (field, env)) store (K.SetAttr2 (pattr, next, obj_val, k))
    | ValClosure (field_val, env), K.SetAttr2 (pattr, next, obj_val, k) ->
      eval (ExpClosure (next, env)) store (K.SetAttr3 (pattr, obj_val, field_val, k))
    | ValClosure (valu, env), K.SetAttr3 (pattr, obj_val, field_val, k) ->
      let b, store = set_attr store pattr obj_val field_val valu in
      eval (ValClosure (bool b, env)) store k
    (* S.GetObjAttr (pos, oattr, obj)
     * Get the oattr for obj. *)
    | ExpClosure (S.GetObjAttr (_, oattr, obj), env), k ->
      eval (ExpClosure (obj, env)) store (K.GetObjAttr (oattr, k))
    | ValClosure (obj_val, env), K.GetObjAttr (oattr, k) ->
      (match obj_val with
      | ObjLoc obj_loc ->
        let (attrs, _) = get_obj store obj_loc in
        eval (ValClosure (get_obj_attr attrs oattr, env)) store k
      | _ -> failwith ("[interp] GetObjAttr got a non-object: " ^
                          (pretty_value obj_val)))
    (* S.SetObjAttr (pos, oattr, obj, next)
     * The oattr for obj is set to next. *)
    | ExpClosure (S.SetObjAttr (_, oattr, obj, next), env), k ->
      eval (ExpClosure (obj, env)) store (K.SetObjAttr (oattr, next, k))
    | ValClosure (obj_val, env), K.SetObjAttr (oattr, next, k) ->
      eval (ExpClosure (next, env)) store (K.SetObjAttr2 (oattr, obj_val, k))
    | ValClosure (valu, env), K.SetObjAttr2 (oattr, obj_val, k) ->
      (match obj_val with
      | ObjLoc loc ->
        let (attrs, props) = get_obj store loc in
        let attrs' = match oattr, valu with
          | S.Proto, ObjLoc _
          | S.Proto, Null -> { attrs with proto=valu }
          | S.Proto, _ ->
            failwith ("[interp] Update proto failed: " ^
                      (pretty_value valu))
          | S.Extensible, True  -> { attrs with extensible=true }
          | S.Extensible, False -> { attrs with extensible=false }
          | S.Extensible, _ ->
            failwith ("[interp] Update extensible failed: " ^
                      (pretty_value valu))
          | S.Code, _ -> failwith "[interp] Can't update Code"
          | S.Primval, v -> { attrs with primval=Some v }
          | S.Klass, _ -> failwith "[interp] Can't update Klass" in
        eval (ValClosure (valu, env)) (set_obj store loc (attrs', props)) k
      | _ -> failwith ("[interp] SetObjAttr got a non-object: " ^
                       (pretty_value obj_val)))
    (* S.GetField (pos, obj, field, body)
     * If the getter field in obj is evaluated and, is a data
     * property, continues with the value; if an accessor, evaluates
     * the getter with the body and the obj values as arguments. *)
    | ExpClosure (S.GetField (p, obj, field, body), env), k ->
      eval (ExpClosure (obj, env)) store (K.GetField (p, field, body, env, k))
    | ValClosure (obj_val, env), K.GetField (p, field, body, env', k) ->
      eval (ExpClosure (field, env)) store (K.GetField2 (p, body, obj_val, env', k))
    | ValClosure (field_val, env), K.GetField2 (p, body, obj_val, env', k) ->
      eval (ExpClosure (body, env)) store (K.GetField3 (p, obj_val, field_val, env', k))
    | ValClosure (body_val, env), K.GetField3 (p, obj_val, field_val, env', k) ->
      (match (obj_val, field_val) with
      | (ObjLoc _, String s) ->
        let prop = get_prop p store obj_val s in
        (match prop with
        | Some (Data ({value=v;}, _, _)) -> eval (ValClosure (v, env')) store k
        | Some (Accessor ({getter=g;},_,_)) ->
          let (body, env'', store') = (apply p store g [obj_val; body_val]) in
          eval (ExpClosure (body, env'')) store' (K.GetField4 (env', k))
        | None -> eval (ValClosure (Undefined, env')) store k)
      | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                       ^ Pos.string_of_pos p ^ ". Instead, it got "
                       ^ pretty_value obj_val ^ " and "
                       ^ pretty_value field_val))
    | ValClosure (acc_val, _), K.GetField4 (env, k) ->
      eval (ValClosure (acc_val, env)) store k
    (* S.OwnFieldNames (pos, obj)
     * Create an object in the store with a map of indices to all
     * obj's properties and the count of that map. *)
    | ExpClosure (S.OwnFieldNames (p, obj), env), k ->
      eval (ExpClosure (obj, env)) store (K.OwnFieldNames k)
    | ValClosure (obj_val, env), K.OwnFieldNames k ->
      (match obj_val with
      | ObjLoc loc ->
        let _, props = get_obj store loc in
        let add_name n x m =
          IdMap.add (string_of_int x) (Data ({ value = String n; writable = false; },
                                             false,
                                             false)) m in
        let names = IdMap.fold (fun k v l -> (k :: l)) props [] in
        let props = List.fold_right2 add_name names (iota (List.length names)) IdMap.empty in
        let d = float_of_int (List.length names) in
        let final_props =
          IdMap.add "length" (Data ({ value = Num d; writable = false; },
                                    false,
                                    false)) props in
        let (new_obj, store) = add_obj store (d_attrsv, final_props) in
        eval (ValClosure (ObjLoc new_obj, env)) store k
      | _ -> failwith ("[interp] OwnFieldNames didn't get an object," ^
                          " got " ^ (pretty_value obj_val) ^ " instead."))
    (* S.DeleteField(pos, obj, field)
     * Deletes field from obj. *)
    | ExpClosure (S.DeleteField (p, obj, field), env), k ->
      eval (ExpClosure (obj, env)) store (K.DeleteField (p, field, k))
    | ValClosure (obj_val, env), K.DeleteField (p, field, k) ->
      eval (ExpClosure (field, env)) store (K.DeleteField2 (p, obj_val, k))
    | ValClosure (field_val, env), K.DeleteField2 (p, obj_val, k) ->
      (match obj_val, field_val with
      | ObjLoc loc, String s ->
        (match get_obj store loc with
        | attrs, props ->
          (try match IdMap.find s props with
          | Data (_, _, true)
          | Accessor (_, _, true) ->
            let store' = set_obj store loc (attrs, IdMap.remove s props) in
            eval (ValClosure (True, env)) store' k
          | _ -> eval (LobClosure (Throw ([], String "unconfigurable-delete", store))) store k
           with Not_found -> eval (ValClosure (False, env)) store k))
      | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                       ^ Pos.string_of_pos p
                       ^ ". Instead, it got "
                       ^ pretty_value obj_val
                       ^ " and "
                       ^ pretty_value field_val))
    (* S.SetField (pos, obj, field, next, body)
     * Sets obj's field to next by executing body. *)
    | ExpClosure (S.SetField (p, obj, field, next, body), env), k ->
      eval (ExpClosure (obj, env)) store (K.SetField  (p, field, next, body, env, k))
    | ValClosure (obj_val, env), K.SetField  (p, field, next, body, env', k) ->
      eval (ExpClosure (field, env)) store (K.SetField2 (p, next, body, obj_val, env', k))
    | ValClosure (field_val, env), K.SetField2 (p, next, body, obj_val, env', k) ->
      eval (ExpClosure (next, env)) store (K.SetField3 (p, body, obj_val, field_val, env', k))
    | ValClosure (valu, env), K.SetField3 (p, body, obj_val, field_val, env', k) ->
      eval (ExpClosure (body, env)) store (K.SetField4 (p, obj_val, field_val, valu, env', k))
    | ValClosure (body_val, env), K.SetField4 (p, obj_val, field_val, valu, env', k) ->
      (match (obj_val, field_val) with
      | (ObjLoc loc, String s) ->
        let ({extensible=extensible;} as attrs, props) = get_obj store loc in
        let prop = get_prop p store obj_val s in
        let unwritable = (Throw ([], String "unwritable-field", store)) in
        (match prop with
        | Some (Data ({ writable = true; }, enum, config)) ->
          let (enum, config) =
            if (IdMap.mem s props)
            then (enum, config) (* 8.12.5, step 3, changing the value of a field *)
            else (true, true) in (* 8.12.4, last step where inherited.[[writable]] is true *)
          let store = set_obj store loc
            (attrs,
             IdMap.add s (Data ({ value = valu; writable = true }, enum, config)) props) in
          eval (ValClosure (valu, env)) store k
        | Some (Data _) -> eval (LobClosure unwritable) store k
        | Some (Accessor ({ setter = Undefined; }, _, _)) ->
          eval (LobClosure unwritable) store k
        | Some (Accessor ({ setter = setterv; }, _, _)) ->
          (* 8.12.5, step 5 *)
          let (body, env'', store') = apply p store setterv [obj_val; body_val] in
          eval (ExpClosure (body, env'')) store' (K.SetField5 (env', k))
        | None ->
          (* 8.12.5, step 6 *)
          if extensible
          then
            let store = set_obj store loc
              (attrs,
               IdMap.add s (Data ({ value = valu; writable = true; }, true, true)) props) in
            eval (ValClosure (valu, env)) store k
          else
            eval (ValClosure (Undefined, env)) store k)
      | _ -> failwith ("[interp] Update field didn't get an object and a string"
                       ^ Pos.string_of_pos p ^ " : " ^ (pretty_value obj_val) ^
                         ", " ^ (pretty_value field_val)))
    | ValClosure (acc_val, _), K.SetField5 (env, k) ->
      eval (ValClosure (acc_val, env)) store k
    (* S.Op1 (pos, name, arg)
     * Evaluates a unary operation name on arg. *)
    | ExpClosure (S.Op1 (_, name, arg), env), k ->
      eval (ExpClosure (arg, env)) store (K.OpOne (name, k))
    | ValClosure (arg_val, env), K.OpOne (name, k) ->
      eval (ValClosure (op1 store name arg_val, env)) store k
    (* S.Op2 (pos, name, arg1, arg2)
     * Evaluates a binary operation name on arg1 and arg2. *)
    | ExpClosure (S.Op2 (_, name, arg1, arg2), env), k ->
      eval (ExpClosure (arg1, env)) store (K.OpTwo (name, arg2, k))
    | ValClosure (arg1_val, env), K.OpTwo (name, arg2, k) ->
      eval (ExpClosure (arg2, env)) store (K.OpTwo2 (name, arg1_val, k))
    | ValClosure (arg2_val, env), K.OpTwo2 (name, arg1_val, k) ->
      eval (ValClosure (op2 store name arg1_val arg2_val, env)) store k
    (* S.If (pos, pred, then, else)
     * Evaluates then if pred, else otherwise. *)
    | ExpClosure (S.If (_, pred, than, elze), env), k ->
      eval (ExpClosure (pred, env)) store (K.If (env, than, elze, k))
    | ValClosure (pred_val, env), K.If (env', than, elze, k) ->
      if (pred_val = True)
      then eval (ExpClosure (than, env')) store k
      else eval (ExpClosure (elze, env')) store k
    (* S.App (pos, func, args)
     * Applies the body of func with the given args. *)
    | ExpClosure (S.App (pos, func, args), env), k ->
      eval (ExpClosure (func, env)) store (K.App (pos, env, args, k))
      (* special case for no arg apps *)
    | ValClosure (func, env), K.App (pos, env', [], k) ->
      let (body, env'', store') = apply pos store func [] in
      eval (ExpClosure (body, env'')) store' (K.App3 (env', k))
    | ValClosure (func, env), K.App  (pos, env', expr::exprs, k) ->
      eval (ExpClosure (expr, env')) store (K.App2 (pos, func, env', [] , exprs, k))
    | ValClosure (arg_val, env), K.App2 (pos, func, env', vs, expr::exprs, k) ->
      eval (ExpClosure (expr, env')) store (K.App2 (pos, func, env', arg_val::vs, exprs, k))
    | ValClosure (arg_val,  env), K.App2 (pos, func, env', vs, [], k) ->
      let (body, env'', store') = apply pos store func (List.rev (arg_val::vs)) in
      eval (ExpClosure (body, env'')) store' (K.App3 (env', k))
    | ValClosure (body_val, _), K.App3 (env', k) ->
      eval (ValClosure (body_val, env')) store k
    (* S.Seq (pos, left, right)
     * Evaluates left then right, continuing with right's value. *)
    | ExpClosure (S.Seq (_, left, right), env), k ->
      eval (ExpClosure (left, env)) store (K.Seq (right, k))
    | ValClosure (_, env), K.Seq (right, k) ->
      eval (ExpClosure (right, env)) store k
    (* S.Let (pos, name, expr, body)
     * Evaluates body with name bound to expr. *)
    | ExpClosure (S.Let (_, name, expr, body), env), k ->
      eval (ExpClosure (expr, env)) store (K.Let (name, body, k))
    | ValClosure (v, env), K.Let (name, body, k) ->
      let (new_loc, store') = add_var store v in
      eval (ExpClosure (body, IdMap.add name new_loc env)) store' k
    (* S.Rec (pos, name, expr, body)
     * Evaluates body with name bound to expr, which may contain
     * recursive references to name. *)
    | ExpClosure (S.Rec (_, name, expr, body), env), k ->
      let (new_loc, store') = add_var store Undefined in
      let env' = IdMap.add name new_loc env in
      eval (ExpClosure (expr, env')) store' (K.Rec (new_loc, body, k))
    | ValClosure (v, env), K.Rec (new_loc, body, k) ->
      eval (ExpClosure (body, env)) (set_var store new_loc v) k
    (* S.Label (pos, name, expr)
     * Evaluates expr, catching any Breaks with the matching name. *)
    | ExpClosure (S.Label (_, name, exp), env), k ->
      eval (ExpClosure (exp, env)) store (K.Label (name, env, k))
    | ValClosure (valu, env), K.Label (_, _, k) ->
      eval (ValClosure (valu, env)) store k
    (* S.Break (pos, label, expr)
     * Breaks to label with expr as the value passed back. *)
    | ExpClosure (S.Break (_, label, expr), env), k ->
      eval (ExpClosure (expr, env)) store (K.Break (label, k))
    | ValClosure (v, _), K.Break (label, k) ->
      eval (LobClosure (Break ([], label, v, store))) store k
    | LobClosure (Break (t, label, v, store')), K.Label (name, env, k) ->
      if name = label then eval (ValClosure (v, env)) store k
      else eval (LobClosure (Break (t, label, v, store'))) store k
    (* S.TryCatch (pos, body, catch)
     * Evaluates body, evaluating catch with the thrown value as an
     * argument if a Throw is lobbed up. *)
    | ExpClosure (S.TryCatch (p, body, catch), env), k ->
      eval (ExpClosure (body, env)) store (K.TryCatch (p, catch, env, k))
    | ValClosure (body_val, env'), K.TryCatch (p, catch, env, k) ->
      eval (ValClosure (body_val, env')) store k
    | LobClosure (Throw (_, throw_val, store)), K.TryCatch (p, catch, env, k) ->
      eval (ExpClosure (catch, env)) store (K.TryCatch2 (p, throw_val, env, k))
    | ValClosure (catch_val, env'), K.TryCatch2 (p, throw_val, env, k) ->
      let (body, env'', store') = apply p store catch_val [throw_val] in
      eval (ExpClosure (body, env'')) store' (K.TryCatch3 (env, k))
    | ValClosure (catch_body_val, _), K.TryCatch3 (env, k) ->
      eval (ValClosure (catch_body_val, env)) store k
    (* S.TryFinally (pos, body, fin)
     * Evaluates body then fin; if an exception is thrown from body
     * fin will be executed and the exn's store is updated. *)
    | ExpClosure (S.TryFinally (_, body, fin), env), k ->
      eval (ExpClosure (body, env)) store (K.TryFinally (fin, env, k))
    | ValClosure (valu, env'), K.TryFinally (fin, env, k) ->
      eval (ExpClosure (fin, env)) store k
    | LobClosure except, K.TryFinally (fin, env, k) ->
      eval (ExpClosure (fin, env)) store (K.TryFinally2 (except, env, k))
    | ValClosure (_, _), K.TryFinally2 (except, env, k) ->
      (match except with
      | Throw (t, v, _) -> eval (LobClosure (Throw (t, v, store))) store k
      | Break (t, l, v, _) -> eval (LobClosure (Break (t, l, v, store))) store k
      | _ -> failwith "Try finally caught something other than a throw or break.")
    (* S.Throw (pos, expr)
     * Lobs expr up through the future konts. *)
    | ExpClosure (S.Throw (_, expr), env), k ->
      eval (ExpClosure (expr, env)) store (K.Throw k)
    | ValClosure (valu, env), K.Throw k ->
      eval (LobClosure (Throw ([], valu, store))) store k
    (* S.Eval (pos, str_expr, bindings)
     * Evaluates str_expr with the fields defined in the object
     * bindings added to the environment. *)
    | ExpClosure (S.Eval (pos, str, bindings), env), k ->
      eval (ExpClosure (str, env)) store (K.Eval (pos, bindings, store, k))
    | ValClosure (str_val, env), K.Eval (pos, bindings, store', k) ->
      eval (ExpClosure (bindings, env)) store (K.Eval2 (pos, str_val, store', k))
    | ValClosure (bind_val, env), K.Eval2 (pos, str_val, store', k) ->
      (match str_val, bind_val with
      | String s, ObjLoc o ->
        let expr = desugar s in
        let env', store'' = envstore_of_obj pos (get_obj store o) store in
        eval (ExpClosure (expr, env')) store'' (K.Eval3 (store', k))
      | String _, _ -> interp_error pos "Non-object given to eval() for env"
      | v, _ -> eval (ValClosure (v, env)) store' k)
    | ValClosure (valu, env), K.Eval3 (store', k) ->
      eval (ValClosure (valu, env)) store' k
    (* S.Hint (pos, str, expr)
     * Evaluates expr, continuing with a Snapshot if str is
     * "___takeS5Snapshot", or just continues with expr's val. *)
    | ExpClosure (S.Hint (_, "___takeS5Snapshot", expr), env), k ->
      eval (ExpClosure (expr, env)) store (K.Hint k)
    | ExpClosure (S.Hint (_, _, expr), env), k ->
      eval (ExpClosure (expr, env)) store k
    | ValClosure (valu, env), K.Hint k ->
      eval (LobClosure (Snapshot ([], valu, [], store))) store k
    (* control cases. TODO: make own exns, remove the store from them. *)
    | LobClosure exn, K.Mt -> raise exn
    | LobClosure (Break (exprs, l, v, s)), k ->
      eval (LobClosure (Break (add_opt clos exprs exp_of, l, v, s))) store (shed k)
    | LobClosure (Throw (exprs, v, s)), k ->
      eval (LobClosure (Throw (add_opt clos exprs exp_of, v, s))) store (shed k)
    | LobClosure (PrimErr (exprs, v)), k ->
      eval (LobClosure (PrimErr (add_opt clos exprs exp_of, v))) store (shed k)
    | LobClosure (Snapshot (exprs, v, envs, s)), k ->
      let snap = Snapshot (add_opt clos exprs exp_of, v, add_opt clos envs env_of, s) in
      eval (LobClosure snap) store (shed k)
    | _ -> begin
      print_debug clos store kont i ;
      failwith "Encountered an unmatched eval_cesk case."
    end
  end

(*     expr => Ljs_syntax.exp
       desugar => (string -> Ljs_syntax.exp)
       print_trace => bool
       env => IdMap
       store => (Store, Store)
       where the left is for objects and
       the right is for values            *)
let continue_eval expr desugar print_trace env store =
  try
    Sys.catch_break true;
    let (v, store) = eval_cesk desugar (ExpClosure (expr, env)) store K.Mt 0 should_print in
    L.Answer ([], v, [], store)
  with
  | Snapshot (exprs, v, envs, store) ->
    L.Answer (exprs, v, envs, store)
  | Throw (t, v, store) ->
    let err_msg =
      match v with
      | ObjLoc loc -> begin match get_obj store loc with
        | _, props -> try match IdMap.find "%js-exn" props with
          | Data ({value=jserr}, _, _) -> string_of_value jserr store
          | _ -> string_of_value v store
          with Not_found -> string_of_value v store
      end
      | v -> string_of_value v store in
    err print_trace t (sprintf "Uncaught exception: %s\n" err_msg)
  | Break (p, l, v, _) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | PrimErr (t, v) ->
    err print_trace t (sprintf "Uncaught error: %s\n" (pretty_value v))

(*     expr => Ljs_syntax.exp
       desugar => (string -> Ljs_syntax.exp)
       print_trace => bool                       *)
let eval_expr expr desugar print_trace =
  continue_eval expr desugar print_trace IdMap.empty (Store.empty, Store.empty)

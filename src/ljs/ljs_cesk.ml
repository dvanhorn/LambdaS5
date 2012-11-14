open Ljs_delta
open Ljs_pretty
open Ljs_values
open Prelude

module S = Ljs_syntax
module K = Ljs_kont

let interp_error pos message =
  raise (PrimErr ([], String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))

(* Machine-specific closures *)
type closure = ExpClosure of S.exp * env
             | ValClosure of value * env ;;

let exp_of clos = match clos with
  | ExpClosure (expr, _) -> Some expr
  | _ -> None
let env_of clos = match clos with
  | ExpClosure (_, env) -> Some env
  | _ -> None
let add_opt clos xs f = match f clos with
  | Some x -> x::xs
  | None -> xs

(* from ljs_eval, let's move these to a util file eventuallly *)
let rec get_attr store attr obj field = match obj, field with
  | ObjLoc loc, String s -> let (attrs, props) = get_obj store loc in
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
                     ^ pretty_value obj
                     ^ " " ^ field ^ ")")

(* end borrowed ljs_eval helpers *)

let rec eval_cesk desugar clos store kont : (value * store) =
  let eval clos store kont =
    begin try eval_cesk desugar clos store kont with
    | Break (exprs, l, v, s) ->
      raise (Break (add_opt clos exprs exp_of, l, v, s))
    | Throw (exprs, v, s) ->
      raise (Throw (add_opt clos exprs exp_of, v, s))
    | PrimErr (exprs, v) ->
      raise (PrimErr (add_opt clos exprs exp_of, v))
    | Snapshot (exps, v, envs, s) ->
      raise (Snapshot (add_opt clos exps exp_of, v, add_opt clos envs env_of, s))
    | Sys.Break ->
      raise (PrimErr (add_opt clos [] exp_of, String "s5_cesk_eval stopped by user interrupt"))
    | Stack_overflow ->
      raise (PrimErr (add_opt clos [] exp_of, String "s5_cesk_eval overflowed the Ocaml stack"))
    end in
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
                         pretty_value func)) in
  match clos, kont with
  | ValClosure (valu, env), K.Mt -> (valu, store)
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
    (try
      let valu = get_var store (IdMap.find name env) in
      eval (ValClosure (valu, env)) store kont
    with Not_found ->
      failwith ("[interp] Unbound identifier: " ^ name ^ " in identifier lookup at " ^
                   (Pos.string_of_pos p)))
  | ExpClosure (S.Lambda (_, xs, body), env), k -> (* should we remove the env' from Closure? *)
    let free = S.free_vars body in
    let env' = IdMap.filter (fun var _ -> IdSet.mem var free) env in
    eval (ValClosure (Closure (env', xs, body), env')) store k
  (* SetBang cases *)
  (* TODO(adam): error cases for non-existent id's *)
  | ExpClosure (S.SetBang (_, x, exp'), env), k ->
    eval (ExpClosure (exp', env)) store (K.SetBang (IdMap.find x env, k))
  | ValClosure (v, env), K.SetBang (loc, k) ->
    let store' = set_var store loc v in
    eval (ValClosure (v, env)) store' k
  (* Object cases *)
  (*| ExpClosure*)
  (* GetAttr *)
  (* better way to do this? it's non-exhaustive, but shouldn't be an issue we
     we are guaranteeing left to right evaluation on the obj / field *)
  | ExpClosure (S.GetAttr (p, attr, obj, field), env), k ->
    eval (ExpClosure (obj, env)) store (K.GetAttr (attr, None, Some field, k))
  | ValClosure (obj_val, env), K.GetAttr (attr, None, Some field, k) ->
    eval (ExpClosure (field, env)) store (K.GetAttr (attr, Some obj_val, None, k))
  | ValClosure (field_val, env), K.GetAttr (attr, Some obj_val, None, k) ->
    eval (ValClosure (get_attr store attr obj_val field_val, env)) store k
  (* SetAttr Cases *)
  | ExpClosure (S.SetAttr (_, pattr, oe, pe, new_val_expr), env), k ->
    eval (ExpClosure (oe, env)) store (K.SetAttr (pattr, None, Some pe, None, Some new_val_expr, k))
  | ValClosure (oe_val, env), K.SetAttr (pattr, None, Some pe, None, Some new_val_expr, k) ->
    eval (ExpClosure (pe, env)) store (K.SetAttr (pattr, Some oe_val, None, None, Some new_val_expr, k))
  | ValClosure (pe_val, env), K.SetAttr (pattr, Some oe_val, None, None, Some new_val_expr, k) ->
    eval (ExpClosure (new_val_expr, env)) store (K.SetAttr (pattr, Some oe_val, None, Some pe_val, None, k))
  | ValClosure (new_val, env), K.SetAttr (pattr, Some oe_val, None, Some pe_val, None, k) ->
    let b, store = set_attr store pattr oe_val pe_val new_val in
    eval (ValClosure (bool b, env)) store k
  (* GetObjAttr Cases *)
  | ExpClosure (S.GetObjAttr (_, oattr, obj), env), k ->
    eval (ExpClosure (obj, env)) store (K.GetObjAttr (oattr, k))
  | ValClosure (obj_val, env), K.GetObjAttr (oattr, k) ->
    begin match obj_val with
      | ObjLoc obj_loc ->
        let (attrs, _) = get_obj store obj_loc in
        eval (ValClosure (get_obj_attr attrs oattr, env)) store k
      | _ -> failwith ("[interp] GetObjAttr got a non-object: " ^
                          (pretty_value obj_val))
    end
  (* SetObjAttr Cases *)
  | ExpClosure (S.SetObjAttr (_, oattr, obj_exp, na_exp), env), k ->
    eval (ExpClosure (obj_exp, env)) store (K.SetObjAttr (oattr, None, Some na_exp, k))
  | ValClosure (obj_val, env), K.SetObjAttr (oattr, None, Some na_exp, k) ->
    eval (ExpClosure (na_exp, env)) store (K.SetObjAttr (oattr, Some obj_val, None, k))
  | ValClosure (na_val, env), K.SetObjAttr (oattr, Some obj_val, None, k) ->
    begin match obj_val with
      | ObjLoc loc ->
        let (attrs, props) = get_obj store loc in
        let attrs' = match oattr, na_val with
          | S.Proto, ObjLoc _
          | S.Proto, Null -> { attrs with proto=na_val }
          | S.Proto, _ ->
            failwith ("[interp] Update proto failed: " ^
                       (pretty_value na_val))
          | S.Extensible, True -> { attrs with extensible=true }
          | S.Extensible, False -> { attrs with extensible=false }
          | S.Extensible, _ ->
            failwith ("[interp] Update extensible failed: " ^
                       (pretty_value na_val))
          | S.Code, _ -> failwith "[interp] Can't update Code"
          | S.Primval, v -> { attrs with primval=Some v }
          | S.Klass, _ -> failwith "[interp] Can't update Klass" in
        eval (ValClosure (na_val, env)) (set_obj store loc (attrs', props)) k
      | _ -> failwith ("[interp] SetObjAttr got a non-object: " ^
                        (pretty_value obj_val))
    end
  (* GetField cases *)
  | ExpClosure (S.GetField (p, obj, field, args), env), k ->
    eval (ExpClosure (obj, env)) store (K.GetField (p, field, args, k))
  | ValClosure (obj_val, env), K.GetField (p, field, args, k) ->
    eval (ExpClosure (field, env)) store (K.GetField' (p, obj_val, args, k))
  | ValClosure (field_val, env), K.GetField' (p, obj_val, args, k) ->
    eval (ExpClosure (args, env)) store (K.GetField'' (p, obj_val, field_val, k))
  | ValClosure (args_val, env), K.GetField'' (p, obj_val, field_val, k) ->
    begin match (obj_val, field_val) with
      | (ObjLoc _, String s) ->
        let prop = get_prop p store obj_val s in
        let (v, store') = match prop with
          | Some (Data ({value=v;}, _, _)) -> v, store
          | Some (Accessor ({getter=g;},_,_)) ->
            (apply p store g [obj_val; args_val])
          | None -> Undefined, store in
        eval (ValClosure (v, env)) store' k
      | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                       ^ Pos.string_of_pos p ^ ". Instead, it got "
                       ^ pretty_value obj_val ^ " and "
                       ^ pretty_value field_val)
    end
  (* If cases *)
  | ExpClosure (S.If (_, pred, than, elze), env), k ->
    eval (ExpClosure (pred, env)) store (K.If (env, than, elze, k))
  | ValClosure (v, env), K.If (env', than, elze, k) ->
    if (v = True)
    then eval (ExpClosure (than, env')) store k
    else eval (ExpClosure (elze, env')) store k
  (* App cases *)
  | ExpClosure (S.App (pos, func, args), env), k ->
    eval (ExpClosure (func, env)) store (K.App (pos, None, env, [], args, k))
  | ValClosure (func, _), K.App (pos, None, _, vals, [], k) -> (* special case for no arg apps *)
    let (body, env', store') = apply pos store func vals in
    eval (ExpClosure (body, env')) store' k
  | ValClosure (func, _), K.App (pos, None, env, vs, expr::exprs, k) ->
    eval (ExpClosure (expr, env)) store (K.App (pos, Some func, env, vs, exprs, k))
  | ValClosure (arg_val, _), K.App (pos, Some func, env, vs, expr::exprs, k) ->
    eval (ExpClosure (expr, env)) store (K.App (pos, Some func, env, arg_val::vs, exprs, k))
  | ValClosure (arg_val, _), K.App (pos, Some func, env, vs, [], k) ->
    let (body, env', store') = apply pos store func (arg_val::vs) in (* may need to reverse this list *)
    eval (ExpClosure (body, env')) store' k
  (* sequence (begin) cases *)
  | ExpClosure (S.Seq (_, left, right), env), k ->
    eval (ExpClosure (left, env)) store (K.Seq (right, k))
  | ValClosure (_, env), K.Seq (right, k) ->
    eval (ExpClosure (right, env)) store k
  (* let cases *)
  | ExpClosure (S.Let (_, name, expr, body), env), k ->
    eval (ExpClosure (expr, env)) store (K.Let (name, body, k))
  | ValClosure (v, env), K.Let (name, body, k) ->
    let (new_loc, store') = add_var store v in
    eval (ExpClosure (body, IdMap.add name new_loc env)) store' k
  (* letrec cases *)
  | ExpClosure (S.Rec (_, name, expr, body), env), k ->
    let (new_loc, store') = add_var store Undefined in
    let env' = IdMap.add name new_loc env in
    eval (ExpClosure (expr, env')) store' (K.Rec (new_loc, body, k))
  | ValClosure (v, env), K.Rec (new_loc, body, k) ->
    eval (ExpClosure (body, env)) (set_var store new_loc v) k
  (* Label case, just creates a try that we can break to. Should control flow
     rely on OCaml's control flow? *)
  | ExpClosure (S.Label (_, name, exp), env), k ->
    (try
      eval (ExpClosure (exp, env)) store k
    with Break (t, l', v, store') ->
      if name = l' then (v, store')
      else raise (Break (t, l', v, store')))
  (* break cases, see details in label case for future work *)
  | ExpClosure (S.Break (_, label, expr), env), k ->
    eval (ExpClosure (expr, env)) store (K.Break (label, k))
  | ValClosure (v, _), K.Break (label, _) ->
    raise (Break ([], label, v, store))
  (* try catch *)
  | ExpClosure (S.TryCatch (pos, body, catch), env), k ->
    (try
      eval (ExpClosure (body, env)) store k
    with Throw (_, valu, store) ->
      eval (ExpClosure (catch, env)) store (K.TryCatch (pos, catch, env, valu, k)))
  | ValClosure (valu, _), K.TryCatch (pos, catch, env, throw_val, k) ->
    let (body, env', store') = apply pos store valu [throw_val] in
    eval (ExpClosure (body, env')) store' k
  (* try finally. the semantics below will throw errors which occur during the evaluation
     of the finally clause up, as is the expected? functionality, which is inconsistent with
     the original eval *)
  | ExpClosure (S.TryFinally (_, body, fin), env), k ->
    (try
       eval (ExpClosure (body, env)) store (K.TryFinally (Some fin, env, None, k))
     with
     | except ->
       eval (ExpClosure (fin, env)) store (K.TryFinally (None, env, Some except, k)))
  | ValClosure (valu, env'), K.TryFinally (Some fin, env, None, k) -> (* now evaluate the fin *)
    eval (ExpClosure (fin, env)) store k
  | ValClosure (valu, env'), K.TryFinally (None, env, Some except, k) ->
    (match except with
    | Throw (t, v, _) -> raise (Throw (t, v, store))
    | Break (t, l, v, _) -> raise (Break (t, l, v, store)))
  (* lob those exceptions *)
  | ExpClosure (S.Throw (_, expr), env), k ->
    eval (ExpClosure (expr, env)) store K.Throw
  | ValClosure (valu, env), K.Throw ->
    raise (Throw ([], valu, store))
  (* eval *)
  | ExpClosure (S.Eval (pos, str_expr, bindings), env), k ->
    eval (ExpClosure (str_expr, env)) store (K.Eval (pos, None, Some bindings, store, k))
  | ValClosure (valu, env), K.Eval (pos, None, Some bindings, store', k) ->
    eval (ExpClosure (bindings, env)) store (K.Eval (pos, Some valu, None, store', k))
  | ValClosure (bind_val, env), K.Eval (pos, Some str_val, None, store', k) ->
    (match str_val, bind_val with
    | String s, ObjLoc o ->
      let expr = desugar s in
      let env', store'' = envstore_of_obj pos (get_obj store o) store in
      eval (ExpClosure (expr, env')) store'' (K.Eval (pos, None, None, store', k))
    | String _, _ -> interp_error pos "Non-object given to eval() for env"
    | v, _ -> eval (ValClosure (v, env)) store' k)
  | ValClosure (valu, env), K.Eval (_, None, None, store', k) ->
    eval (ValClosure (valu, env)) store' k
  (* hints, we raise a snapshot if that's what we need to do, otherwise we
     just continue evaluation *)
  | ExpClosure (S.Hint (_, "___takeS5Snapshot", expr), env), k ->
    eval (ExpClosure (expr, env)) store K.Hint
  | ExpClosure (S.Hint (_, _, expr), env), k ->
    eval (ExpClosure (expr, env)) store k
  | ValClosure (valu, env), K.Hint ->
    raise (Snapshot ([], valu, [], store))

and envstore_of_obj p (_, props) store =
  IdMap.fold (fun id prop (env, store) -> match prop with
    | Data ({value=v}, _, _) ->
      let new_loc, store = add_var store v in
      let env = IdMap.add id new_loc env in
      env, store
    | _ -> interp_error p "Non-data value in env_of_obj")
  props (IdMap.empty, store)

and arity_mismatch_err p xs args = interp_error p ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ ". Arg names were: " ^ (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (map (fun v -> " " ^ pretty_value v ^ " ") args) ""))

let err show_stack trace message =
  if show_stack then begin
      eprintf "%s\n" (string_stack_trace trace);
      eprintf "%s\n" message;
      failwith "Runtime error"
    end
  else
    eprintf "%s\n" message;
    failwith "Runtime error"

(*
(*     expr => Ljs_syntax.exp
    desugar => (string -> Ljs_syntax.exp)
print_trace => bool
        env => IdMap
      store => (Store, Store)
               where the left is for objects and
               the right is for values            *)
let continue_eval expr desugar print_trace env store = try
  Sys.catch_break true;
  let (v, store) = eval desugar expr env store in
  Answer ([], v, [], store)
with
  | Snapshot (exprs, v, envs, store) ->
    Answer (exprs, v, envs, store)
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
*)

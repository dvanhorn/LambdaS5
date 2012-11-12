open Prelude
module S = Ljs_syntax
open Format
open Ljs
open Ljs_values
open Ljs_delta
open Ljs_pretty
open Ljs_pretty_value
open Unix
open SpiderMonkey
open Exprjs_to_ljs
open Js_to_exprjs
open Str


type answer = Answer of S.exp list * value * env list * store

let bool b = match b with
  | true -> True
  | false -> False

let unbool b = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (pretty_value b))

let interp_error pos message =
  raise (PrimErr ([], String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))

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

let get_obj_attr attrs attr = match attrs, attr with
  | { proto=proto }, S.Proto -> proto
  | { extensible=extensible} , S.Extensible -> bool extensible
  | { code=Some code}, S.Code -> code
  | { code=None}, S.Code -> Null
  | { primval=Some primval}, S.Primval -> primval
  | { primval=None}, S.Primval ->
      failwith "[interp] Got Primval attr of None"
  | { klass=klass }, S.Klass -> String klass


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

(* 
   The goal here is to maintain a few invariants (implied by 8.12.9
   and 8.10.5), while keeping things simple from a semantic
   standpoint.  The errors from 8.12.9 and 8.10.5 can be defined in
   the environment and enforced that way.  The invariants here make it
   more obvious that the semantics can't go wrong.  In particular, a
   property

   1.  Has to be either an accessor or a data property, and;

   2.  Can't change attributes when Config is false, except for 
       a. Value, which checks Writable
       b. Writable, which can change true->false
*)
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

(*
So, what are our continuations? We'll figure it out by looking at our expressions. Those which
call eval we can call node expressions, because they do not end evaluation. Those which return
values we can call leaf expressions.
Leaf-step:
- S.Hint
- S.Undefined
- S.Null
- S.String
- S.Num
- S.True
- S.False
- S.Id
Node-step:
- S.SetBang
- S.Object
- S.SetField
- S.GetField
- S.DeleteField
- S.GetAttr
- S.SetAttr
- S.GetObjAttr
- S.SetObjAttr
- S.OwnFieldNames
- S.Op1
- S.Op2
- S.If
- S.App
- S.Seq
- S.Let
- S.Rec
- S.Label
- S.Break
- S.TryCatch
- S.TryFinally
- S.Throw
- S.Lambda
- S.Eval
*)

module K = Ljs_kont

type closure = ExpClosure of S.exp * env
             | ValClosure of value * env ;;

let rec eval_cesk desugarer clos store kont : (value * store) =
  let eval clos store kont =
    begin try eval_cesk desugarer clos store kont with
    | Break (exprs, l, v, s) ->
      raise (Break (exp::exprs, l, v, s))
    | Throw (exprs, v, s) ->
      raise (Throw (exp::exprs, v, s))
    | PrimErr (exprs, v) ->
      raise (PrimErr (exp::exprs, v))
    | Snapshot (exps, v, envs, s) ->
      raise (Snapshot (exp :: exps, v, env :: envs, s))
    | Sys.Break ->
      raise (PrimErr ([exp], String "s5_cesk_eval stopped by user interrupt"))
    | Stack_overflow ->
      raise (PrimErr ([exp], String "s5_cesk_eval overflowed the Ocaml stack"))
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
  (* value cases *)
  | ExpClosure (S.Undefined _, env), _ ->
    eval (ValClosure (Undefined, env)) store kont
  | ExpClosure (S.Null _, env), _ ->
    eval (ValClosure (Null, env)) store kont
  | ExpClosure (S.String (_, s), env), _ ->
    eval (ValClosure (String s, env)) store kont
  | ExpClosure (S.Num (_, n), env), _ ->
    eval (ValClosure (Num n, env)) store kont ->
  | ExpClosure (S.True _, env), _ ->
    eval (ValClosure (True, env)) store kont ->
  | ExpClosure (S.False _, env), _ ->
    eval (ValClosure (False, env)) store kont ->
  | ExpClosure (S.Id (p, name), env), _ ->
    begin
      try
        let valu = get_var store (IdMap.find name env) in
        eval (ValClosure (valu, env)) store kont
      with Not_found ->
        failwith ("[interp] Unbound identifier: " ^ x ^ " in identifier lookup at " ^
                     (Pos.string_of_pos p))
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
  | ValClosure (arg_val, _), K.App (pos, Some _, env, vs, expr::exprs, k) ->
    eval (ExpClosure (expr, env)) store (K.App (pos, Some func, env, arg_val::vs, exprs, k))
  | ValClosure (arg_val, _), K.App (pos, Some func, env, vs, [], k) ->
    let (body, env', store') = apply pos store func (arg_val::vs) in (* may need to reverse this list *)
    eval (ExpClosure (body, env')) store' k
  (* sequence (begin) cases *)
  | ExpClosure (S.Seq (left, right), env), k ->
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
  (* Label case, just creates a try that we can break to.
     A more CESKish solution would make a break type that wraps a value,
     and add a case to strip continuations until we hit a K.Label with
     the same name. This would involve modifying the value definition
     to include all things represented with exceptions in ljs_values,
     and those changes would bubble up to be more than we want on this
     first pass. For now, we'll match the original eval. *)
  | ExpClosure (S.Label (_, name, exp), env), k ->
    begin
      try
        eval (ExpClosure (exp, env)) store k
      with Break (t, l', v, store') ->
        if l = l' then (v, store')
        else raise (Break (t, l', v, store'))
    end
  (* break cases, see details in label case for future work *)
  | ExpClosure (S.Break (_, label, expr), env), k ->
    eval (ExpClosure (expr, env)) store (K.Break label k)
  | ValClosure (v, _), K.Break (label, _) ->
    raise (Break ([], label, v, store))
(* still need to do the tries, throw, lambda, eval, and hint *)
    
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

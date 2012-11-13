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

let interp_error pos message =
  raise (PrimErr ([], String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))

module K = Ljs_kont

type closure = ExpClosure of S.exp * env
             | ValClosure of value * env ;;
let exp_of clos = match clos with
  | ExpClosure (expr, _) -> Some expr
  | _ -> None
let add_exp clos exprs = match exp_of clos with
  | Some expr -> expr::exprs
  | None -> exprs
let env_of clos = match clos with
  | ExpClosure (_, env) -> Some env
  | _ -> None
let add_env clos envs = match env_of clos with
  | Some env -> env::envs
  | None -> envs

let rec eval_cesk desugar clos store kont : (value * store) =
  let eval clos store kont =
    begin try eval_cesk desugar clos store kont with
    | Break (exprs, l, v, s) ->
      raise (Break (add_exp clos exprs, l, v, s))
    | Throw (exprs, v, s) ->
      raise (Throw (add_exp clos exprs, v, s))
    | PrimErr (exprs, v) ->
      raise (PrimErr (add_exp clos exprs, v))
    | Snapshot (exps, v, envs, s) ->
      raise (Snapshot (add_exp clos exps, v, add_env clos envs, s))
    | Sys.Break ->
      raise (PrimErr (add_exp clos [], String "s5_cesk_eval stopped by user interrupt"))
    | Stack_overflow ->
      raise (PrimErr (add_exp clos [], String "s5_cesk_eval overflowed the Ocaml stack"))
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

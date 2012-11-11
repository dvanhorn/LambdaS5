open Store
module S = Ljs_syntax

type id = string

(* when I write "we'll have n cases for this...", it means we'll match the 
   expressions to see if they're values, if they are we just move on to the
   next (immediately right) exp, if there are no more exps, we move on. *)

type kont =
| SetBang of Loc.t * kont
  (* created after obtaining new location from the IdMap, then we evaluate the
     S.expression, update the environment and store, and then continue *)
| Object  of S.exp list * S.exp list * (string * S.exp) list * (string * S.exp) list
  (* object of vattrs, expattrs, vprops, expprops,
     where we iterate through expattrs until we have all vattrs, then we iterate
     through expprops until we have all vprops, then we add the object to the store *)
| GetAttr of S.pattr * S.exp * S.exp
  (* getattr of property attribute, object expression, and property expression.
     We'll have three cases for this, where neither exp is a value, the first exp is
     a value but the second is not, and both exps are values. *)
| SetAttr of S.pattr * S.exp * S.exp * S.exp
  (* setattr of property attribute, object expression, property expression, and new value.
     We'll have four cases for this... *)
| GetObjAttr of S.oattr * S.exp
  (* getobjattr of object attribute, object expression,
     We'll have two cases for this...
     we just need to evaluate the object expression and then pull it out of the store *)
| SetObjAttr of S.oattr * S.exp * S.exp
  (* setobjattr of object attribute, object expression, new attribute value expression
     we'll have three cases for this... then we update the store *)
| GetField of S.exp * S.exp * S.exp
  (* getfield of object expression, field expression, arg value
     we'll have four cases for this... *)
| DeleteField of S.exp * S.exp
  (* deletefield of object expression, field expression
     we'll have three cases for this... *)
| SetField of S.exp * S.exp * S.exp * S.exp
  (* setfield of object expression, field expression, new value expression, arg value
     we'll have five cases for this... *)
| OwnFieldNames of S.exp
  (* ownfieldnames of object expression; we'll have two cases for this... *)
| Op1 of string * S.exp
  (* op1 of operation name and argument expression; we'll have two cases for this... *)
| Op2 of string * S.exp * S.exp
  (* op2 of operation name and two argument expressions; we'll have three cases for this... *)
(* ^ aa *)
(* v labichn *)
| If of S.exp * S.exp * S.exp
  (* self explanatory *)
| App of S.exp * S.exp list
  (* app of function and arguments list; we'll have 2+|l| cases for this *)
| Seq of S.exp * S.exp
  (* we'll have three cases for this... *)
| Let of id * S.exp * S.exp
  (* let of name and bound expression and expression in which the name is bound (body)
     we'll evaluate the bound expression, update the env and store, then continue
     to the body *)
| Rec of id * S.exp * S.exp
  (* letrec...; we'll have three cases for this... (first exp must be a lambda) *)
| Label of id * S.exp
  (* label of name and expression, we'll have two cases for this... *)
| Break of id * S.exp
  (* raise a break up to the label denoted by id... we'll have two cases for this... *)
| TryCatch of S.exp * S.exp
  (* try catch of a body and catch block (catch block must be a lambda).
     we'll have three cases for this... *)
| TryFinally of S.exp * S.exp
  (* try to execute the first exp, the body, and finally evaluate and return the evaluation
     of the second exp *)
| Throw of S.exp
  (* evaluate and then throw the expression of this throw *)
| Lambda of id list * exp
  (* self explanatory *)
| Eval of S.exp * S.exp
  (* eval of string exp to be evaled and environment object *)
| Hint of string * S.exp
(* not sure what this guy does yet, looks like there is some snapshot functionality here
   if the string is equal to "___takeS5Snapshot", otherwise the expression is just evaled
   and returned *)

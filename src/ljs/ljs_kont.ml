open Store
module S = Ljs_syntax

(* when I write "we'll have n cases for this...", it means we'll match the 
   expressions to see if they're values, if they are we just move on to the
   next (immediately right) exp, if there are no more exps, we move on. *)

type kont =
  | SetBang of Loc.t * kont
(* created after obtaining new location from the IdMap, then we evaluate the
   expression, update the environment and store, and then continue *)
  | Object  of expr list * expr list * (string * expr) list * (string * expr) list
(* object of vattrs, expattrs, vprops, expprops,
   where we iterate through expattrs until we have all vattrs, then we iterate
   through expprops until we have all vprops, then we add the object to the store *)
  | GetAttr of S.pattr * exp * exp
(* getattr of property attribute, object expression, and property expression.
   We'll have three cases for this, where neither exp is a value, the first exp is
   a value but the second is not, and both exps are values. *)
  | SetAttr of S.pattr * exp * exp * exp
(* setattr of property attribute, object expression, property expression, and new value.
   We'll have four cases for this... *)
  | GetObjAttr of S.oattr * exp
(* getobjattr of object attribute, object expression,
   We'll have two cases for this...
   we just need to evaluate the object expression and then pull it out of the store *)
  | SetObjAttr of S.oattr * exp * exp
(* setobjattr of object attribute, object expression, new attribute value expression
   we'll have three cases for this... then we update the store *)
  | GetField of exp * exp * exp
(* getfield of object expression, field expression, arg value list

(** * Surface notation for the object language.

    A readable syntax for [expr] in scope [react_scope] (key [%r]), so
    that example programs read like the paper's:

<<
  (print: Str "Counter" ;;
   let: "s", "setS" := useState "x" in
   print: Str "Return" ;;
   ⟪ "s"; λ: "_", "setS" (λ: "s", "s" + 1) ⟫)%r
>>

    - Numerals are integer constants ([Number Notation]); [true] / [false]
      are boolean constants; [#()] is unit; [Str s] is a string constant.
    - A string literal is a *variable* (coercion [var_e]); [Comp C] names
      a component.
    - Application is juxtaposition, through a coercion of [expr] to
      [Funclass]: [f x y] is [EApp (EApp f x) y].
    - [e1 ;; e2], [λ: x, e], [let: x := e1 in e2], [if: e0 then e1 else e2],
      [let: x, xs := useState e1 in e2] (label 0; labels are ignored under
      cursor semantics — write [EUseState l …] to set one), [useEffect: e],
      [print: e], and the view [⟪ e1; …; en ⟫].
    - Operators [+ - * < ≤ = ¬] at Coq's usual levels.

    Notations are printing-only sugar over the constructors: terms are
    unchanged, so proofs about programs written either way coincide. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax.

(* Not Iris's [expr_scope] (key [%r]), which the [WP] notation applies to
   its expression argument: our numerals and keywords must not leak into
   machine expressions such as [TPath 0]. *)
Declare Scope react_scope.
Delimit Scope react_scope with r.
Bind Scope react_scope with expr.

(** Argument scopes of the constructors, so that labels, variables, and
    sub-expressions parse correctly inside [%r]. *)
Arguments EVar x%string_scope.
Arguments ECompName C%string_scope.
Arguments EFun x%string_scope e%r.
Arguments ELet x%string_scope e1%r e2%r.
Arguments EUseState l%nat_scope x%string_scope xset%string_scope e1%r e2%r.

(** ** Constants and variables *)
Definition expr_of_Z (n : Z) : expr := EConst (CInt n).
Definition Z_of_expr (e : expr) : option Z :=
  match e with EConst (CInt n) => Some n | _ => None end.
Number Notation expr expr_of_Z Z_of_expr : react_scope.

Definition var_e (x : string) : expr := EVar x.
Coercion var_e : string >-> expr.
Definition bool_e (b : bool) : expr := EConst (CBool b).
Coercion bool_e : bool >-> expr.

Notation "'Str' s" := (EConst (CString s%string)) (at level 1, s at level 0) : react_scope.
Notation "'Comp' C" := (ECompName C%string) (at level 1, C at level 0) : react_scope.
Notation "#()" := (EConst CUnit) : react_scope.

(** ** Application by juxtaposition *)
Coercion EApp : expr >-> Funclass.

(** ** Operators *)
Notation "e1 + e2" := (EBop BPlus e1%r e2%r) (at level 50, left associativity) : react_scope.
Notation "e1 - e2" := (EBop BMinus e1%r e2%r) (at level 50, left associativity) : react_scope.
Notation "e1 * e2" := (EBop BTimes e1%r e2%r) (at level 40, left associativity) : react_scope.
Notation "e1 < e2" := (EBop BLt e1%r e2%r) (at level 70) : react_scope.
Notation "e1 > e2" := (EBop BGt e1%r e2%r) (at level 70) : react_scope.
Notation "e1 ≤ e2" := (EBop BLe e1%r e2%r) (at level 70) : react_scope.
Notation "e1 ≥ e2" := (EBop BGe e1%r e2%r) (at level 70) : react_scope.
Notation "e1 = e2" := (EBop BEq e1%r e2%r) (at level 70) : react_scope.
Notation "e1 ≠ e2" := (EBop BNe e1%r e2%r) (at level 70) : react_scope.
Notation "e1 && e2" := (EBop BAnd e1%r e2%r) (at level 40, left associativity) : react_scope.
Notation "e1 || e2" := (EBop BOr e1%r e2%r) (at level 50, left associativity) : react_scope.
Notation "¬ e" := (EUop UNot e%r) (at level 75, right associativity) : react_scope.
Notation "- e" := (EUop UNeg e%r) (at level 35, right associativity) : react_scope.

(** ** Control, binders, hooks, views *)
Notation "e1 ;; e2" := (ESeq e1%r e2%r)
  (at level 100, e2 at level 200, right associativity,
   format "'[v' e1 ;;  '/' e2 ']'") : react_scope.
Notation "'λ:' x , e" := (EFun x%string e%r)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : react_scope.
Notation "'let:' x := e1 'in' e2" := (ELet x%string e1%r e2%r)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : react_scope.
Notation "'let:' x , xs := 'useState' e1 'in' e2" :=
  (EUseState 0 x%string xs%string e1%r e2%r)
  (at level 200, x, xs at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x ,  xs  :=  'useState'  '[' e1 ']'  'in'  '/' e2 ']'") : react_scope.
Notation "'if:' e0 'then' e1 'else' e2" := (EIf e0%r e1%r e2%r)
  (at level 200, e0, e1, e2 at level 200,
   format "'[hv' 'if:'  e0  '/' '[' 'then'  e1 ']'  '/' '[' 'else'  e2 ']' ']'") : react_scope.
Notation "'useEffect:' e" := (EUseEffect e%r) (at level 10, e at level 10) : react_scope.
Notation "'print:' e" := (EPrint e%r) (at level 10, e at level 10) : react_scope.
Notation "⟪ ⟫" := (EView nil) : react_scope.
Notation "⟪ e1 ; .. ; en ⟫" :=
  (EView (cons (e1%r : expr) .. (cons (en%r : expr) nil) ..)) : react_scope.

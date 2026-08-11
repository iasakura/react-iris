(** * Syntax of the React-tRace core calculus.

    Follows Fig. 1 and App. A.1 of "React-tRace: A Semantics for Understanding
    React Hooks" (Lee, Ahn, Yi; OOPSLA 2025), with two mild extensions aligned
    with the reference OCaml interpreter ([lib/domains/syntax.ml] in
    [vendor/react-trace]):

    - string constants (used pervasively by the test suite via [print]);
    - a concrete set of unary/binary primitive operators (comparisons return
      booleans, as in the interpreter, rather than the paper's ℤ×ℤ→ℤ family).

    Hooks carry static labels [ℓ] as in the paper; the top-level-only
    placement of hooks is captured by the [hook_free]/[body_ok] predicates
    below (the paper enforces it by parsing, the OCaml implementation by
    phantom types). *)
From react_iris Require Import prelude.

Definition var := string.
Definition comp_name := string.
Definition label := nat.

(** ** Constants *)
Inductive const :=
  | CUnit
  | CBool (b : bool)
  | CInt (n : Z)
  | CString (s : string).

(** ** Primitive operators *)
Inductive un_op := UNeg | UNot.

Inductive bin_op :=
  | BEq | BNe | BLt | BGt | BLe | BGe        (* comparisons (on integers) *)
  | BAnd | BOr                               (* booleans *)
  | BPlus | BMinus | BTimes | BDiv | BMod.   (* integer arithmetic *)

(** ** Expressions

    [EUseState ℓ x xset e1 e2] is the paper's
    [let (x, x_set) = useState^ℓ e1 in e2]. *)
Inductive expr :=
  | EConst (k : const)
  | EVar (x : var)
  | ECompName (C : comp_name)
  | EView (es : list expr)                   (* array view [ē] *)
  | EIf (e1 e2 e3 : expr)
  | EFun (x : var) (e : expr)
  | EApp (e1 e2 : expr)
  | ELet (x : var) (e1 e2 : expr)
  | ESeq (e1 e2 : expr)
  | EUseState (l : label) (x xset : var) (e1 e2 : expr)
  | EUseEffect (e : expr)
  | EUop (op : un_op) (e : expr)
  | EBop (op : bin_op) (e1 e2 : expr)
  | EPrint (e : expr).

(** ** Programs

    A program is a sequence of component definitions [let C x = e] plus a
    main expression. *)
Record comp_def := CompDef {
  cd_param : var;
  cd_body : expr;
}.

Definition def_table := gmap comp_name comp_def.

Record prog := Prog {
  p_defs : list (comp_name * comp_def);
  p_main : expr;
}.

Definition prog_def_table (P : prog) : def_table := list_to_map (p_defs P).

(** ** The hook discipline (Rules of Hooks, syntactic form)

    [hook_free e]: [e] contains no hook at all.
    [body_ok e]: hooks occur only along the top-level spine of [e]
    (through [let]-bodies, [seq], and hook continuations), as required for
    component bodies. This mirrors the [hook_free]/[hook_full] distinction
    of the OCaml implementation. *)
Fixpoint hook_free (e : expr) : bool :=
  match e with
  | EConst _ | EVar _ | ECompName _ => true
  | EView es => forallb hook_free es
  | EIf e1 e2 e3 => hook_free e1 && hook_free e2 && hook_free e3
  | EFun _ e => hook_free e
  | EApp e1 e2 => hook_free e1 && hook_free e2
  | ELet _ e1 e2 => hook_free e1 && hook_free e2
  | ESeq e1 e2 => hook_free e1 && hook_free e2
  | EUseState _ _ _ _ _ => false
  | EUseEffect _ => false
  | EUop _ e => hook_free e
  | EBop _ e1 e2 => hook_free e1 && hook_free e2
  | EPrint e => hook_free e
  end.

Fixpoint body_ok (e : expr) : bool :=
  match e with
  | ELet _ e1 e2 => hook_free e1 && body_ok e2
  | ESeq e1 e2 => body_ok e1 && body_ok e2
  | EUseState _ _ _ e1 e2 => hook_free e1 && body_ok e2
  | EUseEffect e => hook_free e
  | _ => hook_free e
  end.

(** Labels of the [useState] hooks along the spine of a component body.
    Validity (paper Def. 6) states that the state store of a mounted view is
    keyed exactly by this set. *)
Fixpoint body_labels (e : expr) : gset label :=
  match e with
  | ELet _ _ e2 => body_labels e2
  | ESeq e1 e2 => body_labels e1 ∪ body_labels e2
  | EUseState l _ _ _ e2 => {[l]} ∪ body_labels e2
  | _ => ∅
  end.

Definition comp_def_wf (d : comp_def) : bool := body_ok (cd_body d).

(** ** Decidable equality *)
Global Instance const_eq_dec : EqDecision const.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.

Global Instance expr_eq_dec : EqDecision expr.
Proof.
  (* The hole is sumbool-typed (not [Decision]) so that typeclass search
     cannot fill it with the unguarded [go] itself; [Hgo] then exposes the
     fix hypothesis to instance search for the nested [list expr] case. *)
  refine (fix go (e1 e2 : expr) : {e1 = e2} + {e1 ≠ e2} := _).
  assert (EqDecision expr) as Hgo by exact go.
  decide equality; apply (decide _).
Defined.

Global Instance comp_def_eq_dec : EqDecision comp_def.
Proof. solve_decision. Defined.

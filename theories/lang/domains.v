(** * Semantic objects of the React-tRace core calculus.

    Follows App. A.1 of the paper. The value type collapses the paper's
    [Val] ⊇ [ViewSpec] hierarchy into a single inductive with a
    well-formedness predicate [is_view_spec] carving out view specs.

    Environments are association lists ([list (var * val)]) rather than
    [gmap]s: nesting a value type recursively through [gmap] is not
    strictly positive in Rocq, and the paper's [σ = [x̄ ↦ v̄]] is a finite
    map that first-match association lists implement faithfully. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax.
From RecordUpdate Require Import RecordSet.

Definition path : Set := nat.

(** ** Values

    [VClos x e σ]     — closure ⟨λx.e, σ⟩
    [VCompSpec C v]   — component spec ⟨C, v⟩ (component applied to argument)
    [VList vs]        — array view spec [s̄] (also used for tuple-ish data)
    [VSetter ℓ p]     — setter closure ⟨ℓ, p⟩ *)
Inductive val :=
  | VConst (k : const)
  | VClos (x : var) (e : expr) (env : list (var * val))
  | VCompName (C : comp_name)
  | VCompSpec (C : comp_name) (arg : val)
  | VList (vs : list val)
  | VSetter (l : label) (p : path).

Notation env := (list (var * val)).

Definition env_lookup (x : var) : env → option val :=
  fix go (σ : env) :=
    match σ with
    | [] => None
    | (y, v) :: σ' => if decide (x = y) then Some v else go σ'
    end.

Definition env_insert (x : var) (v : val) (σ : env) : env := (x, v) :: σ.

Definition of_const (k : const) : val := VConst k.
Coercion of_const : const >-> val.

(** ** View specs (paper: [s ::= k | cl | cs | [s̄]]) *)
Inductive is_view_spec : val → Prop :=
  | VSConst k : is_view_spec (VConst k)
  | VSClos x e σ : is_view_spec (VClos x e σ)
  | VSCompSpec C v : is_view_spec (VCompSpec C v)
  | VSList vs : Forall is_view_spec vs → is_view_spec (VList vs).

(** ** Trees (paper: [t ::= k | cl | [t̄] | p]) *)
Inductive tree :=
  | TConst (k : const)
  | TClos (x : var) (e : expr) (σ : env)
  | TList (ts : list tree)
  | TPath (p : path).

(** ** Decisions (paper: [d ::= Check | Effect], views carry a subset) *)
Record decisions := Decisions {
  dec_check : bool;
  dec_effect : bool;
}.

Definition dec_empty : decisions := Decisions false false.
Definition dec_union (d1 d2 : decisions) : decisions :=
  Decisions (dec_check d1 || dec_check d2) (dec_effect d1 || dec_effect d2).

Definition dec_add_check (d : decisions) : decisions :=
  Decisions true (dec_effect d).
Definition dec_add_effect (d : decisions) : decisions :=
  Decisions (dec_check d) true.
Definition dec_rm_check (d : decisions) : decisions :=
  Decisions false (dec_effect d).
Definition dec_rm_effect (d : decisions) : decisions :=
  Decisions (dec_check d) false.

(** ** State stores (paper: [ρ ::= [ℓ ↦ {val: v, sttq: q}]])

    Queue entries and effect-queue entries are closure values; this is a
    representation invariant, not enforced by the type. *)
Record st_entry := StEntry {
  st_val : val;
  st_queue : list val;
}.

Definition stt_store : Type := gmap label st_entry.

(** ** Views and tree memory

    [π = {spec: ⟨C, v⟩, dec: d̄, sttst: ρ, effq: q, child: t}]

    The constructor is [MkView], not [View]: Iris exports a constructor
    [View] (of [iris.algebra.view]) that would shadow it in files importing
    Iris — and elaborating a wrongly-resolved [View] against an expected
    [domains.view] has been observed to make the unifier diverge (memory
    exhaustion), not merely fail. The type names [val]/[view] are likewise
    shadowed by Iris in the logic layer and are referred to as
    [domains.val] / [domains.view] there. *)
Record view := MkView {
  vw_comp : comp_name;
  vw_arg : val;
  vw_dec : decisions;
  vw_sttst : stt_store;
  vw_effq : list val;
  vw_child : tree;
}.

Definition tree_mem : Type := gmap path view.

(** ** Phases and modes *)
Inductive phase := PInit | PSucc | PNormal.

Inductive mode :=
  | MRendered   (* ❀: rendered, queued effects pending *)
  | MCheck      (* ↺: checking for re-render *)
  | MEvent.     (* •: event loop, waiting for user input *)

(** ** Evaluation contexts of the paper's big-step judgment
    (Σ ::= m | π — whole-memory vs. local-view context).

    We bundle the current path with the local-view context: in the paper the
    path is a subscript of the judgment, but it is only ever consulted
    together with a view context (STTBIND binds setters to it, APPSETCOMP
    compares against it), and Normal-phase evaluation has no path. *)
Inductive rctx :=
  | RCtxMem (m : tree_mem)
  | RCtxView (p : path) (π : view).

(** ** Output buffer (observations of [print]) *)
Definition out_buf : Set := list val.

(** ** Machine configurations (paper: ⟨t, m, ω, δ, μ⟩; the definition
    table δ is a parameter, not part of the configuration) *)
Record config := Config {
  c_tree : tree;
  c_mem : tree_mem;
  c_out : out_buf;
  c_mode : mode;
}.

(** ** Displays: the realized view hierarchy observed in quiescent states
    (constants and structure are visible; handlers are opaque) *)
Inductive dtree :=
  | DConst (k : const)
  | DHandler
  | DList (ds : list dtree).

(** ** Record updates *)
Global Instance st_entry_settable : Settable st_entry :=
  settable! StEntry <st_val; st_queue>.
Global Instance decisions_settable : Settable decisions :=
  settable! Decisions <dec_check; dec_effect>.
Global Instance view_settable : Settable view :=
  settable! MkView <vw_comp; vw_arg; vw_dec; vw_sttst; vw_effq; vw_child>.
Global Instance config_settable : Settable config :=
  settable! Config <c_tree; c_mem; c_out; c_mode>.

(** ** Decidable equality *)
Global Instance val_eq_dec : EqDecision val.
Proof.
  refine (fix go (v1 v2 : val) : {v1 = v2} + {v1 ≠ v2} := _).
  assert (EqDecision val) as Hgo by exact go.
  decide equality; apply (decide _).
Defined.

Global Instance tree_eq_dec : EqDecision tree.
Proof.
  refine (fix go (t1 t2 : tree) : {t1 = t2} + {t1 ≠ t2} := _).
  assert (EqDecision tree) as Hgo by exact go.
  decide equality; apply (decide _).
Defined.

Global Instance decisions_eq_dec : EqDecision decisions.
Proof. solve_decision. Defined.
Global Instance st_entry_eq_dec : EqDecision st_entry.
Proof. solve_decision. Defined.
Global Instance phase_eq_dec : EqDecision phase.
Proof. solve_decision. Defined.
Global Instance mode_eq_dec : EqDecision mode.
Proof. solve_decision. Defined.

Global Instance dtree_eq_dec : EqDecision dtree.
Proof.
  refine (fix go (d1 d2 : dtree) : {d1 = d2} + {d1 ≠ d2} := _).
  assert (EqDecision dtree) as Hgo by exact go.
  decide equality; apply (decide _).
Defined.

Global Instance view_eq_dec : EqDecision view.
Proof. solve_decision. Defined.
Global Instance config_eq_dec : EqDecision config.
Proof. solve_decision. Defined.

(** [useState]'s Succ-phase comparison [vₙ ≢ v₀] (STTREBIND) is decidable
    value equality; the reference interpreter compares values structurally. *)
Definition val_eqb (v1 v2 : val) : bool := bool_decide (v1 = v2).

(** * Iris language instance for the React-tRace machine.

    The machine configuration [mcfg] splits into
    - the language expression [lexpr] (focus + frame stack), and
    - the physical state [lstate] (tree memory, render register, output).

    Values are terminal foci with an empty stack: intermediate results
    ([FVal]/[FTree]/[FBool]/[FUnit]) as well as quiescence ([FIdle]).
    Making intermediate results values is what enables a bind rule
    ("run the focus down to a result, then resume the frames"), and hence
    modular specifications of sub-computations — a component body, a
    single runtime operation — rather than only whole-program runs.
    A full program still ends in [MIdle t] (event-loop mode •), so
    top-level WP postconditions speak about reaching quiescence, matching
    design decision D6.

    Steps are the graph of the deterministic [mstep]; a [Stuck] result of
    [mstep] is precisely irreducibility, so Iris safety ("not stuck")
    coincides with the absence of Rules-of-React violations. Event
    injection (STEPEVENT) is not a language step — values do not reduce —
    and is composed at the meta level, one event per WP. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From iris.program_logic Require Import language.

Definition lexpr : Type := focus * list frame.

Record lstate := LState {
  ls_mem : tree_mem;
  ls_reg : option (path * view);
  ls_out : out_buf;
}.

Definition cfg_expr (c : mcfg) : lexpr := (mc_focus c, mc_stack c).
Definition cfg_state (c : mcfg) : lstate :=
  LState (mc_mem c) (mc_reg c) (mc_out c).
Definition glue (e : lexpr) (σ : lstate) : mcfg :=
  MCfg e.1 e.2 (ls_mem σ) (ls_reg σ) (ls_out σ).

Lemma glue_split c : glue (cfg_expr c) (cfg_state c) = c.
Proof. by destruct c. Qed.
Lemma glue_expr e σ : cfg_expr (glue e σ) = e.
Proof. by destruct e. Qed.
Lemma glue_state e σ : cfg_state (glue e σ) = σ.
Proof. by destruct σ. Qed.

(** ** Machine values *)
Inductive mval :=
  | MRetV (v : domains.val)  (* an expression evaluated to a value
                                ([domains.val]; [language.val] shadows it) *)
  | MRetT (t : tree)    (* init/reconcile built a tree *)
  | MRetB (b : bool)    (* check reported whether a re-render happened *)
  | MRetU               (* commit finished *)
  | MIdle (t : tree).   (* quiescent: event-loop mode • *)

Definition lof_val (w : mval) : lexpr :=
  match w with
  | MRetV v => (FVal v, [])
  | MRetT t => (FTree t, [])
  | MRetB b => (FBool b, [])
  | MRetU => (FUnit, [])
  | MIdle t => (FIdle t, [])
  end.

Definition lto_val (e : lexpr) : option mval :=
  match e with
  | (FVal v, []) => Some (MRetV v)
  | (FTree t, []) => Some (MRetT t)
  | (FBool b, []) => Some (MRetB b)
  | (FUnit, []) => Some MRetU
  | (FIdle t, []) => Some (MIdle t)
  | _ => None
  end.

Lemma lto_val_idle c t :
  mcfg_value c = Some t → lto_val (cfg_expr c) = Some (MIdle t).
Proof.
  destruct c as [f ks ???]; destruct f, ks; try done.
  by intros [= ->].
Qed.

Section lang.
  Context (δ : def_table).

  Definition lprim_step (e1 : lexpr) (σ1 : lstate) (κ : list Empty_set)
      (e2 : lexpr) (σ2 : lstate) (efs : list lexpr) : Prop :=
    κ = [] ∧ efs = [] ∧ mstep δ (glue e1 σ1) = Ok (glue e2 σ2).

  (** A configuration that steps is not a value: terminal foci with an
      empty stack are exactly where [mstep] is [Stuck]. *)
  Lemma mstep_not_val c c' :
    mstep δ c = Ok c' → lto_val (cfg_expr c) = None.
  Proof. destruct c as [f ks ???]; destruct f, ks; try done; by intros ?. Qed.

  Lemma react_lang_mixin : LanguageMixin lof_val lto_val lprim_step.
  Proof.
    split.
    - by intros [].
    - intros [f ks] w. destruct f, ks; try done; by intros [= <-].
    - intros [f ks] σ κ e' σ' efs (_ & _ & Hstep).
      exact (mstep_not_val _ _ Hstep).
  Qed.

  Canonical Structure reactLang : language := Language react_lang_mixin.
End lang.

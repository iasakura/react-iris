(** * Iris language instance for the React-tRace machine.

    The machine configuration [mcfg] splits into
    - the language expression [lexpr] (focus + frame stack), and
    - the physical state [lstate] (tree memory, render register, output).

    Values are quiescent trees: [FIdle t] with an empty stack. WP
    postconditions therefore speak about reaching quiescence (event-loop
    mode •), matching the top-level theorem shape of design decision D6.

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

Definition lof_val (t : tree) : lexpr := (FIdle t, []).
Definition lto_val (e : lexpr) : option tree :=
  match e with (FIdle t, []) => Some t | _ => None end.

Lemma lto_val_cfg c : lto_val (cfg_expr c) = mcfg_value c.
Proof. by destruct c as [f ks ???]; destruct f, ks. Qed.

Section lang.
  Context (δ : def_table).

  Definition lprim_step (e1 : lexpr) (σ1 : lstate) (κ : list Empty_set)
      (e2 : lexpr) (σ2 : lstate) (efs : list lexpr) : Prop :=
    κ = [] ∧ efs = [] ∧ mstep δ (glue e1 σ1) = Ok (glue e2 σ2).

  Lemma react_lang_mixin : LanguageMixin lof_val lto_val lprim_step.
  Proof.
    split.
    - by intros t.
    - intros [f ks] t. destruct f; try done. destruct ks; try done.
      by intros [= ->].
    - intros [f ks] σ κ e' σ' efs (_ & _ & Hstep).
      (* only [FIdle] has [lto_val ≠ None], and [mstep] is [Stuck] on it,
         contradicting [Hstep] by discriminate *)
      by destruct f.
  Qed.

  Canonical Structure reactLang : language := Language react_lang_mixin.
End lang.

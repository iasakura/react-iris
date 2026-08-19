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
    design decision D7.

    Steps are the graph of the deterministic [mstep]; a [Stuck] result of
    [mstep] is precisely irreducibility, so Iris safety ("not stuck")
    coincides with the absence of Rules-of-React violations. User input
    is data: a [KEvents] frame carries the pending trace and quiescent
    foci dispatch against it, so a whole multi-event run is one
    execution; top-level theorems quantify over traces outside the
    logic. *)
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

Lemma glue_split (c : mcfg) : glue (cfg_expr c) (cfg_state c) = c.
Proof. by destruct c. Qed.
Lemma glue_expr (e : lexpr) (σ : lstate) : cfg_expr (glue e σ) = e.
Proof. by destruct e. Qed.
Lemma glue_state (e : lexpr) (σ : lstate) : cfg_state (glue e σ) = σ.
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

Lemma lto_val_idle (c : mcfg) (t : tree) :
  mcfg_value c = Some t → lto_val (cfg_expr c) = Some (MIdle t).
Proof.
  destruct c as [f ks ???]; destruct f, ks; try done.
  by intros [= ->].
Qed.

(** ** Frame-stack contexts

    Appending frames below the current stack is the machine's notion of
    an evaluation context: [fill K e] runs [e]'s focus down to a result
    and then resumes the frames [K]. *)
Definition fill (K : list frame) (e : lexpr) : lexpr := (e.1, e.2 ++ K).

Definition app_cfg (K : list frame) (c : mcfg) : mcfg :=
  MCfg (mc_focus c) (mc_stack c ++ K) (mc_mem c) (mc_reg c) (mc_out c).

Lemma app_cfg_glue (K : list frame) (e : lexpr) (σ : lstate) :
  glue (fill K e) σ = app_cfg K (glue e σ).
Proof. by destruct e. Qed.
Lemma app_cfg_expr (K : list frame) (c : mcfg) :
  cfg_expr (app_cfg K c) = fill K (cfg_expr c).
Proof. done. Qed.
Lemma app_cfg_state (K : list frame) (c : mcfg) :
  cfg_state (app_cfg K c) = cfg_state c.
Proof. done. Qed.

Lemma fill_lto_val (K : list frame) (e : lexpr) :
  lto_val e = None → lto_val (fill K e) = None.
Proof. destruct e as [f ks]; destruct f, ks; done. Qed.

Section lang.
  Context (δ : def_table).

  Definition lprim_step (e1 : lexpr) (σ1 : lstate) (κ : list Empty_set)
      (e2 : lexpr) (σ2 : lstate) (efs : list lexpr) : Prop :=
    κ = [] ∧ efs = [] ∧ mstep δ (glue e1 σ1) = Ok (glue e2 σ2).

  (** A configuration that steps is not a value: terminal foci with an
      empty stack are exactly where [mstep] is [Stuck]. *)
  Lemma mstep_not_val (c c' : mcfg) :
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

  (** [mstep] commutes with appending frames below a non-value: no step
      inspects the stack beyond its head, and a non-value never exposes
      the appended frames as the head. This single fact makes [fill K] a
      [LanguageCtx], from which Iris's generic [wp_bind] follows. *)
  Lemma mstep_app (K : list frame) (c : mcfg) :
    lto_val (cfg_expr c) = None →
    mstep δ (app_cfg K c) = app_cfg K <$> mstep δ c.
  Proof.
    destruct c as [f ks m r o]. intros Hnv.
    (* per case: reduce, split on matches, and split on the results of
       opaque helpers ([≫=] on view_enqueue / operators / handlers) *)
    destruct f, ks; try done; cbn;
      repeat first [ progress (simplify_eq/=)
                   | case_match
                   | destruct (view_enqueue _ _ _)
                   | destruct (un_op_eval _ _)
                   | destruct (bin_op_eval _ _ _)
                   | destruct (handlers_of _ _) ];
      done.
  Qed.

  Global Instance fill_ctx K : LanguageCtx (Λ := reactLang) (fill K).
  Proof.
    split.
    - intros e. apply fill_lto_val.
    - intros e1 σ1 κ e2 σ2 efs (-> & -> & Hstep).
      pose proof (mstep_not_val _ _ Hstep) as Hnv.
      rewrite glue_expr in Hnv.
      split_and!; [done..|].
      rewrite !app_cfg_glue.
      rewrite (mstep_app K (glue e1 σ1)); last by rewrite glue_expr.
      by rewrite Hstep.
    - intros e1' σ1 κ e2 σ2 efs Hnv (-> & -> & Hstep).
      rewrite app_cfg_glue in Hstep.
      rewrite (mstep_app K (glue e1' σ1)) in Hstep;
        last by rewrite glue_expr.
      destruct (mstep δ (glue e1' σ1)) as [c0| |] eqn:Hbase; [|done..].
      cbn in Hstep.
      assert (app_cfg K c0 = glue e2 σ2) as Hglue by congruence.
      exists (cfg_expr c0).
      assert (σ2 = cfg_state c0) as ->.
      { by rewrite -(glue_state e2 σ2) -Hglue app_cfg_state. }
      split.
      + by rewrite -(glue_expr e2 (cfg_state c0)) -Hglue app_cfg_expr.
      + split_and!; [done..|]. by rewrite glue_split.
  Qed.
End lang.

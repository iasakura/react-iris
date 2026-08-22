(** * Step rules by state footprint, and redex rules for the render phase.

    Layer between the base lifting ([wp_mstep_det]) and the hook
    specifications (M3):

    - state-footprint primitives — one lemma per kind of physical
      footprint a machine step can have: register only ([wp_reg_step]),
      memory read only ([wp_mem_read_step]), memory update + register
      ([wp_mem_write_step]), memory allocation + register
      ([wp_mem_alloc_step]). Together with [wp_pure_step] and [wp_print]
      (lifting.v) these cover every [mstep] case.

    - redex rules for the render phase — symbolic-execution rules for
      the hook and retry steps, with no side conditions left to clients
      (the [mstep] computations are discharged here once). These are the
      machine-level material from which the useState/useEffect
      specifications and the render-phase protocol will be built.

    [wp_usestate_demo] at the end shows the intended style: a component
    body fragment with a hook is executed symbolically, rule by rule. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section step_rules.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Implicit Types Φ : mval → iProp Σ.

  (** ** State-footprint primitives *)

  (** Steps that read and write only the render register. *)
  Lemma wp_reg_step (e e' : lexpr) (r r' : option (path * domains.view)) Φ :
    lto_val e = None →
    (∀ m ω, mstep δ (glue e (LState m r ω)) = Ok (glue e' (LState m r' ω))) →
    reg_token r -∗
    ▷ (reg_token r' -∗ WP (e' : expr (reactLang δ)) {{ Φ }}) -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He Hstep) "Hr Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "(Hm & Hrsi & Ho)".
    iDestruct (ghost_var_agree with "Hrsi Hr") as %<-.
    iMod (ghost_var_update_halves r' with "Hrsi Hr") as "[Hrsi Hr]".
    iModIntro.
    iExists (glue e' (LState (ls_mem σ) r' (ls_out σ))).
    iSplit.
    { iPureIntro. destruct σ. apply Hstep. }
    iNext. iModIntro. rewrite glue_expr glue_state /=. iFrame.
    by iApply "Hwp".
  Qed.

  (** Steps that only read the memory (dispatching on a stored view,
      computing a fresh path). *)
  Lemma wp_mem_read_step (e e' : lexpr) (m : tree_mem) Φ :
    lto_val e = None →
    (∀ r ω, mstep δ (glue e (LState m r ω)) = Ok (glue e' (LState m r ω))) →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗ WP (e' : expr (reactLang δ)) {{ Φ }}) -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He Hstep) "Hm Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "(Hmsi & Hr & Ho)".
    iDestruct (ghost_map_auth_agree with "Hmsi Hm") as %<-.
    iModIntro.
    iExists (glue e' σ).
    iSplit.
    { iPureIntro. destruct σ. apply Hstep. }
    iNext. iModIntro. rewrite glue_expr glue_state. iFrame.
    by iApply "Hwp".
  Qed.

  (** Steps that update one existing view and the register (write-backs,
      Normal-phase setters, commit bookkeeping). *)
  Lemma wp_mem_write_step (e e' : lexpr) (m : tree_mem) (p : path)
      (π0 π' : domains.view) (r r' : option (path * domains.view)) Φ :
    lto_val e = None →
    (∀ ω, mstep δ (glue e (LState m r ω))
          = Ok (glue e' (LState (<[p:=π']> m) r' ω))) →
    mem_auth_frag m -∗ view_ptsto p π0 -∗ reg_token r -∗
    ▷ (mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token r' -∗
       WP (e' : expr (reactLang δ)) {{ Φ }}) -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He Hstep) "Hm Hp Hr Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "(Hmsi & Hrsi & Ho)".
    iDestruct (ghost_map_auth_agree with "Hmsi Hm") as %<-.
    iDestruct (ghost_var_agree with "Hrsi Hr") as %<-.
    iDestruct (mem_auth_halves_join with "Hmsi Hm") as "Hm2".
    iMod (ghost_map_update π' with "Hm2 Hp") as "[Hm2 Hp]".
    iDestruct (mem_auth_halves_split with "Hm2") as "[Hmsi2 Hm]".
    iMod (ghost_var_update_halves r' with "Hrsi Hr") as "[Hrsi Hr]".
    iModIntro.
    iExists (glue e' (LState (<[p:=π']> (ls_mem σ)) r' (ls_out σ))).
    iSplit.
    { iPureIntro. destruct σ. apply Hstep. }
    iNext. iModIntro. rewrite glue_expr glue_state /=. iFrame.
    by iApply ("Hwp" with "Hmsi2 Hp Hrsi").
  Qed.

  (** Steps that mount a view at a fresh path and touch the register. *)
  Lemma wp_mem_alloc_step (e e' : lexpr) (m : tree_mem) (p : path)
      (π' : domains.view) (r r' : option (path * domains.view)) Φ :
    lto_val e = None →
    m !! p = None →
    (∀ ω, mstep δ (glue e (LState m r ω))
          = Ok (glue e' (LState (<[p:=π']> m) r' ω))) →
    mem_auth_frag m -∗ reg_token r -∗
    ▷ (mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token r' -∗
       WP (e' : expr (reactLang δ)) {{ Φ }}) -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He Hfresh Hstep) "Hm Hr Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "(Hmsi & Hrsi & Ho)".
    iDestruct (ghost_map_auth_agree with "Hmsi Hm") as %<-.
    iDestruct (ghost_var_agree with "Hrsi Hr") as %<-.
    iDestruct (mem_auth_halves_join with "Hmsi Hm") as "Hm2".
    iMod (ghost_map_insert p π' with "Hm2") as "[Hm2 Hp]"; first done.
    iDestruct (mem_auth_halves_split with "Hm2") as "[Hmsi2 Hm]".
    iMod (ghost_var_update_halves r' with "Hrsi Hr") as "[Hrsi Hr]".
    iModIntro.
    iExists (glue e' (LState (<[p:=π']> (ls_mem σ)) r' (ls_out σ))).
    iSplit.
    { iPureIntro. destruct σ. apply Hstep. }
    iNext. iModIntro. rewrite glue_expr glue_state /=. iFrame.
    by iApply ("Hwp" with "Hmsi2 Hp Hrsi").
  Qed.

  (** ** Redex rules for the render phase

      Notation: [π] is the view under construction (in the register);
      the rules mirror the paper's rules on the machine. *)

  (** Enter a component body: clear Check and the effect queue, reset the
      hook cursor, push the retry frame (Fig. 6, round entry). *)
  Lemma wp_body_enter (φ : phase) (p : path) (π : domains.view) (σb : env)
      (body : syntax.expr) (ks : list machine.frame)
      (r : option (path * domains.view)) Φ :
    reg_token r -∗
    ▷ (reg_token (Some (p, π <| vw_dec ::= dec_rm_check |>
                              <| vw_effq := [] |> <| vw_hook_cursor := 0 |>)) -∗
       WP ((FExpr φ σb body, KRetry σb body :: ks)
           : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FBody φ p π σb body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_reg_step; [done|by intros]. Qed.

  (** STTBIND, dispatch: evaluate the initial-value expression. (Cursor
      semantics: the syntactic label is ignored; the slot is the cursor
      when the value comes back.) *)
  Lemma wp_usestate_init (x xset : var) (e1 e2 : syntax.expr)
      (σb : env) (p : path) (π : domains.view) (ks : list machine.frame) Φ :
    reg_token (Some (p, π)) -∗
    ▷ (reg_token (Some (p, π)) -∗
       WP ((FExpr PInit σb e1, KUseState σb x xset e2 :: ks)
           : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit σb (EUseState x xset e1 e2), ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_reg_step; [done|by intros]. Qed.

  (** STTBIND, continuation: allocate the slot at the cursor, advance the
      cursor, bind the state variable and the setter. *)
  Lemma wp_usestate_bind (v : domains.val) (σb : env) (x xset : var)
      (e2 : syntax.expr) (p : path) (π : domains.view)
      (ks : list machine.frame) Φ :
    reg_token (Some (p, π)) -∗
    ▷ (reg_token (Some (p, π <| vw_sttst ::= insert (vw_hook_cursor π) (StEntry v []) |> <| vw_hook_cursor := S (vw_hook_cursor π) |>)) -∗
       WP ((FExpr PInit (env_insert xset (VSetter (vw_hook_cursor π) p) (env_insert x v σb)) e2,
            ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KUseState σb x xset e2 :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_reg_step; [done|by intros]. Qed.

  (** STTREBIND, empty queue: rebind the committed value of the slot at
      the cursor; the decision is unchanged. *)
  Lemma wp_usestate_succ_nil (x xset : var) (e1 e2 : syntax.expr)
      (σb : env) (p : path) (π : domains.view) (v0 : domains.val)
      (ks : list machine.frame) Φ :
    vw_sttst π !! vw_hook_cursor π = Some (StEntry v0 []) →
    reg_token (Some (p, π)) -∗
    ▷ (reg_token (Some (p, π <| vw_sttst ::= insert (vw_hook_cursor π) (StEntry v0 []) |>
                              <| vw_hook_cursor := S (vw_hook_cursor π) |>)) -∗
       WP ((FExpr PSucc (env_insert xset (VSetter (vw_hook_cursor π) p) (env_insert x v0 σb)) e2,
            ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc σb (EUseState x xset e1 e2), ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl). iApply wp_reg_step; first done.
    intros m ω. cbn. by rewrite Hl.
  Qed.

  (** STTREBIND, non-empty queue: apply the first queued updater to the
      committed value of the slot at the cursor. *)
  Lemma wp_usestate_succ_cons (x xset : var) (e1 e2 : syntax.expr)
      (σb : env) (p : path) (π : domains.view) (v0 : domains.val) (xi : var)
      (ei : syntax.expr) (σi : env) (q : list domains.val)
      (ks : list machine.frame) Φ :
    vw_sttst π !! vw_hook_cursor π = Some (StEntry v0 (VClos xi ei σi :: q)) →
    reg_token (Some (p, π)) -∗
    ▷ (reg_token (Some (p, π)) -∗
       WP ((FExpr PSucc (env_insert xi v0 σi) ei,
            KSttFold σb (vw_hook_cursor π) x xset e2 v0 q :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc σb (EUseState x xset e1 e2), ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl). iApply wp_reg_step; first done.
    intros m ω. cbn. by rewrite Hl.
  Qed.

  (** STTREBIND, fold exhausted: commit the folded value, add the Effect
      decision iff it changed, flush the queue, advance the cursor, bind. *)
  Lemma wp_sttfold_nil (v : domains.val) (σb : env) (l : label) (x xset : var)
      (e2 : syntax.expr) (v0 : domains.val) (p : path) (π : domains.view)
      (ks : list machine.frame) Φ :
    reg_token (Some (p, π)) -∗
    ▷ (reg_token (Some (p, π <| vw_dec := (if val_eqb v v0 then vw_dec π else dec_add_effect (vw_dec π)) |> <| vw_sttst ::= insert l (StEntry v []) |> <| vw_hook_cursor := S l |>)) -∗
       WP ((FExpr PSucc (env_insert xset (VSetter l p) (env_insert x v σb)) e2,
            ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KSttFold σb l x xset e2 v0 [] :: ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_reg_step; [done|by intros]. Qed.

  (** STTREBIND, next updater. *)
  Lemma wp_sttfold_cons (v : domains.val) (σb : env) (l : label)
      (x xset : var) (e2 : syntax.expr) (v0 : domains.val) (xi : var)
      (ei : syntax.expr) (σi : env) (q : list domains.val) (p : path)
      (π : domains.view) (ks : list machine.frame) Φ :
    reg_token (Some (p, π)) -∗
    ▷ (reg_token (Some (p, π)) -∗
       WP ((FExpr PSucc (env_insert xi v σi) ei,
            KSttFold σb l x xset e2 v0 q :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KSttFold σb l x xset e2 v0 (VClos xi ei σi :: q) :: ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_reg_step; [done|by intros]. Qed.

  (** EFF: register an effect thunk. *)
  Lemma wp_useeffect (φ : phase) (e' : syntax.expr) (σb : env) (p : path)
      (π : domains.view) (ks : list machine.frame) Φ :
    φ ≠ PNormal →
    reg_token (Some (p, π)) -∗
    ▷ (reg_token
         (Some (p, π <| vw_effq ::= (λ q, q ++ [VClos "_" e' σb]) |>)) -∗
       WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr φ σb (EUseEffect e'), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hφ). iApply wp_reg_step; first done.
    intros m ω. destruct φ; [done|done|contradiction].
  Qed.

  (** APPSETCOMP: calling the component's own setter during rendering
      queues the updater and turns on the Check decision. *)
  Lemma wp_setter_comp (φ : phase) (l : label) (p : path) (π : domains.view)
      (ent : st_entry) (xi : var) (ei : syntax.expr) (σi : env)
      (ks : list machine.frame) Φ :
    φ ≠ PNormal →
    vw_sttst π !! l = Some ent →
    reg_token (Some (p, π)) -∗
    ▷ (reg_token
         (Some (p, π <| vw_dec ::= dec_add_check |>
                     <| vw_sttst ::=
                          insert l (ent <| st_queue ::=
                                            (λ q, q ++ [VClos xi ei σi]) |>) |>)) -∗
       WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal (VClos xi ei σi), KAppR φ (VSetter l p) :: ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hφ Hl). iApply wp_reg_step; first done.
    intros m ω. destruct φ; [| |contradiction]; cbn.
    all: destruct (decide (p = p)) as [_|]; last congruence.
    all: rewrite /view_enqueue Hl; cbn; done.
  Qed.

  (** EVALONCE: the round left no Check decision and executed as many
      hooks as there are slots (Rules of Hooks) — the body settled. *)
  Lemma wp_retry_done (s : domains.val) (σb : env) (body : syntax.expr)
      (p : path) (π' : domains.view) (ks : list machine.frame) Φ :
    dec_check (vw_dec π') = false →
    vw_hook_cursor π' = map_size (vw_sttst π') →
    reg_token (Some (p, π')) -∗
    ▷ (reg_token (Some (p, π')) -∗
       WP ((FVal s, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal s, KRetry σb body :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hc Hcur). iApply wp_reg_step; first done.
    intros m ω. cbn. rewrite Hc.
    by destruct (decide (vw_hook_cursor π' = map_size (vw_sttst π'))).
  Qed.

  (** EVALMULT: the round turned Check back on — re-enter the body. *)
  Lemma wp_retry_again (s : domains.val) (σb : env) (body : syntax.expr)
      (p : path) (π' : domains.view) (ks : list machine.frame) Φ :
    dec_check (vw_dec π') = true →
    reg_token (Some (p, π')) -∗
    ▷ (reg_token (Some (p, π' <| vw_dec ::= dec_rm_check |>
                              <| vw_effq := [] |> <| vw_hook_cursor := 0 |>)) -∗
       WP ((FExpr PSucc σb body, KRetry σb body :: ks)
           : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal s, KRetry σb body :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hc). iApply wp_reg_step; first done.
    intros m ω. cbn. by rewrite Hc.
  Qed.

  (** ** Demo: symbolic execution of a body fragment with a hook

      [let (s, _) = useState⁰ x in [s]] in Init phase: the initial value
      is read from the environment, the slot is allocated, and the view
      spec [[v]] is produced — rule by rule, no computation of whole
      runs. *)
  Example wp_usestate_demo (p : path) (π : domains.view) (v : domains.val)
      (ks : list machine.frame) Φ :
    reg_token (Some (p, π)) -∗
    (reg_token (Some (p, π <| vw_sttst ::= insert (vw_hook_cursor π) (StEntry v []) |> <| vw_hook_cursor := S (vw_hook_cursor π) |>)) -∗
       WP ((FVal (VList [v]), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit [("x", v)]
           (EUseState "s" "setS" (EVar "x") (EView [EVar "s"])), ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hr Hwp".
    iApply (wp_usestate_init with "Hr"). iNext. iIntros "Hr".
    iApply (wp_pure_step _ _ (FVal v, KUseState [("x", v)] "s" "setS"
                              (EView [EVar "s"]) :: ks));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_usestate_bind with "Hr"). iNext. iIntros "Hr".
    set (σ' := env_insert "setS" (VSetter (vw_hook_cursor π) p)
                 (env_insert "s" v [("x", v)])).
    iApply (wp_pure_step _ _ (FExpr PInit σ' (EVar "s"),
                            KView PInit σ' [] [] :: ks));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_pure_step _ _ (FVal v, KView PInit σ' [] [] :: ks));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_pure_step _ _ (FVal (VList [v]), ks));
      [done|intros σ; reflexivity|]. iNext.
    by iApply "Hwp".
  Qed.
End step_rules.

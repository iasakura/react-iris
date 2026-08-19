(** * State interpretation and basic lifting for the React language.

    Resources (design decision D4):
    - [view_ptsto p π] — per-view points-to backed by a [ghost_map]
      (per-field / per-hook abstractions are layered on top in the hook
      logic, M3);
    - [mem_auth_frag m] — the client half of the memory authority, pinning
      the exact tree memory (the other half lives in the state
      interpretation);
    - [reg_token r] — exclusive token for the render register (the view
      currently being rendered); this is the resource the render-phase
      protocol will hand to a component body;
    - [out_frag ω] — the output buffer.

    [own_cfg c] bundles full ownership of a machine configuration;
    [wp_mrun_ok] ("WP by computation") transports a deterministic run to
    quiescence into a weakest precondition. Modular per-step lifting
    lemmas will complement it as the runtime lemmas are developed. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre lifting.
From iris.proofmode Require Import proofmode.

Class reactGS (Σ : gFunctors) := ReactGS {
  react_mem_inG :: ghost_mapG Σ path domains.view;
  react_reg_inG :: ghost_varG Σ (option (path * domains.view));
  react_out_inG :: ghost_varG Σ out_buf;
  (* logical values of hook slots (slot layer, slots.v); allocated per
     slot, so no fixed name *)
  react_slot_inG :: ghost_varG Σ domains.val;
  react_mem_name : gname;
  react_reg_name : gname;
  react_out_name : gname;
}.

Section resources.
  Context `{!reactGS Σ}.

  Definition view_ptsto (p : path) (π : domains.view) : iProp Σ :=
    p ↪[react_mem_name] π.

  Definition mem_auth_frag (m : tree_mem) : iProp Σ :=
    ghost_map_auth react_mem_name (1/2) m.

  Definition reg_token (r : option (path * domains.view)) : iProp Σ :=
    ghost_var react_reg_name (1/2) r.

  Definition out_frag (ω : out_buf) : iProp Σ :=
    ghost_var react_out_name (1/2) ω.

  Definition state_res (σ : lstate) : iProp Σ :=
    ghost_map_auth react_mem_name (1/2) (ls_mem σ) ∗
    ghost_var react_reg_name (1/2) (ls_reg σ) ∗
    ghost_var react_out_name (1/2) (ls_out σ).

  (** Full client-side ownership of a machine configuration. *)
  Definition own_cfg (c : mcfg) : iProp Σ :=
    mem_auth_frag (mc_mem c) ∗
    ([∗ map] p ↦ π ∈ mc_mem c, view_ptsto p π) ∗
    reg_token (mc_reg c) ∗
    out_frag (mc_out c).
End resources.

Section iris_instance.
  Context `{!invGS Σ, !reactGS Σ}.

  (* Defined transparently, field for field the instance that Iris's
     [wp_adequacy] constructs, so that WPs proved against it apply
     directly in the adequacy proof (conversion). *)
  Global Instance react_irisGS (δ : def_table) : irisGS (reactLang δ) Σ :=
    IrisG _ (λ σ _ _ _, state_res σ) (λ _, True%I) (λ _, 0%nat)
      (λ σ ns κs nt, fupd_intro ∅ (state_res σ)).
End iris_instance.

Section wp_run.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Lemma mem_auth_halves_join m :
    mem_auth_frag m -∗ mem_auth_frag m -∗
    ghost_map_auth react_mem_name 1 m.
  Proof.
    iIntros "H1 H2".
    pose proof (ghost_map_auth_fractional react_mem_name m) as Hfrac.
    iAssert (ghost_map_auth react_mem_name (1/2 + 1/2)%Qp m)
      with "[H1 H2]" as "H".
    { rewrite (Hfrac (1/2)%Qp (1/2)%Qp). iFrame. }
    by iEval (rewrite Qp.half_half) in "H".
  Qed.

  Lemma mem_auth_halves_split m :
    ghost_map_auth react_mem_name 1 m -∗
    mem_auth_frag m ∗ mem_auth_frag m.
  Proof.
    iIntros "H".
    pose proof (ghost_map_auth_fractional react_mem_name m) as Hfrac.
    by iEval (rewrite -Qp.half_half (Hfrac (1/2)%Qp (1/2)%Qp)) in "H".
  Qed.

  Local Lemma own_cfg_agree σ c :
    state_res σ -∗ own_cfg c -∗ ⌜σ = cfg_state c⌝.
  Proof.
    iIntros "(Hm & Hr & Ho) (Hm' & _ & Hr' & Ho')".
    iDestruct (ghost_map_auth_agree with "Hm Hm'") as %Hm.
    iDestruct (ghost_var_agree with "Hr Hr'") as %Hr.
    iDestruct (ghost_var_agree with "Ho Ho'") as %Ho.
    iPureIntro. destruct σ. rewrite /cfg_state. by f_equal.
  Qed.

  (** Wholesale replacement of the physical state: the client owns the
      exact memory (auth half + all fragments), so both can be rebuilt for
      an arbitrary successor configuration. *)
  Local Lemma own_cfg_update c c' :
    state_res (cfg_state c) -∗ own_cfg c ==∗
    state_res (cfg_state c') ∗ own_cfg c'.
  Proof.
    iIntros "(Hm & Hr & Ho) (Hm' & Hfr & Hr' & Ho')".
    iDestruct (mem_auth_halves_join with "Hm Hm'") as "Hm".
    iMod (ghost_map_delete_big with "Hm Hfr") as "Hm".
    iEval (rewrite map_difference_diag) in "Hm".
    iMod (ghost_map_insert_big (mc_mem c') with "Hm") as "[Hm Hfr]".
    { apply map_disjoint_empty_r. }
    iEval (rewrite map_union_empty) in "Hm".
    iDestruct (mem_auth_halves_split with "Hm") as "[Hm Hm']".
    iMod (ghost_var_update_halves (mc_reg c') with "Hr Hr'") as "[Hr Hr']".
    iMod (ghost_var_update_halves (mc_out c') with "Ho Ho'") as "[Ho Ho']".
    by iFrame.
  Qed.

  (** ** Primitive per-step lifting

      [wp_mstep_det] is the base rule for the deterministic machine: to
      prove a WP of a non-value, exhibit the successor configuration
      (under the current physical state, learned from [state_res]) and
      perform the ghost updates for the step. The step-kind rules below
      derive from it; runtime lemmas (M3) will build on these. *)
  Lemma wp_mstep_det (e : lexpr) (Φ : mval → iProp Σ) :
    lto_val e = None →
    (∀ σ, state_res σ ==∗
       ∃ c', ⌜mstep δ (glue e σ) = Ok c'⌝ ∗
             ▷ |==> (state_res (cfg_state c') ∗
                     WP (cfg_expr c' : expr (reactLang δ)) {{ Φ }})) -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He) "H".
    iApply wp_lift_step; first exact He.
    iIntros (σ1 ns κ κs nt) "Hsi".
    iMod ("H" $! σ1 with "Hsi") as (c' Hstep) "H".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { iPureIntro. exists [], (cfg_expr c'), (cfg_state c'), [].
      split_and!; [done..|]. by rewrite glue_split. }
    iIntros "!>" (e2 σ2 efs) "%Hp Hlc".
    destruct Hp as (-> & -> & Hp).
    rewrite Hstep in Hp.
    assert (glue e2 σ2 = c') as Hg by congruence.
    assert (e2 = cfg_expr c') as -> by (by rewrite -Hg glue_expr).
    assert (σ2 = cfg_state c') as -> by (by rewrite -Hg glue_state).
    iMod "Hclose" as "_". iMod "H" as "[Hsi Hwp]".
    iModIntro. iFrame "Hsi". by iSplitL.
  Qed.

  (** Steps that do not touch the physical state (the bulk of expression
      evaluation: dispatch, frame push/pop, β-reduction, arithmetic). The
      side condition is discharged by [reflexivity] at concrete redexes. *)
  Lemma wp_pure_step (e e' : lexpr) (Φ : mval → iProp Σ) :
    lto_val e = None →
    (∀ σ, mstep δ (glue e σ) = Ok (glue e' σ)) →
    ▷ WP (e' : expr (reactLang δ)) {{ Φ }} -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He Hstep) "Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "Hsi". iModIntro.
    iExists (glue e' σ). iSplit; first done.
    iNext. iModIntro. rewrite glue_expr glue_state. iFrame.
  Qed.

  (** Output steps: [print] appends the value to the buffer. *)
  Lemma wp_print (v : domains.val) (ks : list machine.frame) (ω : out_buf)
      (Φ : mval → iProp Σ) :
    out_frag ω -∗
    ▷ (out_frag (ω ++ [v]) -∗
       WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KPrint :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hout Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "(Hm & Hr & Ho)".
    iDestruct (ghost_var_agree with "Ho Hout") as %<-.
    iMod (ghost_var_update_halves (ls_out σ ++ [v]) with "Ho Hout")
      as "[Ho Hout]".
    iModIntro.
    iExists (MCfg (FVal (VConst CUnit)) ks (ls_mem σ) (ls_reg σ)
               (ls_out σ ++ [v])).
    iSplit; first done.
    iNext. iModIntro. iFrame "Hm Hr Ho".
    by iApply "Hwp".
  Qed.

  (** Sanity demo of the intended proof style: step-by-step symbolic
      execution of [print 1] via the primitive rules, ending in a value.
      The pure side conditions compute by [reflexivity]. *)
  Example wp_print_demo (ω : out_buf) (Φ : mval → iProp Σ) :
    out_frag ω -∗
    (out_frag (ω ++ [VConst (CInt 1)]) -∗ Φ (MRetV (VConst CUnit))) -∗
    WP ((FExpr PNormal [] (EPrint (EConst (CInt 1))), [])
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Ho HΦ".
    iApply (wp_pure_step _ (FExpr PNormal [] (EConst (CInt 1)), [KPrint]));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_pure_step _ (FVal (VConst (CInt 1)), [KPrint]));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    iApply (wp_value' _ _ _ (MRetV (VConst CUnit))). by iApply "HΦ".
  Qed.

  (** Bind: run the focus down to a result, then resume the frames.
      Direct specialization of Iris's generic [wp_bind] to the
      [LanguageCtx] instance of [fill] — the key to modular specs of
      sub-computations (component bodies, runtime operations). *)
  Lemma wp_fill (Ks : list machine.frame) (e : lexpr) (Φ : mval → iProp Σ) :
    WP (e : expr (reactLang δ))
      {{ w, WP (fill Ks (lof_val w) : expr (reactLang δ)) {{ Φ }} }} -∗
    WP (fill Ks e : expr (reactLang δ)) {{ Φ }}.
  Proof. iIntros "H". by iApply (wp_bind (fill Ks)). Qed.

  (** Deterministic execution to quiescence implies WP. *)
  Lemma wp_mrun_ok (n : nat) (c c' : mcfg) (Φ : mval → iProp Σ) :
    mrun δ n c = Ok c' →
    own_cfg c -∗
    (∀ t, ⌜mcfg_value c' = Some t⌝ -∗ own_cfg c' -∗ Φ (MIdle t)) -∗
    WP (cfg_expr c : expr (reactLang δ)) {{ Φ }}.
  Proof.
    revert c. induction n as [|n IH]; intros c Hrun; first done.
    simpl in Hrun.
    destruct (mcfg_value c) as [t|] eqn:Hval.
    - (* quiescent: a language value *)
      assert (c' = c) as ->.
      { unfold mret, res_mret in Hrun. by simplify_eq. }
      iIntros "Hown Hpost".
      assert (@to_val (reactLang δ) (cfg_expr c) = Some (MIdle t)) as Hv.
      { exact (lto_val_idle _ _ Hval). }
      apply of_to_val in Hv. rewrite -Hv.
      iApply wp_value'. by iApply ("Hpost" with "[//] Hown").
    - (* one deterministic step *)
      destruct (mstep δ c) as [c1|msg|] eqn:Hstep;
        unfold mbind, res_mbind in Hrun; [|done..].
      iIntros "Hown Hpost".
      iApply wp_lift_step.
      { exact (mstep_not_val _ _ _ Hstep). }
      iIntros (σ1 ns κ κs nt) "Hsi".
      iDestruct (own_cfg_agree with "Hsi Hown") as %->.
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
      iSplit.
      { iPureIntro. exists [], (cfg_expr c1), (cfg_state c1), [].
        split_and!; [done..|]. by rewrite !glue_split. }
      iIntros "!>" (e2 σ2 efs) "%Hpstep Hlc".
      destruct Hpstep as (-> & -> & Hpstep).
      rewrite glue_split Hstep in Hpstep.
      injection Hpstep as Hglue.
      assert (e2 = cfg_expr c1) as ->.
      { by rewrite Hglue glue_expr. }
      assert (σ2 = cfg_state c1) as ->.
      { by rewrite Hglue glue_state. }
      iMod (own_cfg_update c c1 with "Hsi Hown") as "[Hsi Hown]".
      iMod "Hclose" as "_". iModIntro.
      iFrame "Hsi". iSplitL; last done.
      by iApply (IH with "Hown Hpost").
  Qed.
End wp_run.

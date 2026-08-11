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

  Global Program Instance react_irisGS (δ : def_table)
      : irisGS (reactLang δ) Σ := {|
    iris_invGS := _;
    state_interp σ _ _ _ := state_res σ;
    fork_post _ := True%I;
    num_laters_per_step _ := 0%nat;
  |}.
  Next Obligation. intros. by iIntros "$". Qed.
End iris_instance.

Section wp_run.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Local Lemma mem_auth_halves_join m :
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

  Local Lemma mem_auth_halves_split m :
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

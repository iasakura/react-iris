(** * State interpretation and basic lifting for the React language.

    PROVISIONAL state interpretation: the whole physical state is held in
    a single exclusive ghost variable, with the standard halves split
    between the state interpretation and the client ([state_frag]). This
    validates the language plumbing end to end (see [examples/counter.v])
    and will be refined into the points-to family of design decision D4
    (per-view ghost map, render-register token, output resource) before
    the hook specifications are built.

    [wp_mrun_ok] is "WP by computation": a deterministic machine run that
    reaches quiescence yields a weakest precondition. It is the seed of
    the runtime lemmas — modular WP rules will replace it, but it already
    shows that safety and the final display can be transported through
    Iris for concrete programs. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import weakestpre lifting.
From iris.proofmode Require Import proofmode.

Class reactGS (Σ : gFunctors) := ReactGS {
  react_state_inG :: ghost_varG Σ lstate;
  react_state_name : gname;
}.

Section iris_instance.
  Context `{!invGS Σ, !reactGS Σ}.

  Definition state_frag (σ : lstate) : iProp Σ :=
    ghost_var react_state_name (1/2) σ.

  Global Program Instance react_irisGS (δ : def_table)
      : irisGS (reactLang δ) Σ := {|
    iris_invGS := _;
    state_interp σ _ _ _ := ghost_var react_state_name (1/2) σ;
    fork_post _ := True%I;
    num_laters_per_step _ := 0%nat;
  |}.
  Next Obligation. by iIntros (?????) "$". Qed.
End iris_instance.

Section wp_run.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  (** Deterministic execution to quiescence implies WP. *)
  Lemma wp_mrun_ok (n : nat) (c c' : mcfg) (Φ : tree → iProp Σ) :
    mrun δ n c = Ok c' →
    state_frag (cfg_state c) -∗
    (∀ t, ⌜mcfg_value c' = Some t⌝ -∗ state_frag (cfg_state c') -∗ Φ t) -∗
    WP (cfg_expr c : expr (reactLang δ)) {{ Φ }}.
  Proof.
    revert c. induction n as [|n IH]; intros c Hrun; first done.
    simpl in Hrun.
    destruct (mcfg_value c) as [t|] eqn:Hval.
    - (* quiescent: a language value *)
      assert (c' = c) as ->.
      { unfold mret, res_mret in Hrun. by simplify_eq. }
      iIntros "Hfrag Hpost".
      assert (@to_val (reactLang δ) (cfg_expr c) = Some t) as Hv.
      { exact (eq_trans (lto_val_cfg c) Hval). }
      apply of_to_val in Hv. rewrite -Hv.
      iApply wp_value'. by iApply ("Hpost" with "[//] Hfrag").
    - (* one deterministic step *)
      destruct (mstep δ c) as [c1|msg|] eqn:Hstep;
        unfold mbind, res_mbind in Hrun; [|done..].
      iIntros "Hfrag Hpost".
      iApply wp_lift_step.
      { exact (eq_trans (lto_val_cfg c) Hval). }
      iIntros (σ1 ns κ κs nt) "Hsi".
      iDestruct (ghost_var_agree with "Hsi Hfrag") as %->.
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
      iMod (ghost_var_update_halves (cfg_state c1) with "Hsi Hfrag")
        as "[Hsi Hfrag]".
      iMod "Hclose" as "_". iModIntro.
      iFrame "Hsi". iSplitL; last done.
      by iApply (IH with "Hfrag Hpost").
  Qed.
End wp_run.

(** * Redex rules for the runtime operations (init / reconcile / check /
    commit).

    Completes the rule coverage of the machine begun in [step_rules.v]:
    every state-touching dispatch or return step of the runtime
    operations gets a rule with no side conditions left to clients (pure
    dispatches — constants, lists, frame bookkeeping — are handled by the
    generic [wp_pure_step]). With these, a whole render/commit/check
    cycle can be executed symbolically, which is what the runtime lemmas
    of M3 will package.

    Two more footprint primitives are added: [wp_mem_only_write_step]
    (memory update, register untouched) and the [mem_lookup] helper
    deriving the pure lookup fact clients need to instantiate rules. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section runtime_rules.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Implicit Types Φ : mval → iProp Σ.

  (** The pure lookup fact behind a points-to, for instantiating rules. *)
  Lemma mem_lookup (m : tree_mem) (p : path) (π : domains.view) :
    mem_auth_frag m -∗ view_ptsto p π -∗ ⌜m !! p = Some π⌝.
  Proof. iIntros "Hm Hp". by iApply (ghost_map_lookup with "Hm Hp"). Qed.

  (** Memory update with the register untouched. *)
  Lemma wp_mem_only_write_step (e e' : lexpr) (m : tree_mem) (p : path)
      (π0 π' : domains.view) Φ :
    lto_val e = None →
    (∀ r ω, mstep δ (glue e (LState m r ω))
            = Ok (glue e' (LState (<[p:=π']> m) r ω))) →
    mem_auth_frag m -∗ view_ptsto p π0 -∗
    ▷ (mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗
       WP (e' : expr (reactLang δ)) {{ Φ }}) -∗
    WP (e : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He Hstep) "Hm Hp Hwp".
    iApply wp_mstep_det; first done.
    iIntros (σ) "(Hmsi & Hrsi & Ho)".
    iDestruct (ghost_map_auth_agree with "Hmsi Hm") as %<-.
    iDestruct (mem_auth_halves_join with "Hmsi Hm") as "Hm2".
    iMod (ghost_map_update π' with "Hm2 Hp") as "[Hm2 Hp]".
    iDestruct (mem_auth_halves_split with "Hm2") as "[Hmsi2 Hm]".
    iModIntro.
    iExists (glue e' (LState (<[p:=π']> (ls_mem σ)) (ls_reg σ) (ls_out σ))).
    iSplit.
    { iPureIntro. destruct σ. apply Hstep. }
    iNext. iModIntro. rewrite glue_expr glue_state /=. iFrame.
    by iApply ("Hwp" with "Hmsi2 Hp").
  Qed.

  (** ** Init (Fig. 7) *)

  (** INITCOM, dispatch: allocate a fresh path and enter the body. *)
  Lemma wp_init_comp (C : comp_name) (v : domains.val) (x : var)
      (body : syntax.expr) (m : tree_mem) (ks : list machine.frame) Φ :
    δ !! C = Some (CompDef x body) →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FBody PInit (fresh_path m)
              (MkView C v dec_empty ∅ [] (TConst CUnit)) [(x, v)] body,
            KInitBody (fresh_path m) :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FInit (VCompSpec C v), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (HC). iApply wp_mem_read_step; first done.
    intros r ω. cbn. by rewrite HC.
  Qed.

  (** INITCOM, body settled: mount the view, initialize the child spec. *)
  Lemma wp_mount (s : domains.val) (p : path) (π : domains.view)
      (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = None →
    mem_auth_frag m -∗ reg_token (Some (p, π)) -∗
    ▷ (mem_auth_frag (<[p:=π]> m) -∗ view_ptsto p π -∗ reg_token None -∗
       WP ((FInit s, KInitChild p :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal s, KInitBody p :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hfresh). iApply wp_mem_alloc_step; [done|done|].
    intros ω. cbn. by destruct (decide (p = p)); [|congruence].
  Qed.

  (** INITCOM, child initialized: set the Effect decision and the child. *)
  Lemma wp_init_finish (t : tree) (p : path) (π : domains.view)
      (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = Some π →
    mem_auth_frag m -∗ view_ptsto p π -∗
    ▷ (mem_auth_frag
         (<[p := π <| vw_dec := Decisions false true |>
                    <| vw_child := t |>]> m) -∗
       view_ptsto p (π <| vw_dec := Decisions false true |>
                       <| vw_child := t |>) -∗
       WP ((FTree (TPath p), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FTree t, KInitChild p :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp). iApply wp_mem_only_write_step; first done.
    intros r ω. cbn. by rewrite Hp.
  Qed.

  (** ** Reconcile (Fig. 10) *)

  (** RECONCILECOMEFFECT, dispatch: same component name — re-enter the
      body with the new argument. *)
  Lemma wp_recon_comp_same (p : path) (π : domains.view) (C : comp_name)
      (v : domains.val) (x : var) (body : syntax.expr) (m : tree_mem)
      (ks : list machine.frame) Φ :
    m !! p = Some π →
    vw_comp π = C →
    δ !! C = Some (CompDef x body) →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FBody PSucc p (π <| vw_arg := v |>) [(x, v)] body,
            KReconBody p (vw_child π) :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FRecon (TPath p) (VCompSpec C v), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp HC Hδ). iApply wp_mem_read_step; first done.
    intros r ω. cbn. rewrite Hp.
    destruct (decide (vw_comp π = C)); last congruence.
    by rewrite Hδ.
  Qed.

  (** RECONCILECOMNEW, dispatch: different component name — reinit. *)
  Lemma wp_recon_comp_new (p : path) (π : domains.view) (C : comp_name)
      (v : domains.val) (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = Some π →
    vw_comp π ≠ C →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FInit (VCompSpec C v), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FRecon (TPath p) (VCompSpec C v), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp HC). iApply wp_mem_read_step; first done.
    intros r ω. cbn. rewrite Hp.
    by destruct (decide (vw_comp π = C)); [congruence|].
  Qed.

  (** RECONCILECOMEFFECT, body settled: write back, reconcile the old
      child against the new view spec. *)
  Lemma wp_recon_writeback (s' : domains.val) (child : tree) (p : path)
      (π0 π' : domains.view) (m : tree_mem) (ks : list machine.frame) Φ :
    mem_auth_frag m -∗ view_ptsto p π0 -∗ reg_token (Some (p, π')) -∗
    ▷ (mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
       WP ((FRecon child s', KReconChild p :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal s', KReconBody p child :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iApply wp_mem_write_step; first done.
    intros ω. cbn. by destruct (decide (p = p)); [|congruence].
  Qed.

  (** RECONCILECOMEFFECT, child reconciled: set Effect and the child. *)
  Lemma wp_recon_finish (t' : tree) (p : path) (π : domains.view)
      (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = Some π →
    mem_auth_frag m -∗ view_ptsto p π -∗
    ▷ (mem_auth_frag
         (<[p := π <| vw_dec := Decisions false true |>
                    <| vw_child := t' |>]> m) -∗
       view_ptsto p (π <| vw_dec := Decisions false true |>
                       <| vw_child := t' |>) -∗
       WP ((FTree (TPath p), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FTree t', KReconChild p :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp). iApply wp_mem_only_write_step; first done.
    intros r ω. cbn. by rewrite Hp.
  Qed.

  (** ** Check (Fig. 9) *)

  (** CHECKIDLE: no Check decision — recurse into the child. *)
  Lemma wp_check_idle (p : path) (π : domains.view) (m : tree_mem)
      (ks : list machine.frame) Φ :
    m !! p = Some π →
    dec_check (vw_dec π) = false →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FCheck (vw_child π), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FCheck (TPath p), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hc). iApply wp_mem_read_step; first done.
    intros r ω. cbn. by rewrite Hp Hc.
  Qed.

  (** CHECK*, dispatch: Check is on — re-evaluate the body. *)
  Lemma wp_check_enter (p : path) (π : domains.view) (x : var)
      (body : syntax.expr) (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = Some π →
    dec_check (vw_dec π) = true →
    δ !! vw_comp π = Some (CompDef x body) →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FBody PSucc p π [(x, vw_arg π)] body,
            KCheckBody p (vw_child π) :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FCheck (TPath p), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hc Hδ). iApply wp_mem_read_step; first done.
    intros r ω. cbn. by rewrite Hp Hc Hδ.
  Qed.

  (** CHECKEFFECT: the re-evaluation decided to run Effects — write back
      and reconcile the old child against the new view spec. *)
  Lemma wp_check_writeback_eff (s' : domains.val) (child : tree) (p : path)
      (π0 π' : domains.view) (m : tree_mem) (ks : list machine.frame) Φ :
    dec_effect (vw_dec π') = true →
    mem_auth_frag m -∗ view_ptsto p π0 -∗ reg_token (Some (p, π')) -∗
    ▷ (mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
       WP ((FRecon child s', KCheckRecon p :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal s', KCheckBody p child :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He). iApply wp_mem_write_step; first done.
    intros ω. cbn.
    destruct (decide (p = p)); [|congruence]. by rewrite He.
  Qed.

  (** CHECKNOEFFECT: settled with the same state — write back, keep the
      old child, and keep checking below. *)
  Lemma wp_check_writeback_noeff (s' : domains.val) (child : tree)
      (p : path) (π0 π' : domains.view) (m : tree_mem)
      (ks : list machine.frame) Φ :
    dec_effect (vw_dec π') = false →
    mem_auth_frag m -∗ view_ptsto p π0 -∗ reg_token (Some (p, π')) -∗
    ▷ (mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
       WP ((FCheck child, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal s', KCheckBody p child :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (He). iApply wp_mem_write_step; first done.
    intros ω. cbn.
    destruct (decide (p = p)); [|congruence]. by rewrite He.
  Qed.

  (** CHECKEFFECT, child reconciled: install it and report a re-render. *)
  Lemma wp_check_finish (t' : tree) (p : path) (π : domains.view)
      (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = Some π →
    mem_auth_frag m -∗ view_ptsto p π -∗
    ▷ (mem_auth_frag (<[p := π <| vw_child := t' |>]> m) -∗
       view_ptsto p (π <| vw_child := t' |>) -∗
       WP ((FBool true, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FTree t', KCheckRecon p :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp). iApply wp_mem_only_write_step; first done.
    intros r ω. cbn. by rewrite Hp.
  Qed.

  (** ** Commit (Fig. 8) *)

  (** COMMITEFFSPATHIDLE: no Effect decision — only the child. *)
  Lemma wp_commit_idle (p : path) (π : domains.view) (m : tree_mem)
      (ks : list machine.frame) Φ :
    m !! p = Some π →
    dec_effect (vw_dec π) = false →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FCommit (vw_child π), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FCommit (TPath p), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp He). iApply wp_mem_read_step; first done.
    intros r ω. cbn. by rewrite Hp He.
  Qed.

  (** COMMITEFFSPATH, dispatch: commit the child first, then this
      view's queue. *)
  Lemma wp_commit_enter (p : path) (π : domains.view) (m : tree_mem)
      (ks : list machine.frame) Φ :
    m !! p = Some π →
    dec_effect (vw_dec π) = true →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FCommit (vw_child π), KCommitEffs p (vw_effq π) :: ks)
           : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FCommit (TPath p), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp He). iApply wp_mem_read_step; first done.
    intros r ω. cbn. by rewrite Hp He.
  Qed.

  (** COMMITEFFSPATH, queue exhausted: clear the Effect decision.
      Two entry points, matching the two return foci ([FUnit] after the
      child commit with an empty queue; [FVal] after the last effect). *)
  Lemma wp_commit_finish_u (p : path) (π : domains.view) (m : tree_mem)
      (ks : list machine.frame) Φ :
    m !! p = Some π →
    mem_auth_frag m -∗ view_ptsto p π -∗
    ▷ (mem_auth_frag (<[p := π <| vw_dec ::= dec_rm_effect |>]> m) -∗
       view_ptsto p (π <| vw_dec ::= dec_rm_effect |>) -∗
       WP ((FUnit, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FUnit, KCommitEffs p [] :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp). iApply wp_mem_only_write_step; first done.
    intros r ω. cbn. by rewrite Hp.
  Qed.

  Lemma wp_commit_finish_v (v : domains.val) (p : path) (π : domains.view)
      (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p = Some π →
    mem_auth_frag m -∗ view_ptsto p π -∗
    ▷ (mem_auth_frag (<[p := π <| vw_dec ::= dec_rm_effect |>]> m) -∗
       view_ptsto p (π <| vw_dec ::= dec_rm_effect |>) -∗
       WP ((FUnit, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KCommitEffs p [] :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp). iApply wp_mem_only_write_step; first done.
    intros r ω. cbn. by rewrite Hp.
  Qed.

  (** ** Demo: mounting a unit component, rule by rule

      [init ⟨C, v⟩] for [let C x = ()]: fresh path, body evaluation
      (one pure step), retry settles, mount, child init, finish — the
      client ends with the points-to of the mounted view. *)
  Example wp_mount_demo (C : comp_name) (v : domains.val) (m : tree_mem)
      (ks : list machine.frame) Φ :
    δ !! C = Some (CompDef "x" (EConst CUnit)) →
    mem_auth_frag m -∗ reg_token None -∗
    (∀ p, mem_auth_frag
             (<[p := MkView C v (Decisions false true) ∅ [] (TConst CUnit)]> m) -∗
          view_ptsto p (MkView C v (Decisions false true) ∅ [] (TConst CUnit)) -∗
          reg_token None -∗
          WP ((FTree (TPath p), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FInit (VCompSpec C v), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (HC) "Hm Hr Hwp".
    iApply (wp_init_comp with "Hm"); first done. iNext. iIntros "Hm".
    iApply (wp_body_enter with "Hr"). iNext. iIntros "Hr".
    iApply (wp_pure_step _ _ (FVal (VConst CUnit),
                              KRetry [("x", v)] (EConst CUnit)
                                :: KInitBody (fresh_path m) :: ks));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_retry_done with "Hr"); first done. iNext. iIntros "Hr".
    iApply (wp_mount with "Hm Hr"); first apply fresh_path_fresh.
    iNext. iIntros "Hm Hp Hr".
    iApply (wp_pure_step _ _ (FTree (TConst CUnit), KInitChild (fresh_path m) :: ks));
      [done|intros σ; reflexivity|]. iNext.
    iApply (wp_init_finish with "Hm Hp").
    { by rewrite lookup_insert_eq. }
    iNext. iIntros "Hm Hp".
    (* collapse the double insert and normalize the record updates *)
    iEval (rewrite insert_insert_eq; cbn) in "Hm". iEval (cbn) in "Hp".
    by iApply ("Hwp" with "Hm Hp Hr").
  Qed.
End runtime_rules.

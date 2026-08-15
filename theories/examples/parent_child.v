(** * Parent / Child (§3.2): a child's effect updates the parent's state,
    the parent re-renders and drops the child.

<<
let Child setS = useEffect (setS (fun _ -> false)); ();;
let Parent b = let (s, setS) = useState b in if s then Child setS else ();;
Parent true
>>

    Two components, nested initialization, an inter-component setter call
    from an effect (Normal phase, on the *parent's* view), and a
    reconciliation that replaces the child subtree by a constant. Shows
    how the runtime lemmas compose across components: the parent's
    initialization continuation runs the child's [wp_init_component]; the
    child's effect specification carries the parent's view resource in
    the [wp_commit_effects] chain; the parent's re-render is a
    [wp_check_component] whose body spec is stated on the parent alone.
    The dropped child's view stays in memory (paths are never
    deallocated), invisible to the display. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine tests.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime adequacy.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section parent_child.
  Context `{!invGS Σ, !reactGS Σ}.

  Local Definition δ : def_table := prog_def_table eff_cross_prog.
  Local Notation vbool b := (VConst (CBool b)).

  (** The child's effect thunk (captures the parent's setter) and the
      updater it queues. *)
  Local Definition eff (p : path) : domains.val :=
    VClos "_" (EApp (EVar "set") (EFun "_" (EConst (CBool false)))) [("set", VSetter 0 p)].
  Local Definition to_false (p : path) : domains.val :=
    VClos "_" (EConst (CBool false)) [("set", VSetter 0 p)].
  Local Definition is_bool (v : domains.val) : Prop := ∃ b, v = vbool b.

  Lemma upd_pure_to_false p :
    ⊢ upd_pure δ is_bool (to_false p) (λ _, vbool false).
  Proof.
    iIntros "!>" (v ks Φ _) "Hwp". wp_pure. by iApply "Hwp".
  Qed.

  (** ** Body specifications *)

  (** Parent, Init: allocates slot 0 at [true] and returns the child spec
      ⟨Child, setB⟩. *)
  Lemma parent_init p π ks Φ :
    render_ctx p π -∗
    (render_ctx p (π <| vw_sttst ::= <[0 := StEntry (vbool true) []]> |>) -∗
     WP ((FVal (VCompSpec "EffChild" (VSetter 0 p)), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit [("x", VConst CUnit)] eff_parent_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hr Hwp". rewrite /eff_parent_body.
    iApply (wp_usestate_init with "Hr"). iNext. iIntros "Hr".
    wp_pure.
    iApply (wp_usestate_mount with "Hr"). iNext. iIntros "Hr".
    do 8 wp_pure.
    by iApply "Hwp".
  Qed.

  (** Parent, Succ, with the child's update queued: folds to [false]
      (Effect), renders (). *)
  Lemma parent_succ p π ks Φ :
    vw_sttst π !! 0 = Some (StEntry (vbool true) [to_false p]) →
    render_ctx p π -∗
    (render_ctx p (π <| vw_dec ::= dec_add_effect |>
                     <| vw_sttst ::= <[0 := StEntry (vbool false) []]> |>) -∗
     WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc [("x", VConst CUnit)] eff_parent_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl) "Hr Hwp". rewrite /eff_parent_body.
    iApply (wp_usestate_succ_pure _ is_bool _ _ _ _ _ _ _ _ _ [to_false p]
              [λ _, vbool false] with "[] Hr").
    { done. }
    { by exists true. }
    { iSplit.
      - iPureIntro. constructor; last constructor. intros v _. by exists false.
      - iSplitL; last done. iApply upd_pure_to_false. }
    iIntros "Hr". cbn [fold_upd].
    iEval (rewrite /commit_slot /val_eqb bool_decide_eq_false_2; last done) in "Hr".
    do 4 wp_pure.
    by iApply "Hwp".
  Qed.

  (** Child (at path [pc]), Init: registers the effect (which captures
      the parent's setter at [pp]) and renders (). *)
  Lemma child_init pc pp π ks Φ :
    render_ctx pc π -∗
    (render_ctx pc (π <| vw_effq ::= (λ q, q ++ [eff pp]) |>) -∗
     WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit [("set", VSetter 0 pp)] eff_child_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hr Hwp". rewrite /eff_child_body.
    wp_pure.
    iApply (wp_useeffect with "Hr"); first done. iNext. iIntros "Hr".
    do 2 wp_pure.
    by iApply "Hwp".
  Qed.

  (** The child's effect: calls the parent's setter (path [p]) with
      [λ_. false] — queued on the parent's slot 0, Check on. *)
  Lemma child_effect p π ent m ks Φ :
    m !! p = Some π →
    vw_sttst π !! 0 = Some ent →
    mem_auth_frag m -∗ view_ptsto p π -∗ reg_token None -∗
    (let π' := π <| vw_dec ::= dec_add_check |>
                 <| vw_sttst ::= insert 0 (ent <| st_queue ::= (λ q, q ++ [to_false p]) |>) |> in
     mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
     WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PNormal [("set", VSetter 0 p)]
           (EApp (EVar "set") (EFun "_" (EConst (CBool false)))), ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hl) "Hm Hv Hr Hwp".
    do 4 wp_pure.
    iApply (wp_setter_normal with "Hm Hv Hr"); [done|done|].
    iNext. iIntros "Hm Hv Hr". by iApply ("Hwp" with "Hm Hv Hr").
  Qed.

  (** ** The run *)

  (** Views along the run (paths 0 = Parent, 1 = Child). *)
  Local Definition Πp1 : domains.view :=
    enter_view (MkView "Parent" (VConst CUnit) dec_empty ∅ [] (TConst CUnit))
      <| vw_sttst ::= <[0 := StEntry (vbool true) []]> |>.
  Local Definition Πc1 : domains.view :=
    enter_view (MkView "EffChild" (VSetter 0 0) dec_empty ∅ [] (TConst CUnit))
      <| vw_effq ::= (λ q, q ++ [eff 0]) |>.
  Local Definition Πc2 : domains.view :=
    Πc1 <| vw_dec := Decisions false true |> <| vw_child := TConst CUnit |>.
  Local Definition Πp2 : domains.view :=
    Πp1 <| vw_dec := Decisions false true |> <| vw_child := TPath 1 |>.

  Lemma parent_child_wp :
    own_cfg (machine_init_cfg eff_cross_prog []) -∗
    WP (cfg_expr (machine_init_cfg eff_cross_prog []) : expr (reactLang δ)) {{ w,
      ∃ m ω, mem_auth_frag m ∗ out_frag ω ∗
        ⌜∃ t, w = MIdle t ∧ display_t 1000 m t = Ok (DConst CUnit) ∧ ω = []⌝ }}.
  Proof.
    iIntros "(Hm & _ & Hr & Ho)".
    iEval (rewrite /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main eff_cross_prog])
      in "Hm Hr Ho".
    iEval (rewrite /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main eff_cross_prog]).
    do 6 wp_pure.
    (* --- mount Parent; its child spec is ⟨Child, setB⟩ --- *)
    iApply (wp_init_component _ _ _ _ _ _
              (λ π' s, (⌜π' = Πp1⌝ ∗
                        ⌜s = VCompSpec "EffChild" (VSetter 0 (fresh_path ∅))⌝)%I)
              with "[] Hm Hr").
    { done. }
    { iIntros (ks Φ') "Hr Hk'".
      iApply (parent_init with "Hr"). iIntros "Hr".
      iApply ("Hk'" $! (VCompSpec "EffChild" (VSetter 0 (fresh_path ∅))) Πp1
                with "[//] Hr"). by iSplit. }
    iIntros (s π' _) "Hm Hp Hr (-> & ->)".
    iEval (change (fresh_path ∅) with 0%nat) in "Hm Hp".
    iEval (change (fresh_path ∅) with 0%nat).
    (* --- mount Child at the fresh path 1, inside Parent's continuation --- *)
    iApply (wp_init_component _ _ _ _ _ _
              (λ π' s, (⌜π' = Πc1⌝ ∗ ⌜s = VConst CUnit⌝)%I) with "[] Hm Hr").
    { done. }
    { iIntros (ks Φ') "Hr Hk'".
      iEval (change (fresh_path (<[0:=Πp1]> ∅)) with 1%nat) in "Hr".
      iApply (child_init 1 0 with "Hr"). iIntros "Hr".
      iApply ("Hk'" $! (VConst CUnit) Πc1 with "[//] [Hr]"); last by iSplit.
      by iEval (change (fresh_path (<[0:=Πp1]> ∅)) with 1%nat). }
    iIntros (s π' _) "Hm Hc Hr (-> & ->)".
    iEval (change (fresh_path (<[0:=Πp1]> ∅)) with 1%nat) in "Hm Hc".
    iEval (change (fresh_path (<[0:=Πp1]> ∅)) with 1%nat).
    wp_pure.
    iApply (wp_init_finish with "Hm Hc"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hc".
    iEval (rewrite insert_insert_eq) in "Hm".
    iApply (wp_init_finish with "Hm Hp").
    { by rewrite lookup_insert_ne // lookup_insert_eq. }
    iNext. iIntros "Hm Hp".
    iEval (rewrite (insert_insert_ne _ 0%nat 1%nat) // insert_insert_eq) in "Hm".
    (* memory: {0 ↦ Πp2, 1 ↦ Πc2} *)
    iAssert (mem_auth_frag (<[1:=Πc2]> (<[0:=Πp2]> ∅)) ∗
             view_ptsto 0 Πp2 ∗ view_ptsto 1 Πc2)%I
      with "[Hm Hp Hc]" as "(Hm & Hp & Hc)"; first by iFrame.
    (* --- STEPEFFECT: parent (Effect, no effects) → child (Effect, one effect) --- *)
    wp_pure.
    iApply (wp_commit_enter with "Hm");
      [by rewrite lookup_insert_ne // lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child Πp2) with (TPath 1);
           change (vw_effq Πp2) with (@nil domains.val)).
    iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child Πc2) with (TConst CUnit); change (vw_effq Πc2) with [eff 0]).
    wp_pure.
    (* the child's effect updates the parent's view *)
    set (Πp3 := Πp2 <| vw_dec ::= dec_add_check |>
                    <| vw_sttst ::= <[0 := StEntry (vbool true) [to_false 0]]> |>).
    iApply (wp_commit_effects _
              (λ i, match i with
                    | 0%nat => mem_auth_frag (<[1:=Πc2]> (<[0:=Πp2]> ∅)) ∗
                               view_ptsto 0 Πp2 ∗ reg_token None
                    | _ => mem_auth_frag (<[1:=Πc2]> (<[0:=Πp3]> ∅)) ∗
                           view_ptsto 0 Πp3 ∗ reg_token None
                    end)%I
              with "[] [Hm Hp Hr]"); [by left| |by iFrame|].
    { iSplitL; last done. rewrite /eff. iIntros (ks' Φ') "(Hm & Hp & Hr) Hk'".
      iApply (child_effect 0 Πp2 (StEntry (vbool true) []) with "Hm Hp Hr");
        [by rewrite lookup_insert_ne // lookup_insert_eq|done|].
      iIntros "Hm Hp Hr". iApply ("Hk'" with "[Hm Hp Hr]").
      iEval (rewrite (insert_insert_ne _ 0%nat 1%nat) // insert_insert_eq) in "Hm".
      by iFrame. }
    iIntros (f' Hf') "(Hm & Hp & Hr)".
    iApply (wp_commit_finish_any with "Hm Hc"); [done|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hc".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (Πc3 := Πc2 <| vw_dec ::= dec_rm_effect |>).
    iApply (wp_commit_finish_any with "Hm Hp");
      [by left|by rewrite lookup_insert_ne // lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite (insert_insert_ne _ 0%nat 1%nat) // insert_insert_eq) in "Hm".
    set (Πp4 := Πp3 <| vw_dec ::= dec_rm_effect |>).
    (* --- STEPCHECK: the parent re-renders to () and drops the child --- *)
    wp_pure.
    iEval (rewrite insert_insert_eq) in "Hm".
    set (Πp5 := enter_view Πp4 <| vw_dec ::= dec_add_effect |>
                  <| vw_sttst ::= <[0 := StEntry (vbool false) []]> |>).
    iApply (wp_check_component _ 0 Πp4 "x" eff_parent_body _
              (λ π' s, (⌜π' = Πp5⌝ ∗ ⌜s = VConst CUnit⌝)%I) with "[] Hm Hp Hr").
    { by rewrite lookup_insert_ne // lookup_insert_eq. }
    { done. }
    { done. }
    { iIntros (ks' Φ') "Hr Hk'".
      iApply (parent_succ 0 with "Hr"); first by vm_compute.
      iIntros "Hr". iApply ("Hk'" $! (VConst CUnit) Πp5 with "[//] Hr"). by iSplit. }
    iIntros (s π' _) "Hm Hp Hr (-> & ->)".
    iEval (rewrite (insert_insert_ne _ 0%nat 1%nat) // insert_insert_eq) in "Hm".
    (* the child subtree [TPath 1] is reconciled against (): re-initialized *)
    iEval (change (vw_child Πp4) with (TPath 1)).
    do 2 wp_pure.
    iApply (wp_check_finish with "Hm Hp");
      first by rewrite lookup_insert_ne // lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite (insert_insert_ne _ 0%nat 1%nat) // insert_insert_eq) in "Hm".
    set (Πp6 := Πp5 <| vw_child := TConst CUnit |>).
    (* --- rendered: commit (no effects), check (idle), quiescent --- *)
    wp_pure.
    iApply (wp_commit_enter with "Hm");
      [by rewrite lookup_insert_ne // lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child Πp6) with (TConst CUnit);
           change (vw_effq Πp6) with (@nil domains.val)).
    wp_pure.
    iApply (wp_commit_finish_any with "Hm Hp");
      [by left|by rewrite lookup_insert_ne // lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite (insert_insert_ne _ 0%nat 1%nat) // insert_insert_eq) in "Hm".
    wp_pure.
    iApply (wp_check_idle with "Hm");
      [by rewrite lookup_insert_ne // lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child (Πp6 <| vw_dec ::= dec_rm_effect |>)) with (TConst CUnit)).
    do 2 wp_pure.
    iApply wp_events_done. iNext.
    iApply (wp_value' _ _ _ (MIdle (TPath 0))).
    iExists _, _. iFrame "Hm Ho". iPureIntro.
    exists (TPath 0). split_and!; [done| |done].
    subst Πp6 Πp5 Πp4 Πp3 Πc3. by vm_compute.
  Qed.
End parent_child.

Corollary parent_child_adequate :
  adequate NotStuck
    (cfg_expr (machine_init_cfg eff_cross_prog [])
       : expr (reactLang (prog_def_table eff_cross_prog)))
    (cfg_state (machine_init_cfg eff_cross_prog []))
    (λ w σ, ∃ t, w = MIdle t ∧ display_t 1000 (ls_mem σ) t = Ok (DConst CUnit) ∧ ls_out σ = []).
Proof.
  apply (react_adequacy_state reactΣ _ _
           (λ w m ω, ∃ t, w = MIdle t ∧ display_t 1000 m t = Ok (DConst CUnit) ∧ ω = [])).
  intros HI HR. by iApply parent_child_wp.
Qed.

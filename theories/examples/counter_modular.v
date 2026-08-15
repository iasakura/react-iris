(** * Counter, end to end, from the runtime lemmas and the body
    specifications — no whole-run computation.

    Mount, one click, re-render: the run is driven by
    [wp_init_component] / [wp_check_component] / [wp_commit_effects] /
    [wp_event_dispatch] (runtime.v) and the body and handler
    specifications of hooks.v; the tree, memory, and output steps in
    between are symbolic ([wp_pure]) and the final display is read off
    the resulting memory. Compare [examples/counter.v], which obtains the
    same conclusion by executing the machine ([wp_mrun_ok]). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine tests.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section counter_modular.
  Context `{!invGS Σ, !reactGS Σ}.

  Local Definition δ : def_table := prog_def_table counter_prog.
  Local Notation "'cint' n" := (VConst (CInt n)) (at level 10).

  (** The two updaters queued by one click of the handler (hooks.v,
      [counter_handler_spec]), with the handler's environment. *)
  Local Definition henv (p : path) (ns nx : Z) : env :=
    env_insert "_" (VConst CUnit)
      (env_insert "setS" (VSetter 0 p)
         (env_insert "s" (cint ns) [("x", cint nx)])).
  Local Definition cl1 (p : path) (ns nx : Z) : domains.val :=
    VClos "s" (EBop BPlus (EVar "s") (EConst (CInt 1))) (henv p ns nx).
  Local Definition cl2 (p : path) (ns nx : Z) : domains.val :=
    VClos "s" (ESeq (EPrint (EConst (CString "Update")))
                 (EBop BPlus (EVar "s") (EConst (CInt 1)))) (henv p ns nx).

  (** Succ-phase body with the concrete click queue [cl1; cl2] on slot 0:
      "Counter", then the fold — the second updater prints "Update"
      during the render (the update-timing observation of §2.1) — then
      "Return"; the state advances by 2 and the Effect decision is on. *)
  Lemma counter_body_succ_click (n ns nx : Z) p π ω ks Φ :
    vw_sttst π !! 0 = Some (StEntry (cint n) [cl1 p ns nx; cl2 p ns nx]) →
    render_ctx p π -∗ out_frag ω -∗
    (render_ctx p (commit_slot π 0 (cint n) (cint (n + 1 + 1))) -∗
     out_frag (ω ++ [VConst (CString "Counter"); VConst (CString "Update");
                    VConst (CString "Return")]) -∗
     WP ((FVal (VList [cint (n + 1 + 1); counter_handler p (n + 1 + 1) n]), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc [("x", cint n)] counter_body, ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl) "Hr Ho Hwp".
    rewrite /counter_body.
    wp_pure. wp_pure. wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    wp_pure.
    iApply (wp_usestate_succ_cons with "Hr"); first done. iNext. iIntros "Hr".
    do 5 wp_pure.
    iApply (wp_sttfold_cons with "Hr"). iNext. iIntros "Hr".
    do 3 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 6 wp_pure.
    iApply (wp_sttfold_nil with "Hr"). iNext. iIntros "Hr".
    do 3 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 6 wp_pure.
    rewrite -!app_assoc.
    by iApply ("Hwp" with "Hr Ho").
  Qed.

  (** ** The run: mount, one click, re-render *)

  Local Definition c0 : mcfg := machine_init_cfg counter_prog [0%nat].

  Local Definition out_final : out_buf :=
    [VConst (CString "Counter"); VConst (CString "Return");
     VConst (CString "Counter"); VConst (CString "Update");
     VConst (CString "Return")].

  Lemma counter_click_modular :
    own_cfg c0 -∗
    WP (cfg_expr c0 : expr (reactLang δ)) {{ w,
      ∃ t m, ⌜w = MIdle t⌝ ∗ mem_auth_frag m ∗ out_frag out_final ∗
        ⌜display_t 1000 m t = Ok (DList [DConst (CInt 2); DHandler])⌝ }}.
  Proof.
    iIntros "(Hm & _ & Hr & Ho)".
    iEval (rewrite /c0 /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main counter_prog])
      in "Hm Hr Ho".
    iEval (rewrite /c0 /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main counter_prog]).
    (* main expression: Counter 0 evaluates to ⟨Counter, 0⟩; STEPINIT *)
    do 6 wp_pure.
    (* --- mount: INITCOM with the Init-phase body spec --- *)
    set (p1 := fresh_path ∅).
    set (π1 := enter_view (MkView "Counter" (cint 0) dec_empty ∅ [] (TConst CUnit))
                 <| vw_sttst ::= <[0:=StEntry (cint 0) []]> |>).
    set (s1 := VList [cint 0; counter_handler p1 0 0]).
    set (ω1 := [VConst (CString "Counter"); VConst (CString "Return")]).
    iApply (wp_init_component _ _ _ _ _ _
              (λ π' s, (⌜π' = π1⌝ ∗ ⌜s = s1⌝ ∗ out_frag ω1)%I) with "[Ho] Hm Hr").
    { done. }
    { iIntros (ks Φ) "Hr Hk".
      iApply (counter_body_init _ 0 with "Hr Ho").
      iIntros "Hr Ho".
      iApply ("Hk" $! s1 π1 with "[//] Hr [Ho]"). by iFrame. }
    iIntros (s π' _) "Hm Hp Hr (-> & -> & Ho)".
    iEval (change (fresh_path ∅) with 0%nat) in "Hm Hp".
    iEval (change (fresh_path ∅) with 0%nat).
    subst p1. iEval (change (fresh_path ∅) with 0%nat) in "Ho".
    (* child view spec [0; handler] initializes to a tree *)
    unfold s1. do 5 wp_pure.
    iApply (wp_init_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* --- rendered: commit (no effects), check (idle) --- *)
    wp_pure.
    set (t1 := TList [TConst (CInt 0); TClos "_" _ _]).
    set (π2 := π1 <| vw_dec := Decisions false true |> <| vw_child := t1 |>).
    iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    do 5 wp_pure.
    iApply (wp_commit_finish_any with "Hm Hp");
      [by left|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (π3 := π2 <| vw_dec ::= dec_rm_effect |>).
    wp_pure.
    iApply (wp_check_idle with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    do 6 wp_pure.
    (* --- quiescent: the click --- *)
    iApply (wp_event_dispatch _ (TPath 0) 0%nat [] [counter_handler 0 0 0]
              with "Hm").
    { subst π3 π2 π1 t1. by vm_compute. }
    { done. }
    iNext. iIntros "Hm".
    iApply (counter_handler_spec _ 0 0 π3 (StEntry (cint 0) []) with "Hm Hp Hr");
      [by rewrite lookup_insert_eq|by subst π3 π2 π1; vm_compute|].
    iIntros "Hm Hp Hr".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (π4 := π3 <| vw_dec ::= dec_add_check |>
                  <| vw_sttst ::= <[0:= StEntry (cint 0) [cl1 0 0 0; cl2 0 0 0]]> |>).
    iAssert (mem_auth_frag (<[0:=π4]> ∅) ∗ view_ptsto 0 π4)%I
      with "[Hm Hp]" as "[Hm Hp]"; first by iFrame.
    (* --- re-render: CHECK with the Succ-phase body spec, then reconcile --- *)
    wp_pure.
    set (π5 := commit_slot (enter_view π4) 0 (cint 0) (cint (0 + 1 + 1))).
    set (s5 := VList [cint (0 + 1 + 1); counter_handler 0 (0 + 1 + 1) 0]).
    set (ω5 := ω1 ++ [VConst (CString "Counter"); VConst (CString "Update");
                      VConst (CString "Return")]).
    iApply (wp_check_component _ 0 π4 "x" counter_body _
              (λ π' s, (⌜π' = π5⌝ ∗ ⌜s = s5⌝ ∗ out_frag ω5)%I) with "[Ho] Hm Hp Hr").
    { by rewrite lookup_insert_eq. }
    { done. }
    { done. }
    { iIntros (ks Φ) "Hr Hk".
      iApply (counter_body_succ_click 0 0 0 with "Hr Ho").
      { subst π4 π3 π2 π1. by vm_compute. }
      iIntros "Hr Ho".
      iApply ("Hk" $! s5 π5 with "[//] Hr [Ho]"). by iFrame. }
    iIntros (s π' _) "Hm Hp Hr (-> & -> & Ho)".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* the state changed: reconcile the old child [0; h] against [2; h'] *)
    iEval (change (vw_child π4) with t1). unfold s5, t1.
    do 7 wp_pure.
    iApply (wp_check_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (t6 := TList [TConst (CInt (0 + 1 + 1)); TClos "_" _ _]).
    set (π6 := π5 <| vw_child := t6 |>).
    (* --- rendered again: commit (no effects), check (idle), quiescent --- *)
    wp_pure.
    iApply (wp_commit_enter with "Hm");
      [by rewrite lookup_insert_eq|by subst π6 π5 π4 π3 π2 π1; vm_compute|].
    iNext. iIntros "Hm".
    iEval (change (vw_child π6) with t6; change (vw_effq π6) with (@nil domains.val)).
    unfold t6. do 5 wp_pure.
    iApply (wp_commit_finish_any with "Hm Hp");
      [by left|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (π7 := π6 <| vw_dec ::= dec_rm_effect |>).
    wp_pure.
    iApply (wp_check_idle with "Hm");
      [by rewrite lookup_insert_eq|by subst π7 π6 π5 π4 π3 π2 π1; vm_compute|].
    iNext. iIntros "Hm".
    iEval (change (vw_child π7) with t6). unfold t6.
    do 6 wp_pure.
    iApply wp_events_done. iNext.
    iApply (wp_value' _ _ _ (MIdle (TPath 0))).
    iExists (TPath 0), (<[0:=π7]> ∅). iFrame "Hm".
    iSplit; first done. iSplitL "Ho".
    { by iEval (rewrite /ω5 /ω1 /out_final /=) in "Ho". }
    iPureIntro. subst π7 π6 π5 π4 π3 π2 π1 t6 t1. by vm_compute.
  Qed.
End counter_modular.

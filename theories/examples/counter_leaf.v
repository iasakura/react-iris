(** * Counter through the generic root render loop.

    ** What is verified

    The paper's Counter ([counter_prog], programs.v) again — but this
    time *no run lemma is proved by hand*. The client provides only:

    - the leaf data [counter_leaf]: the slot table, the rendered view
      spec, and the view a click leaves, per abstract state of
      [counter_lts] (counter_modular.v);
    - [counter_leaf_obligations]: the body in Init phase, the handler,
      and the body in Succ phase — the specifications already proved
      from the hook rules in counter_modular.v ([counter_body_init],
      [counter_handler_spec], [counter_body_succ_click]).

    The whole render loop — mount; per click: dispatch, re-render,
    reconcile, commit, check — comes from [leaf_root_obligations]
    (logic/root.v), and [counter_leaf_adequate] is the same refinement
    statement as [counter_root_adequate], obtained without proving
    [counter_mount] / [counter_click_step]. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains notation programs interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime
  adequacy component root.
From react_iris.examples Require Import counter_modular.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** ** The leaf data: Counter's views per abstract state *)

(** The view a click leaves at state [a]: both updaters queued on
    slot 0, Check on, everything else as at quiescence. *)
Definition counter_click_view (a : Z) : domains.view :=
  MkView "Counter" (VConst (CInt 0)) (Decisions true false)
    (<[0 := StEntry (VConst (CInt a)) [cl1 0 a 0; cl2 0 a 0]]> ∅) []
    (tree_of (VList [VConst (CInt a); counter_handler 0 a 0])) 1.

Definition counter_leaf : leaf_data counter_lts :=
  LeafData counter_lts "Counter" "x" counter_body (VConst (CInt 0))
    (λ a, <[0 := StEntry (VConst (CInt a)) []]> ∅)                (* slot table *)
    (λ a, VList [VConst (CInt a); counter_handler 0 a 0])          (* view spec *)
    (λ a i π, π = counter_click_view a).                           (* after a click *)

Section counter_leaf.
  Context `{!invGS Σ, !reactGS Σ}.

  Local Definition δ : def_table := prog_def_table counter_prog.
  Local Notation "'cint' n" := (VConst (CInt n)) (at level 10).

  (** ** The obligations: only the body and handler specifications *)

  Lemma counter_leaf_obligations :
    ⊢ leaf_obligations δ counter_lts counter_leaf.
  Proof.
    rewrite /leaf_obligations.
    iSplit; [iPureIntro; by vm_compute|].
    iSplit.
    { iPureIntro. intros a. split; [cbn; by repeat constructor|cbn; lia]. }
    iSplit; [iPureIntro; intros a; reflexivity|].
    iSplit.
    { iPureIntro. intros a i ->. by eexists _, _, _. }
    iSplit.
    { iPureIntro. intros a i π ->. split_and!; reflexivity. }
    iSplit.
    { iPureIntro. intros a i π -> Hc. discriminate Hc. }
    iSplit.
    { (* Init: [counter_body_init] *)
      iIntros "!>" (ω ks Φ) "Hr Ho Hk".
      iApply (counter_body_init 0 with "Hr Ho"); first done.
      iIntros "Hr Ho".
      assert (init_ctx counter_lts counter_leaf
                <| vw_sttst ::= insert 0 (StEntry (VConst (CInt 0)) []) |>
                <| vw_cur := 1 |>
              = bview counter_lts counter_leaf 0%Z (TConst CUnit)) as Hq
        by reflexivity.
      iEval (rewrite Hq) in "Hr".
      by iApply ("Hk" $! 0%Z with "[//] Hr Ho"). }
    iSplit.
    { (* Handler: [counter_handler_spec] *)
      iIntros "!>" (a i x e σ ω ks Φ) "%Hvalid %Hlk Hm Hp Hr Ho Hk".
      hnf in Hvalid; subst i.
      vm_compute in Hlk. simplify_eq.
      iApply (counter_handler_spec a 0 0
                (qview counter_lts counter_leaf a) (StEntry (cint a) [])
                with "Hm Hp Hr").
      { by rewrite lookup_insert_eq. }
      { done. }
      iIntros "Hm Hp Hr".
      iEval (rewrite insert_insert_eq) in "Hm".
      iApply ("Hk" $! (VConst CUnit) _ ω with "[] Hm Hp Hr Ho").
      iPureIntro. vm_compute. reflexivity. }
    (* Succ: [counter_body_succ_click] *)
    iIntros "!>" (a i π ω ks Φ) "%Hpost %Hcheck Hr Ho Hk".
    hnf in Hpost; subst π.
    iApply (counter_body_succ_click 0 a a 0 0 (enter_view (counter_click_view a))
              with "Hr Ho"); [done|done|].
    iIntros "Hr Ho".
    assert (commit_slot (enter_view (counter_click_view a)) 0
              (cint a) (cint (a + 1 + 1))
            = bview counter_lts counter_leaf (a + 1 + 1)%Z
                (tree_of (ld_spec counter_leaf a))
              <| vw_dec := Decisions false true |>) as Hq.
    { rewrite /commit_slot /val_eqb bool_decide_eq_false_2 //.
      intros [=]. lia. }
    iEval (rewrite Hq) in "Hr".
    iApply ("Hk" $! (a + 1 + 1)%Z true with "[] [] Hr Ho").
    { iPureIntro. hnf. lia. }
    { iPureIntro. by intros [=]. }
  Qed.

  (** ** The root obligations, from the generic loop *)

  Lemma counter_leaf_root_obligations :
    ⊢ root_obligations δ counter_prog counter_lts
        (leaf_inv counter_lts counter_leaf).
  Proof.
    iApply (leaf_root_obligations with "[] []").
    - iApply main_spec_const; reflexivity.
    - iApply counter_leaf_obligations.
  Qed.
End counter_leaf.

(** Counter refines its abstract LTS — same statement as
    [counter_root_adequate], derived through the generic render loop. *)
Corollary counter_leaf_adequate (evs : list nat) :
  Forall (λ i, i = 0%nat) evs →
  adequate NotStuck
    (cfg_expr (machine_init_cfg counter_prog evs)
       : expr (reactLang (prog_def_table counter_prog)))
    (cfg_state (machine_init_cfg counter_prog evs))
    (λ w σ, ∃ a0 a', rs_init counter_lts a0 ∧ rs_reach counter_lts a0 evs a' ∧
                     w = MIdle (TPath 0) ∧
                     display_t 1000 (ls_mem σ) (TPath 0) = Ok (rs_disp counter_lts a')).
Proof.
  intros Hall.
  apply (root_adequacy reactΣ counter_prog counter_lts
           (λ _ HR, @leaf_inv reactΣ HR counter_lts counter_leaf)).
  { intros a _. by apply counter_admissible. }
  intros HI HR. apply counter_leaf_root_obligations.
Qed.

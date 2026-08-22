(** * SelfCounter: the effect-driven render cycle converges at 3.

    ** What is verified

    The paper's SelfCounter:
<<
let SelfCounter x =
  let (s, setS) = useState x in
  print s;
  useEffect (print "Effect"; if s < 3 then setS (fun t -> t + 1) else ());
  print "Return";
  [s];;
SelfCounter 0
>>
    [selfcounter_adequate]: the program never gets stuck, and if it
    reaches a value it is quiescent, displaying 3, having printed exactly
    the console of §2.2: 0 Return Effect 1 Return Effect 2 Return Effect
    3 Return Effect.

    After mounting, the effect runs and (while [s < 3]) queues an
    update, which turns on Check; the re-render commits the folded state,
    registers a new effect, and — the state having changed — turns on
    Effect; the cycle repeats until [s = 3], where the effect still runs
    but queues nothing and the machine becomes quiescent. The measure of
    the cycle is [3 − s] (design decision D3, concretely).

    Ingredients exercised for the first time here: [upd_pure] for a
    concrete updater ([λt. t+1]), [wp_useeffect] (registration),
    [wp_commit_effects] with an [effect_spec] that changes the state
    (setter call in Normal phase), and [wp_usestate_succ_pure] with a
    genuinely pure queue. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains notation interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime adequacy.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** ** SelfCounter (§2.2) — an effect creating an autonomous render cycle

<<
let SelfCounter x =
  let (s, setS) = useState x in
  print s;
  useEffect (print "Effect"; if s < 3 then setS (fun s -> s + 1) else ());
  print "Return";
  [s];;
SelfCounter 0
>>

    Console: 0 Return Effect 1 Return Effect 2 Return Effect 3 Return
    Effect. *)
Definition selfcounter_body : syntax.expr :=
  (let: "s", "setS" := useState "x" in
   print: "s" ;;
   useEffect: (print: Str "Effect" ;;
               if: "s" < 3 then "setS" (λ: "t", "t" + 1) else #()) ;;
   print: Str "Return" ;;
   ⟪ "s" ⟫)%r.

Definition selfcounter_prog : prog :=
  Prog [("SelfCounter", CompDef "x" selfcounter_body)] (Comp "SelfCounter" 0)%r.

Section selfcounter.
  Context `{!invGS Σ, !reactGS Σ}.

  Local Definition δ : def_table := prog_def_table selfcounter_prog.
  Local Notation "'cint' n" := (VConst (CInt n)) (at level 10).

  (** ** Program-side data: what the run creates from [selfcounter_body]

      The effect body, the effect thunk registered at state [k] (in the
      body's environment [benv]), the updater it queues, and the function
      that updater computes. *)
  Local Definition eff_body : syntax.expr :=
    (print: Str "Effect" ;; if: "s" < 3 then "setS" (λ: "t", "t" + 1) else #())%r.
  Local Definition benv (p : path) (k : Z) : env :=
    env_insert "setS" (VSetter 0 p) (env_insert "s" (cint k) [("x", cint 0)]).
  Local Definition eff (p : path) (k : Z) : domains.val := VClos "_" eff_body (benv p k).
  Local Definition inc (p : path) (k : Z) : domains.val :=
    VClos "t" ("t" + 1)%r (benv p k).
  Local Definition finc (v : domains.val) : domains.val :=
    match v with VConst (CInt n) => VConst (CInt (n + 1)) | _ => v end.

  (** ** State-side data: the views along the cycle, and the outputs

      [ΠA k]: the rendered view at state [k] with its effect pending —
      slot 0 committed at [k] with an empty queue, the effect thunk
      registered at [k] queued, Effect on, and the child [[k]].
      [ΠF]: the final quiescent view. *)
  Local Definition ΠA (k : Z) : domains.view :=
    {|
       vw_comp := "SelfCounter";
       vw_arg := cint 0;
       vw_dec := Decisions false true;
       vw_sttst := <[0 := StEntry (cint k) []]> ∅;
       vw_effq := [eff 0 k];
       vw_child := TList [TConst (CInt k)];
       vw_hook_cursor := 1
     |}.
  Local Definition ΠF : domains.view := ΠA 3 <| vw_dec ::= dec_rm_effect |>.

  (** [A k ω]: the machine is about to commit the pending effect
      (STEPEFFECT) with the memory holding [ΠA k] and output [ω]. *)
  Local Definition A (k : Z) (ω : out_buf) : iProp Σ :=
    mem_auth_frag (<[0 := ΠA k]> ∅) ∗ view_ptsto 0 (ΠA k) ∗ reg_token None ∗ out_frag ω.

  Local Definition ω_mount : out_buf := [cint 0; VConst (CString "Return")].
  Local Definition ω_cycle (k : Z) : out_buf :=
    [VConst (CString "Effect"); cint (k + 1); VConst (CString "Return")].
  Local Definition ω_final : out_buf :=
    [cint 0; VConst (CString "Return"); VConst (CString "Effect");
     cint 1; VConst (CString "Return"); VConst (CString "Effect");
     cint 2; VConst (CString "Return"); VConst (CString "Effect");
     cint 3; VConst (CString "Return"); VConst (CString "Effect")].

  (** ** The updater is pure *)

  (** [λt. t+1] is a pure updater on integers — the obligation of
      [wp_usestate_succ_pure], discharged by symbolic execution with no
      state resources in hand. *)
  Lemma upd_pure_inc (σ : env) :
    ⊢ upd_pure δ is_int (VClos "t" ("t" + 1)%r σ) finc.
  Proof.
    iIntros "!>" (v ks Φ [n ->]) "Hwp".
    do 5 wp_pure. by iApply "Hwp".
  Qed.

  Lemma queue_pure_inc (p : path) (k : Z) :
    ⊢ queue_pure δ is_int [inc p k] [finc].
  Proof.
    iSplit.
    - iPureIntro. constructor; last constructor. intros v [n ->]. by exists (n + 1)%Z.
    - iSplitL; last done. iApply upd_pure_inc.
  Qed.

  (** ** Body specifications *)

  (** Init phase (argument 0): allocates slot 0 at 0, prints 0, registers
      the effect thunk, prints "Return", returns the view spec [[0]]. *)
  Lemma body_init (p : path) (π : domains.view) (ω : out_buf)
      (ks : list machine.frame) (Φ : mval → iProp Σ) :
    vw_hook_cursor π = 0 →
    render_ctx p π -∗ out_frag ω -∗
    (render_ctx p (π <| vw_sttst ::= <[0 := StEntry (cint 0) []]> |> <| vw_hook_cursor := 1 |>
                     <| vw_effq ::= (λ q, q ++ [eff p 0]) |>) -∗
     out_frag (ω ++ [cint 0; VConst (CString "Return")]) -∗
     WP ((FVal (VList [cint 0]), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit [("x", cint 0)] selfcounter_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hcur) "Hr Ho Hwp".
    rewrite /selfcounter_body.
    iApply (wp_usestate_init with "Hr"). iNext. iIntros "Hr".
    wp_pure.
    iApply (wp_usestate_mount with "Hr"). iNext. iIntros "Hr".
    rewrite Hcur.
    do 3 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 2 wp_pure.
    iApply (wp_useeffect with "Hr"); first done. iNext. iIntros "Hr".
    do 4 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 4 wp_pure.
    rewrite -app_assoc.
    by iApply ("Hwp" with "Hr Ho").
  Qed.

  (** Succ phase at state [k] with the queued updater: folds to [k+1]
      (Effect on, since the value changed), prints it, registers the
      effect thunk at [k+1], prints "Return", returns [[k+1]]. *)
  Lemma body_succ (k j : Z) (p : path) (π : domains.view) (ω : out_buf)
      (ks : list machine.frame) (Φ : mval → iProp Σ) :
    vw_hook_cursor π = 0 →
    vw_sttst π !! 0 = Some (StEntry (cint k) [inc p j]) →
    render_ctx p π -∗ out_frag ω -∗
    (render_ctx p (π <| vw_dec ::= dec_add_effect |>
                     <| vw_sttst ::= <[0 := StEntry (cint (k + 1)) []]> |>
                     <| vw_hook_cursor := 1 |>
                     <| vw_effq ::= (λ q, q ++ [eff p (k + 1)]) |>) -∗
     out_frag (ω ++ [cint (k + 1); VConst (CString "Return")]) -∗
     WP ((FVal (VList [cint (k + 1)]), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc [("x", cint 0)] selfcounter_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hcur Hl) "Hr Ho Hwp".
    rewrite /selfcounter_body.
    iApply (wp_usestate_succ_pure _ is_int _ _ _ _ _ _ _ _ [inc p j] [finc]
              with "[] Hr").
    { by rewrite Hcur. }
    { by exists k. }
    { iApply queue_pure_inc. }
    iIntros "Hr". cbn [fold_upd finc]. rewrite Hcur.
    (* the value changed: Effect *)
    iEval (rewrite /commit_slot /val_eqb bool_decide_eq_false_2;
           last (intros [=]; lia)) in "Hr".
    do 3 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 2 wp_pure.
    iApply (wp_useeffect with "Hr"); first done. iNext. iIntros "Hr".
    do 4 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 4 wp_pure.
    rewrite -app_assoc.
    by iApply ("Hwp" with "Hr Ho").
  Qed.

  (** ** The effect *)

  (** At state [k < 3]: prints "Effect" and queues [λt. t+1] on slot 0
      of the view at [p], turning on Check. *)
  Lemma effect_lt (k : Z) (p : path) (π : domains.view) (ent : st_entry)
      (m : tree_mem) (ω : out_buf) (ks : list machine.frame)
      (Φ : mval → iProp Σ) :
    (k < 3)%Z →
    m !! p = Some π →
    vw_sttst π !! 0 = Some ent →
    mem_auth_frag m -∗ view_ptsto p π -∗ reg_token None -∗ out_frag ω -∗
    (let π' := π <| vw_dec ::= dec_add_check |>
                 <| vw_sttst ::= insert 0 (ent <| st_queue ::= (λ q, q ++ [inc p k]) |>) |> in
     mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
     out_frag (ω ++ [VConst (CString "Effect")]) -∗
     WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PNormal (benv p k) eff_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hk Hp Hl) "Hm Hv Hr Ho Hwp".
    rewrite /eff_body.
    do 3 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 6 wp_pure.
    (* the comparison: [k <? 3] is [true] *)
    iApply (wp_pure_step _ _ (FVal (VConst (CBool true)), _)); [done| |iNext].
    { intros σ. cbn. rewrite (proj2 (Z.ltb_lt k 3)); [reflexivity|lia]. }
    do 5 wp_pure.
    iApply (wp_setter_normal with "Hm Hv Hr"); [done|done|].
    iNext. iIntros "Hm Hv Hr".
    by iApply ("Hwp" with "Hm Hv Hr Ho").
  Qed.

  (** At state [k ≥ 3]: prints "Effect" and does nothing else. *)
  Lemma effect_ge (k : Z) (p : path) (ω : out_buf)
      (ks : list machine.frame) (Φ : mval → iProp Σ) :
    (3 ≤ k)%Z →
    out_frag ω -∗
    (out_frag (ω ++ [VConst (CString "Effect")]) -∗
     WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PNormal (benv p k) eff_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hk) "Ho Hwp".
    rewrite /eff_body.
    do 3 wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 6 wp_pure.
    iApply (wp_pure_step _ _ (FVal (VConst (CBool false)), _)); [done| |iNext].
    { intros σ. cbn. rewrite (proj2 (Z.ltb_ge k 3)); [reflexivity|lia]. }
    do 2 wp_pure.
    by iApply "Hwp".
  Qed.

  (** ** The render/effect cycle *)


  (** One cycle while [k < 3]: the effect runs and queues an update
      (Check), the re-render folds the state to [k+1] and registers a
      new effect (Effect), the child is reconciled — back to [A (k+1)],
      with the measure [3 − k] decreased. *)
  Lemma cycle (k : Z) (ω : out_buf) (ks : list machine.frame)
      (Φ : mval → iProp Σ) :
    (k < 3)%Z →
    A k ω -∗
    (A (k + 1) (ω ++ ω_cycle k) -∗
     WP ((FCommit (TPath 0), KPostCommit (TPath 0) :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FCommit (TPath 0), KPostCommit (TPath 0) :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hk) "(Hm & Hp & Hr & Ho) Hk".
    (* STEPEFFECT: commit the child (nothing), then run the effect *)
    iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child (ΠA k)) with (TList [TConst (CInt k)]);
           change (vw_effq (ΠA k)) with [eff 0 k]).
    do 3 wp_pure.
    set (ΠB := ΠA k <| vw_dec ::= dec_add_check |>
                    <| vw_sttst ::= <[0 := StEntry (cint k) [inc 0 k]]> |>).
    iApply (wp_commit_effects _
              (λ i, match i with
                    | 0%nat => mem_auth_frag (<[0:=ΠA k]> ∅) ∗ view_ptsto 0 (ΠA k) ∗
                               reg_token None ∗ out_frag ω
                    | _ => mem_auth_frag (<[0:=ΠB]> ∅) ∗ view_ptsto 0 ΠB ∗
                           reg_token None ∗ out_frag (ω ++ [VConst (CString "Effect")])
                    end)%I
              with "[] [Hm Hp Hr Ho]"); [by left| | by iFrame |].
    { (* the effect at [k < 3] *)
      iSplitL; last done. rewrite /eff. iIntros (ks' Φ') "(Hm & Hp & Hr & Ho) Hk'".
      iApply (effect_lt k 0 (ΠA k) (StEntry (cint k) []) with "Hm Hp Hr Ho");
        [done|by rewrite lookup_insert_eq|done|].
      iIntros "Hm Hp Hr Ho".
      iApply ("Hk'" with "[Hm Hp Hr Ho]").
      iEval (rewrite insert_insert_eq) in "Hm".
      iAssert (mem_auth_frag (<[0:=ΠB]> ∅) ∗ view_ptsto 0 ΠB)%I
        with "[Hm Hp]" as "[Hm Hp]"; first by iFrame.
      iFrame. }
    iIntros (f' Hf') "(Hm & Hp & Hr & Ho)".
    iApply (wp_commit_finish_any with "Hm Hp"); [done|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (ΠC := ΠB <| vw_dec ::= dec_rm_effect |>).
    (* STEPCHECK: the re-render *)
    wp_pure.
    set (π5 := enter_view ΠC <| vw_dec ::= dec_add_effect |>
                 <| vw_sttst ::= <[0 := StEntry (cint (k + 1)) []]> |>
                 <| vw_hook_cursor := 1 |>
                 <| vw_effq ::= (λ q, q ++ [eff 0 (k + 1)]) |>).
    iApply (wp_check_component _ 0 ΠC "x" selfcounter_body _
              (λ π' s, (⌜π' = π5⌝ ∗ ⌜s = VList [cint (k + 1)]⌝ ∗
                        out_frag (ω ++ ω_cycle k))%I) with "[Ho] Hm Hp Hr").
    { by rewrite lookup_insert_eq. }
    { done. }
    { done. }
    { iIntros (ks' Φ') "Hr Hk'".
      iApply (body_succ k k with "Hr Ho").
      { done. }
      { subst ΠC ΠB. by vm_compute. }
      iIntros "Hr Ho".
      iApply ("Hk'" $! (VList [cint (k + 1)]) π5 with "[%] Hr [Ho]");
        first (subst π5 ΠC ΠB; split; by vm_compute).
      iSplit; first done. iSplit; first done.
      by iEval (rewrite /ω_cycle -app_assoc) in "Ho". }
    iIntros (s π' _) "Hm Hp Hr (-> & -> & Ho)".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* the state changed: reconcile the child [k] against [k+1] *)
    iEval (change (vw_child ΠC) with (TList [TConst (CInt k)])).
    do 4 wp_pure.
    iApply (wp_check_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* re-rendered: back to the commit step with [ΠA (k+1)] *)
    wp_pure.
    assert (π5 <| vw_child := TList [TConst (CInt (k + 1))] |> = ΠA (k + 1)) as ->
      by (subst π5 ΠC ΠB; vm_compute; reflexivity).
    iApply "Hk". by iFrame.
  Qed.

  (** The last round at [k = 3]: the effect runs (prints "Effect") but
      queues nothing; the check finds nothing to do; quiescence. *)
  Lemma last_round (ω : out_buf) (ks : list machine.frame)
      (Φ : mval → iProp Σ) :
    A 3 ω -∗
    (mem_auth_frag (<[0 := ΠF]> ∅) -∗ out_frag (ω ++ [VConst (CString "Effect")]) -∗
     WP ((FIdle (TPath 0), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FCommit (TPath 0), KPostCommit (TPath 0) :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "(Hm & Hp & Hr & Ho) Hk".
    iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child (ΠA 3)) with (TList [TConst (CInt 3)]);
           change (vw_effq (ΠA 3)) with [eff 0 3]).
    do 3 wp_pure.
    iApply (wp_commit_effects _
              (λ i, match i with
                    | 0%nat => out_frag ω
                    | _ => out_frag (ω ++ [VConst (CString "Effect")])
                    end)%I
              with "[] Ho"); [by left| |].
    { iSplitL; last done. rewrite /eff. iIntros (ks' Φ') "Ho Hk'".
      iApply (effect_ge 3 0 with "Ho"); first lia.
      iIntros "Ho". by iApply "Hk'". }
    iIntros (f' Hf') "Ho".
    iApply (wp_commit_finish_any with "Hm Hp"); [done|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    wp_pure.
    iApply (wp_check_idle with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child (ΠA 3 <| vw_dec ::= dec_rm_effect |>))
             with (TList [TConst (CInt 3)])).
    do 4 wp_pure.
    by iApply ("Hk" with "Hm Ho").
  Qed.

  (** ** Mount *)
  Lemma mount (Φ : mval → iProp Σ) :
    own_cfg (machine_init_cfg selfcounter_prog []) -∗
    (A 0 ω_mount -∗
     WP ((FCommit (TPath 0), [KPostCommit (TPath 0); KEvents []]) : expr (reactLang δ)) {{ Φ }}) -∗
    WP (cfg_expr (machine_init_cfg selfcounter_prog []) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "(Hm & _ & Hr & Ho) Hk".
    iEval (rewrite /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main selfcounter_prog])
      in "Hm Hr Ho".
    iEval (rewrite /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main selfcounter_prog]).
    do 6 wp_pure.
    set (π1 := enter_view ({|
       vw_comp := "SelfCounter";
       vw_arg := cint 0;
       vw_dec := dec_empty;
       vw_sttst := ∅;
       vw_effq := [];
       vw_child := TConst CUnit;
       vw_hook_cursor := 0
     |})
                 <| vw_sttst ::= <[0:=StEntry (cint 0) []]> |> <| vw_hook_cursor := 1 |>
                 <| vw_effq ::= (λ q, q ++ [eff (fresh_path ∅) 0]) |>).
    iApply (wp_init_component _ _ _ _ _ _
              (λ π' s, (⌜π' = π1⌝ ∗ ⌜s = VList [cint 0]⌝ ∗ out_frag ω_mount)%I)
              with "[Ho] Hm Hr").
    { done. }
    { iIntros (ks Φ') "Hr Hk'".
      iApply (body_init with "Hr Ho"); first done.
      iIntros "Hr Ho".
      iApply ("Hk'" $! (VList [cint 0]) π1 with "[%] Hr [Ho]");
        [subst π1; split; by vm_compute|by iFrame]. }
    iIntros (s π' _) "Hm Hp Hr (-> & -> & Ho)".
    iEval (change (fresh_path ∅) with 0%nat) in "Hm Hp".
    iEval (change (fresh_path ∅) with 0%nat).
    do 3 wp_pure.
    iApply (wp_init_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    wp_pure.
    assert (π1 <| vw_dec := Decisions false true |> <| vw_child := TList [TConst (CInt 0)] |>
            = ΠA 0) as -> by (subst π1; vm_compute; reflexivity).
    iApply "Hk". by iFrame.
  Qed.

  (** ** The whole run *)
  Lemma selfcounter_wp :
    own_cfg (machine_init_cfg selfcounter_prog []) -∗
    WP (cfg_expr (machine_init_cfg selfcounter_prog []) : expr (reactLang δ)) {{ w,
      ∃ m ω, mem_auth_frag m ∗ out_frag ω ∗
        ⌜∃ t, w = MIdle t ∧
              display_t 1000 m t = Ok (DList [DConst (CInt 3)]) ∧ ω = ω_final⌝ }}.
  Proof.
    iIntros "Hown".
    iApply (mount with "Hown"). iIntros "HA".
    iApply (cycle 0 with "HA"); first lia. iIntros "HA".
    iApply (cycle 1 with "HA"); first lia. iIntros "HA".
    iApply (cycle 2 with "HA"); first lia. iIntros "HA".
    iApply (last_round with "HA"). iIntros "Hm Ho".
    iApply wp_events_done. iNext.
    iApply (wp_value' _ _ _ (MIdle (TPath 0))).
    iExists _, _. iFrame "Hm Ho". iPureIntro.
    exists (TPath 0). split_and!; [done|by vm_compute|by vm_compute].
  Qed.
End selfcounter.

(** The pure statement: the SelfCounter program never gets stuck, and if
    it reaches a value it is quiescent, displaying 3, having printed
    exactly the console of §2.2. *)
Corollary selfcounter_adequate :
  adequate NotStuck
    (cfg_expr (machine_init_cfg selfcounter_prog [])
       : expr (reactLang (prog_def_table selfcounter_prog)))
    (cfg_state (machine_init_cfg selfcounter_prog []))
    (λ w σ, ∃ t, w = MIdle t ∧
       display_t 1000 (ls_mem σ) t = Ok (DList [DConst (CInt 3)]) ∧
       ls_out σ =
         [VConst (CInt 0); VConst (CString "Return"); VConst (CString "Effect");
          VConst (CInt 1); VConst (CString "Return"); VConst (CString "Effect");
          VConst (CInt 2); VConst (CString "Return"); VConst (CString "Effect");
          VConst (CInt 3); VConst (CString "Return"); VConst (CString "Effect")]).
Proof.
  apply (react_adequacy_state reactΣ _ _
           (λ w m ω, ∃ t, w = MIdle t ∧
              display_t 1000 m t = Ok (DList [DConst (CInt 3)]) ∧
              ω = [VConst (CInt 0); VConst (CString "Return"); VConst (CString "Effect");
                   VConst (CInt 1); VConst (CString "Return"); VConst (CString "Effect");
                   VConst (CInt 2); VConst (CString "Return"); VConst (CString "Effect");
                   VConst (CInt 3); VConst (CString "Return"); VConst (CString "Effect")])).
  intros HI HR. by iApply selfcounter_wp.
Qed.

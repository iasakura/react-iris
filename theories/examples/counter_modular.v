(** * Counter: every click trace, verified from the hook rules.

    ** What is verified

    The paper's Counter ([counter_prog], programs.v):
<<
let Counter x =
  print "Counter";
  let (s, setS) = useState x in
  print "Return";
  [s, button (fun _ -> setS (fun s -> s + 1);
                       setS (fun s -> print "Update"; s + 1))];;
Counter 0
>>
    - [counter_trace_adequate]: for every trace of clicks, the machine
      never gets stuck, and whenever it reaches a value it is quiescent
      with display [2·|clicks|; handler] and output
      ["Counter"; "Return"] ++ ["Counter"; "Update"; "Return"]^|clicks|;
    - [counter_root_adequate]: Counter refines the abstract LTS
      [counter_lts] (states ℤ, initial 0, the click adds 2, display shows
      the state), through [root_adequacy] (component.v).

    The proofs are driven by the runtime lemmas ([wp_init_component] /
    [wp_check_component] / [wp_event_dispatch], runtime.v) and by
    specifications of the Counter body and handler proved from the hook
    rules (hooks.v); tree, memory, and output steps in between are
    symbolic ([wp_pure]) — no whole-run computation. Compare
    [examples/counter.v], which obtains a fixed-trace conclusion by
    executing the machine ([wp_mrun_ok]). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains notation interp machine.
From react_iris.examples Require Import programs.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime adequacy component.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** ** The specification: an abstract LTS *)
Definition counter_lts : root_spec := {|
  rs_A := Z;
  rs_init a := a = 0%Z;
  rs_valid a i := i = 0%nat;
  rs_step a i a' := a' = (a + 2)%Z;
  rs_disp a := DList [DConst (CInt a); DHandler];
|}.

Section counter_modular.
  Context `{!invGS Σ, !reactGS Σ}.

  Local Definition δ : def_table := prog_def_table counter_prog.
  Local Notation "'cint' n" := (VConst (CInt n)) (at level 10).

  (** ** Program-side data: what the run creates from [counter_body] *)

  (** The handler closure rendered by the body: it captures the current
      state [ns] and the argument [nx] (equal on the initial render,
      distinct after re-renders). *)
  Definition counter_handler (p : path) (ns nx : Z) : domains.val :=
    VClos "_"
      ("setS" (λ: "s", "s" + 1) ;; "setS" (λ: "s", print: Str "Update" ;; "s" + 1))%r
      (env_insert "setS" (VSetter 0 p)
         (env_insert "s" (VConst (CInt ns)) [("x", VConst (CInt nx))])).

  (** The two updaters a click queues on slot 0, in the handler's
      environment. *)
  Local Definition henv (p : path) (ns nx : Z) : env :=
    env_insert "_" (VConst CUnit)
      (env_insert "setS" (VSetter 0 p)
         (env_insert "s" (cint ns) [("x", cint nx)])).
  Local Definition cl1 (p : path) (ns nx : Z) : domains.val :=
    VClos "s" ("s" + 1)%r (henv p ns nx).
  Local Definition cl2 (p : path) (ns nx : Z) : domains.val :=
    VClos "s" (print: Str "Update" ;; "s" + 1)%r (henv p ns nx).

  (** ** State-side data: the quiescent view and the outputs

      After mounting, and after every click cycle, the memory holds the
      single Counter view [Π n]: state slot 0 committed at [n] with an
      empty queue, no decisions, no pending effects, and the rendered
      child [[n; handler]] where the handler closure captured [n]. *)
  Local Definition hbody : syntax.expr :=
    ("setS" (λ: "s", "s" + 1) ;; "setS" (λ: "s", print: Str "Update" ;; "s" + 1))%r.

  Local Definition Π (n : Z) : domains.view :=
    MkView "Counter" (cint 0) (Decisions false false)
      (<[0 := StEntry (cint n) []]> ∅) []
      (TList [TConst (CInt n);
              TClos "_" hbody
                (env_insert "setS" (VSetter 0 0)
                   (env_insert "s" (cint n) [("x", cint 0)]))]).

  (** The invariant across events: [Π n] in memory, output [ω]. *)
  Local Definition I (n : Z) (ω : out_buf) : iProp Σ :=
    mem_auth_frag (<[0 := Π n]> ∅) ∗ view_ptsto 0 (Π n) ∗ reg_token None ∗ out_frag ω.

  Local Definition ω_mount : out_buf :=
    [VConst (CString "Counter"); VConst (CString "Return")].
  Local Definition ω_click : out_buf :=
    [VConst (CString "Counter"); VConst (CString "Update"); VConst (CString "Return")].

  Lemma display_Π (n : Z) :
    display_t 1000 (<[0 := Π n]> ∅) (TPath 0)
      = Ok (DList [DConst (CInt n); DHandler]).
  Proof. by vm_compute. Qed.

  (** ** Specifications of the body and the handler, from the hook rules *)

  (** Init phase: prints "Counter", allocates slot 0 with the argument,
      prints "Return", and returns the view spec [[n; handler]]. *)
  Lemma counter_body_init (n : Z) (p : path) (π : domains.view)
      (ω : out_buf) (ks : list machine.frame) (Φ : mval → iProp Σ) :
    render_ctx p π -∗ out_frag ω -∗
    (render_ctx p (π <| vw_sttst ::= insert 0 (StEntry (VConst (CInt n)) []) |>) -∗
     out_frag (ω ++ [VConst (CString "Counter"); VConst (CString "Return")]) -∗
     WP ((FVal (VList [VConst (CInt n); counter_handler p n n]), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PInit [("x", VConst (CInt n))] counter_body, ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hr Ho Hwp".
    rewrite /counter_body.
    wp_pure. wp_pure. wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    wp_pure.
    iApply (wp_usestate_init with "Hr"). iNext. iIntros "Hr".
    wp_pure.
    iApply (wp_usestate_mount with "Hr"). iNext. iIntros "Hr".
    wp_pure. wp_pure. wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 6 wp_pure.
    rewrite -app_assoc.
    by iApply ("Hwp" with "Hr Ho").
  Qed.

  (** Succ phase with a pure, int-preserving queue on slot 0 (the
      argument [nx] is only read by the ignored initial-value expression):
      prints "Counter", folds the queue, prints "Return", returns the view
      spec with the folded value. *)

  Lemma counter_body_succ (nx n : Z) (q : list domains.val)
      (fs : list (domains.val → domains.val)) (p : path) (π : domains.view)
      (ω : out_buf) (ks : list machine.frame) (Φ : mval → iProp Σ) :
    vw_sttst π !! 0 = Some (StEntry (VConst (CInt n)) q) →
    queue_pure δ is_int q fs -∗
    render_ctx p π -∗ out_frag ω -∗
    (∀ n', ⌜fold_upd fs (VConst (CInt n)) = VConst (CInt n')⌝ -∗
     render_ctx p (commit_slot π 0 (VConst (CInt n)) (VConst (CInt n'))) -∗
     out_frag (ω ++ [VConst (CString "Counter"); VConst (CString "Return")]) -∗
     WP ((FVal (VList [VConst (CInt n'); counter_handler p n' nx]), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc [("x", VConst (CInt nx))] counter_body, ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl) "#Hq Hr Ho Hwp".
    iPoseProof "Hq" as "[%Hdom _]".
    pose proof (fold_upd_dom is_int fs (VConst (CInt n)) Hdom (ex_intro _ n eq_refl))
      as [n' Hn'].
    rewrite /counter_body.
    wp_pure. wp_pure. wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    wp_pure.
    iApply (wp_usestate_succ_pure with "Hq Hr"); [done|by exists n|].
    iIntros "Hr". rewrite Hn'.
    wp_pure. wp_pure. wp_pure.
    iApply (wp_print with "Ho"). iNext. iIntros "Ho".
    do 6 wp_pure.
    rewrite -app_assoc.
    by iApply ("Hwp" with "[//] Hr Ho").
  Qed.

  (** The handler, invoked outside rendering (Normal phase, empty
      register) on the mounted view: enqueues both updaters on slot 0
      and turns on Check — the machine content of "the callback is a
      transition (+2) of the abstract state", to be lifted to a ghost
      ghost slot in the component layer. *)
  Lemma counter_handler_spec (ns nx : Z) (p : path) (π : domains.view)
      (ent : st_entry) (m : tree_mem) (ks : list machine.frame)
      (Φ : mval → iProp Σ) :
    m !! p = Some π →
    vw_sttst π !! 0 = Some ent →
    mem_auth_frag m -∗ view_ptsto p π -∗ reg_token None -∗
    (let henv := env_insert "_" (VConst CUnit)
                   (env_insert "setS" (VSetter 0 p)
                      (env_insert "s" (VConst (CInt ns)) [("x", VConst (CInt nx))])) in
     let cl1 := VClos "s" ("s" + 1)%r henv in
     let cl2 := VClos "s" (print: Str "Update" ;; "s" + 1)%r henv in
     let π' := π <| vw_dec ::= dec_add_check |>
                 <| vw_sttst ::= insert 0 (ent <| st_queue ::= (λ q, q ++ [cl1; cl2]) |>) |> in
     mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
     WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PNormal (env_insert "_" (VConst CUnit)
                          (env_insert "setS" (VSetter 0 p)
                             (env_insert "s" (VConst (CInt ns)) [("x", VConst (CInt nx))])))
           ("setS" (λ: "s", "s" + 1) ;; "setS" (λ: "s", print: Str "Update" ;; "s" + 1))%r,
         ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hl) "Hm Hv Hr Hwp".
    wp_pure. wp_pure. wp_pure. wp_pure. wp_pure.
    iApply (wp_setter_normal with "Hm Hv Hr"); [done|done|].
    iNext. iIntros "Hm Hv Hr".
    wp_pure. wp_pure. wp_pure. wp_pure. wp_pure.
    iApply (wp_setter_normal with "Hm Hv Hr").
    { by rewrite lookup_insert_eq. }
    { by rewrite lookup_insert_eq. }
    iNext. iIntros "Hm Hv Hr".
    (* normalize: collapse double inserts, reassociate the queue *)
    iEval (rewrite /= !insert_insert_eq /= -!app_assoc) in "Hm".
    iEval (rewrite /= !insert_insert_eq /= -!app_assoc) in "Hv".
    by iApply ("Hwp" with "Hm Hv Hr").
  Qed.

  (** Succ-phase body with the concrete click queue [cl1; cl2] on slot 0:
      "Counter", then the fold — the second updater prints "Update"
      during the render (the update-timing observation of §2.1) — then
      "Return"; the state advances by 2 and the Effect decision is on. *)
  Lemma counter_body_succ_click (narg n ns nx : Z) (p : path)
      (π : domains.view) (ω : out_buf) (ks : list machine.frame)
      (Φ : mval → iProp Σ) :
    vw_sttst π !! 0 = Some (StEntry (cint n) [cl1 p ns nx; cl2 p ns nx]) →
    render_ctx p π -∗ out_frag ω -∗
    (render_ctx p (commit_slot π 0 (cint n) (cint (n + 1 + 1))) -∗
     out_frag (ω ++ [VConst (CString "Counter"); VConst (CString "Update");
                    VConst (CString "Return")]) -∗
     WP ((FVal (VList [cint (n + 1 + 1); counter_handler p (n + 1 + 1) narg]), ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc [("x", cint narg)] counter_body, ks)
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

  (** ** The runs *)

  (** *** Mount: from the initial configuration to the quiescent [I 0] *)
  Lemma counter_mount (evs : list nat) (Φ : mval → iProp Σ) :
    own_cfg (machine_init_cfg counter_prog evs) -∗
    (I 0 ω_mount -∗
     WP ((FIdle (TPath 0), [KEvents evs]) : expr (reactLang δ)) {{ Φ }}) -∗
    WP (cfg_expr (machine_init_cfg counter_prog evs) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "(Hm & _ & Hr & Ho) Hk".
    iEval (rewrite /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main counter_prog])
      in "Hm Hr Ho".
    iEval (rewrite /machine_init_cfg /cfg_expr;
           cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd p_main counter_prog]).
    (* main expression: Counter 0 evaluates to ⟨Counter, 0⟩; STEPINIT *)
    do 6 wp_pure.
    (* INITCOM with the Init-phase body spec *)
    set (π1 := enter_view (MkView "Counter" (cint 0) dec_empty ∅ [] (TConst CUnit))
                 <| vw_sttst ::= <[0:=StEntry (cint 0) []]> |>).
    set (s1 := VList [cint 0; counter_handler (fresh_path ∅) 0 0]).
    iApply (wp_init_component _ _ _ _ _ _
              (λ π' s, (⌜π' = π1⌝ ∗ ⌜s = s1⌝ ∗ out_frag ω_mount)%I) with "[Ho] Hm Hr").
    { done. }
    { iIntros (ks Φ') "Hr Hk'".
      iApply (counter_body_init 0 with "Hr Ho").
      iIntros "Hr Ho".
      iApply ("Hk'" $! s1 π1 with "[//] Hr [Ho]"). by iFrame. }
    iIntros (s π' _) "Hm Hp Hr (-> & -> & Ho)".
    iEval (change (fresh_path ∅) with 0%nat) in "Hm Hp".
    iEval (change (fresh_path ∅) with 0%nat).
    (* child view spec [0; handler] initializes to a tree *)
    unfold s1. do 5 wp_pure.
    iApply (wp_init_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* rendered: commit (no effects), check (idle) *)
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
    (* the quiescent view is [Π 0] *)
    assert (π3 = Π 0) as -> by (subst π3 π2 π1 t1; vm_compute; reflexivity).
    iApply "Hk". by iFrame.
  Qed.

  (** *** One click: [I n] to [I (n+1+1)] *)
  Lemma counter_click_step (n : Z) (ω : out_buf) (evs : list nat)
      (ks : list machine.frame) (Φ : mval → iProp Σ) :
    I n ω -∗
    (I (n + 1 + 1) (ω ++ ω_click) -∗
     WP ((FIdle (TPath 0), KEvents evs :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FIdle (TPath 0), KEvents (0%nat :: evs) :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "(Hm & Hp & Hr & Ho) Hk".
    (* dispatch the handler *)
    iApply (wp_event_dispatch _ (TPath 0) 0%nat evs [counter_handler 0 n 0] with "Hm").
    { by vm_compute. }
    { done. }
    iNext. iIntros "Hm".
    iApply (counter_handler_spec n 0 0 (Π n) (StEntry (cint n) []) with "Hm Hp Hr");
      [by rewrite lookup_insert_eq|by vm_compute|].
    iIntros "Hm Hp Hr".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (π4 := Π n <| vw_dec ::= dec_add_check |>
                   <| vw_sttst ::= <[0:= StEntry (cint n) [cl1 0 n 0; cl2 0 n 0]]> |>).
    iAssert (mem_auth_frag (<[0:=π4]> ∅) ∗ view_ptsto 0 π4)%I
      with "[Hm Hp]" as "[Hm Hp]"; first by iFrame.
    (* re-render: CHECK with the Succ-phase body spec *)
    wp_pure.
    set (π5 := enter_view π4 <| vw_dec ::= dec_add_effect |>
                 <| vw_sttst ::= <[0:=StEntry (cint (n + 1 + 1)) []]> |>).
    set (s5 := VList [cint (n + 1 + 1); counter_handler 0 (n + 1 + 1) 0]).
    iApply (wp_check_component _ 0 π4 "x" counter_body _
              (λ π' s, (⌜π' = π5⌝ ∗ ⌜s = s5⌝ ∗ out_frag (ω ++ ω_click))%I)
              with "[Ho] Hm Hp Hr").
    { by rewrite lookup_insert_eq. }
    { done. }
    { done. }
    { iIntros (ks' Φ') "Hr Hk'".
      iApply (counter_body_succ_click 0 n n 0 with "Hr Ho").
      { by vm_compute. }
      iIntros "Hr Ho".
      iApply ("Hk'" $! s5 π5 with "[//] [Hr] [Ho]"); last by iFrame.
      (* the folded value differs from the committed one: Effect *)
      rewrite /commit_slot /val_eqb bool_decide_eq_false_2 //.
      intros [=]. lia. }
    iIntros (s π' _) "Hm Hp Hr (-> & -> & Ho)".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* reconcile the old child [n; h] against [n+2; h'] *)
    iEval (change (vw_child π4) with (vw_child (Π n))). unfold s5. cbn [vw_child Π].
    do 7 wp_pure.
    iApply (wp_check_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (t6 := TList [TConst (CInt (n + 1 + 1)); TClos "_" _ _]).
    set (π6 := π5 <| vw_child := t6 |>).
    (* rendered again: commit (no effects), check (idle), quiescent *)
    wp_pure.
    iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child π6) with t6; change (vw_effq π6) with (@nil domains.val)).
    unfold t6. do 5 wp_pure.
    iApply (wp_commit_finish_any with "Hm Hp");
      [by left|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    set (π7 := π6 <| vw_dec ::= dec_rm_effect |>).
    wp_pure.
    iApply (wp_check_idle with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm".
    iEval (change (vw_child π7) with t6). unfold t6.
    do 6 wp_pure.
    (* the quiescent view is [Π (n+1+1)] *)
    assert (π7 = Π (n + 1 + 1)) as ->
      by (subst π7 π6 π5 π4; vm_compute; reflexivity).
    iApply "Hk". by iFrame.
  Qed.

  (** *** Any click trace *)
  Lemma counter_run (evs : list nat) (n : Z) (ω : out_buf) :
    Forall (λ i, i = 0%nat) evs →
    I n ω -∗
    WP ((FIdle (TPath 0), [KEvents evs]) : expr (reactLang δ)) {{ w,
      ∃ m ω', mem_auth_frag m ∗ out_frag ω' ∗
        ⌜∃ t, w = MIdle t ∧
              display_t 1000 m t
                = Ok (DList [DConst (CInt (n + 2 * Z.of_nat (length evs))); DHandler]) ∧
              ω' = ω ++ concat (replicate (length evs) ω_click)⌝ }}.
  Proof.
    revert n ω. induction evs as [|i evs IH]; intros n ω Hall.
    - iIntros "(Hm & Hp & Hr & Ho)".
      iApply wp_events_done. iNext.
      iApply (wp_value' _ _ _ (MIdle (TPath 0))).
      iExists (<[0:=Π n]> ∅), ω. iFrame "Hm Ho". iPureIntro.
      exists (TPath 0). split_and!; [done| |by rewrite app_nil_r].
      rewrite display_Π. do 5 f_equal. simpl. lia.
    - inversion Hall as [|?? Hi Hall']; subst.
      iIntros "HI".
      iApply (counter_click_step with "HI").
      iIntros "HI".
      iApply (wp_wand with "[HI]"); first by iApply (IH with "HI").
      iIntros (w) "(%m & %ω' & Hm & Ho & %t & -> & %Hd & ->)".
      iExists m, _. iFrame. iPureIntro. exists t. split_and!; [done| |].
      + rewrite Hd. do 5 f_equal. simpl length. lia.
      + by rewrite /= -app_assoc.
  Qed.

  Lemma counter_trace_wp (evs : list nat) :
    Forall (λ i, i = 0%nat) evs →
    own_cfg (machine_init_cfg counter_prog evs) -∗
    WP (cfg_expr (machine_init_cfg counter_prog evs) : expr (reactLang δ)) {{ w,
      ∃ m ω, mem_auth_frag m ∗ out_frag ω ∗
        ⌜∃ t, w = MIdle t ∧
              display_t 1000 m t
                = Ok (DList [DConst (CInt (2 * Z.of_nat (length evs))); DHandler]) ∧
              ω = ω_mount ++ concat (replicate (length evs) ω_click)⌝ }}.
  Proof.
    iIntros (Hall) "Hown".
    iApply (counter_mount with "Hown"). iIntros "HI".
    iApply (wp_wand with "[HI]"); first by iApply (counter_run with "HI").
    iIntros (w) "(%m & %ω & Hm & Ho & %t & -> & %Hd & ->)".
    iExists m, _. iFrame. iPureIntro. exists t. split_and!; [done| |done].
    rewrite Hd. by do 5 f_equal.
  Qed.

  (** ** Counter as a refinement of an abstract LTS (component.v)

      Abstract states: integers; the only event is the click (index 0),
      which adds 2; the display shows the state. The three obligations are
      exactly [counter_mount], [counter_click_step], and [display_Π]. *)
  Definition counter_Inv (a : Z) (m : tree_mem) (ω : out_buf) : iProp Σ :=
    ⌜m = <[0 := Π a]> ∅⌝ ∗ I a ω.

  Lemma counter_root_obligations :
    ⊢ root_obligations δ counter_prog counter_lts counter_Inv.
  Proof.
    iSplit; [|iSplit].
    - iIntros "!>" (evs Φ) "Hown Hk".
      iApply (counter_mount with "Hown"). iIntros "HI".
      iApply ("Hk" $! 0 with "[//] [HI]"). by iFrame.
    - iIntros "!>" (a m ω i evs ks Φ Hi) "[%Hm HI] Hk". simpl in Hi; subst i.
      iApply (counter_click_step with "HI"). iIntros "HI".
      iApply ("Hk" $! (a + 1 + 1)%Z with "[%] [HI]"); [simpl; lia|by iFrame].
    - iIntros "!>" (a m ω) "[%Hm (Hm & _ & _ & Ho)]". subst m.
      iFrame. iPureIntro. apply display_Π.
  Qed.
End counter_modular.

(** All-zero traces are admissible. *)
Lemma counter_admissible (evs : list nat) (a : Z) :
  Forall (λ i, i = 0%nat) evs → rs_admissible counter_lts a evs.
Proof.
  revert a. induction evs as [|i evs IH]; intros a Hall; first constructor.
  inversion Hall; subst. constructor; first done.
  intros a' _. by apply IH.
Qed.

(** Counter refines its abstract LTS: for every click trace, the machine
    never gets stuck, and any reached value is quiescent in a reachable
    abstract state [a'] (here: [2·|evs|]) whose display is shown. *)
Corollary counter_root_adequate (evs : list nat) :
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
           (λ _ HR, @counter_Inv reactΣ HR)).
  { intros a _. by apply counter_admissible. }
  intros HI HR. apply counter_root_obligations.
Qed.

(** The top-level theorem, with no Iris in the statement: for every click
    trace, the machine never gets stuck (no Rules-of-React violation), and
    whenever it reaches a value the state is quiescent, the display shows
    twice the number of clicks, and the output is the mount output
    followed by one click output per click. *)
Corollary counter_trace_adequate (evs : list nat) :
  Forall (λ i, i = 0%nat) evs →
  adequate NotStuck
    (cfg_expr (machine_init_cfg counter_prog evs)
       : expr (reactLang (prog_def_table counter_prog)))
    (cfg_state (machine_init_cfg counter_prog evs))
    (λ w σ, ∃ t, w = MIdle t ∧
       display_t 1000 (ls_mem σ) t
         = Ok (DList [DConst (CInt (2 * Z.of_nat (length evs))); DHandler]) ∧
       ls_out σ = [VConst (CString "Counter"); VConst (CString "Return")] ++
                  concat (replicate (length evs)
                            [VConst (CString "Counter"); VConst (CString "Update");
                             VConst (CString "Return")])).
Proof.
  intros Hall.
  apply (react_adequacy_state reactΣ _ _
           (λ w m ω, ∃ t, w = MIdle t ∧
              display_t 1000 m t
                = Ok (DList [DConst (CInt (2 * Z.of_nat (length evs))); DHandler]) ∧
              ω = [VConst (CString "Counter"); VConst (CString "Return")] ++
                  concat (replicate (length evs)
                            [VConst (CString "Counter"); VConst (CString "Update");
                             VConst (CString "Return")]))).
  intros HI HR. by iApply counter_trace_wp.
Qed.

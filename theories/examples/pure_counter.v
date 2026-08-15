(** * A pure Counter in model form: callbacks are abstract transitions,
    the display is a function of the abstract state.

<<
let Counter x =
  let (s, setS) = useState x in
  [s, button (fun _ -> setS (fun s -> s + 1); setS (fun s -> s + 1))];;
>>

    Unlike the paper's Counter (tests.v), the updaters here are pure, so
    the model layer applies:

    - [click_model]: the handler takes [model γ (cint n)] to
      [model γ (cint (n+2))] — the specification of the callback as a
      transition of the abstract state, with the physical queueing of
      the two updaters as a side product;
    - [body_succ_model]: on re-render, from [model γ a] the body renders
      the view spec [[a; handler]] and leaves the model unchanged — the
      display is a function of the abstract state, and rendering does
      not change it.

    The paper's Counter, whose second updater prints, cannot enter the
    model layer: its queue is not pure, so [slot_res] cannot be
    established — [upd_pure] is where the user obligation bites. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime model.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Definition pure_counter_body : syntax.expr :=
  EUseState 0 "s" "setS" (EVar "x")
    (EView [EVar "s";
            EFun "_"
              (ESeq (EApp (EVar "setS") (EFun "s" (EBop BPlus (EVar "s") (EConst (CInt 1)))))
                    (EApp (EVar "setS") (EFun "s" (EBop BPlus (EVar "s") (EConst (CInt 1))))))]).

Section pure_counter.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Local Notation "'cint' n" := (VConst (CInt n)) (at level 10).

  Definition finc (v : domains.val) : domains.val :=
    match v with VConst (CInt n) => VConst (CInt (n + 1)) | _ => v end.

  Lemma finc_int v : is_int v → is_int (finc v).
  Proof. intros [n ->]. by exists (n + 1)%Z. Qed.

  Lemma upd_pure_inc σ :
    ⊢ upd_pure δ is_int (VClos "s" (EBop BPlus (EVar "s") (EConst (CInt 1))) σ) finc.
  Proof.
    iIntros "!>" (v ks Φ [n ->]) "Hwp".
    do 5 wp_pure. by iApply "Hwp".
  Qed.

  (** The handler closure rendered at state [ns] (argument [nx]). *)
  Definition handler (p : path) (ns nx : Z) : domains.val :=
    VClos "_"
      (ESeq (EApp (EVar "setS") (EFun "s" (EBop BPlus (EVar "s") (EConst (CInt 1)))))
            (EApp (EVar "setS") (EFun "s" (EBop BPlus (EVar "s") (EConst (CInt 1))))))
      (env_insert "setS" (VSetter 0 p) (env_insert "s" (cint ns) [("x", cint nx)])).

  (** ** The callback as an abstract transition: +2 *)
  Lemma click_model γ (n ns nx : Z) p π ent m ks Φ :
    m !! p = Some π →
    vw_sttst π !! 0 = Some ent →
    model γ (cint n) -∗ slot_res δ is_int γ ent -∗
    mem_auth_frag m -∗ view_ptsto p π -∗ reg_token None -∗
    (∀ π' ent', model γ (cint (n + 1 + 1)) -∗ slot_res δ is_int γ ent' -∗
       mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
       WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PNormal (env_insert "_" (VConst CUnit)
                          (env_insert "setS" (VSetter 0 p)
                             (env_insert "s" (cint ns) [("x", cint nx)])))
           (ESeq (EApp (EVar "setS") (EFun "s" (EBop BPlus (EVar "s") (EConst (CInt 1)))))
                 (EApp (EVar "setS") (EFun "s" (EBop BPlus (EVar "s") (EConst (CInt 1)))))),
         ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hl) "Hm Hs Hmem Hv Hr Hwp".
    do 5 wp_pure.
    iApply (wp_setter_normal_model _ is_int γ (cint n) finc with "[] Hm Hs Hmem Hv Hr");
      [done|done|apply finc_int|iApply upd_pure_inc|].
    iNext. iIntros "Hm Hs Hmem Hv Hr".
    do 5 wp_pure.
    iApply (wp_setter_normal_model _ is_int γ _ finc with "[] Hm Hs Hmem Hv Hr");
      [by rewrite lookup_insert_eq|by rewrite lookup_insert_eq|apply finc_int
      |iApply upd_pure_inc|].
    iNext. iIntros "Hm Hs Hmem Hv Hr".
    iEval (rewrite insert_insert_eq) in "Hmem".
    iApply ("Hwp" with "Hm Hs Hmem Hv Hr").
  Qed.

  (** ** The display as a function of the abstract state *)
  Lemma body_succ_model γ (a : domains.val) (nx : Z) p π ent ks Φ :
    vw_sttst π !! 0 = Some ent →
    model γ a -∗ slot_res δ is_int γ ent -∗ render_ctx p π -∗
    (∀ n, ⌜a = cint n⌝ -∗
       model γ a -∗ slot_res δ is_int γ (StEntry a []) -∗
       render_ctx p (commit_slot π 0 (st_val ent) a) -∗
       WP ((FVal (VList [a; handler p n nx]), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc [("x", cint nx)] pure_counter_body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl) "Hm Hs Hr Hwp".
    rewrite /pure_counter_body.
    iApply (wp_usestate_succ_model with "Hm Hs Hr"); first done.
    iIntros "Hm Hs Hr".
    iDestruct "Hs" as "(%fs & %HD & Hq & Hγ)". simpl in HD. destruct HD as [n ->].
    iAssert (slot_res δ is_int γ (StEntry (cint n) []))
      with "[Hq Hγ]" as "Hs".
    { iExists fs. iFrame. iPureIntro. by exists n. }
    do 5 wp_pure.
    by iApply ("Hwp" $! n with "[//] Hm Hs Hr").
  Qed.
End pure_counter.

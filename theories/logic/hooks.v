(** * Hook layer: render context, updater purity, derived useState /
    useEffect / setter rules.

    This is the first M3 layer on top of the redex rules:

    - [render_ctx p π] names the view under construction (the render
      register); hook rules are stated on it.

    - [upd_pure D cl f] — the user obligation behind [useState]: the
      updater closure [cl] computes the meta-function [f] on the domain
      [D] *without touching any state*. It is expressed as a
      resource-free WP implication: no [reg_token] / [mem_auth_frag] /
      [out_frag] is available inside, and every state-changing step of
      the machine needs one of them, so only state-preserving evaluation
      can satisfy it. Printing or calling a setter inside an updater is
      thereby excluded — the logical form of the paper's Def. 3.

    - [wp_usestate_succ_pure] — STTREBIND for a pure queue: the value
      bound on re-render is the mathematical fold of the queued
      functions over the committed value, the queue is flushed, and the
      Effect decision appears iff the value changed. Together with
      [wp_usestate_mount] (STTBIND) these are the useState rules of
      design.md §5.1; the purity premise is where "why must updaters be
      pure" shows up as a proof obligation.

    - [wp_setter_normal] — APPSETNORMAL: outside rendering, calling a
      setter enqueues the updater on the target view and turns on its
      Check decision (a memory-touching rule; the machine-level content
      of the "callbacks are abstract transitions" story).

    The paper's Counter is verified from these rules alone in
    [examples/counter_modular.v]. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** Symbolic execution of state-free steps: the successor is computed
    by [cbn] on [mstep]. *)
Ltac wp_pure :=
  iApply (wp_pure_step _ _ (_, _));
  [ done | intros ?; cbn; reflexivity | iNext ].

Section hooks.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Implicit Types Φ : mval → iProp Σ.

  (** ** Render context *)
  Definition render_ctx (p : path) (π : domains.view) : iProp Σ :=
    reg_token (Some (p, π)).

  (** ** Updater purity *)

  (** [f] realizes the closure [cl] on domain [D], with no effect on any
      state (see the header). *)
  Definition upd_pure (D : domains.val → Prop) (cl : domains.val)
      (f : domains.val → domains.val) : iProp Σ :=
    match cl with
    | VClos x e σ =>
        □ ∀ (v : domains.val) ks Φ, ⌜D v⌝ -∗
            WP ((FVal (f v), ks) : expr (reactLang δ)) {{ Φ }} -∗
            WP ((FExpr PSucc (env_insert x v σ) e, ks) : expr (reactLang δ)) {{ Φ }}
    | _ => False
    end.

  Global Instance upd_pure_persistent D cl f : Persistent (upd_pure D cl f).
  Proof. destruct cl; apply _. Qed.

  (** A queue of updaters realized by a list of functions, all preserving
      the domain. *)
  Definition queue_pure (D : domains.val → Prop) (q : list domains.val)
      (fs : list (domains.val → domains.val)) : iProp Σ :=
    ⌜Forall (λ f, ∀ v, D v → D (f v)) fs⌝ ∗
    [∗ list] cl;f ∈ q;fs, upd_pure D cl f.

  Global Instance queue_pure_persistent D q fs : Persistent (queue_pure D q fs).
  Proof. apply _. Qed.

  (** A common domain for updaters: integer values. *)
  Definition is_int (v : domains.val) : Prop := ∃ n : Z, v = VConst (CInt n).

  Fixpoint fold_upd (fs : list (domains.val → domains.val))
      (v : domains.val) : domains.val :=
    match fs with [] => v | f :: fs' => fold_upd fs' (f v) end.

  Lemma fold_upd_dom (D : domains.val → Prop)
      (fs : list (domains.val → domains.val)) (v : domains.val) :
    Forall (λ f, ∀ v, D v → D (f v)) fs → D v → D (fold_upd fs v).
  Proof.
    revert v. induction fs as [|f fs IH]; intros v Hall Hv; first done.
    inversion Hall; subst. apply IH; auto.
  Qed.

  Local Lemma set_dec_id (π : domains.view) : π <| vw_dec := vw_dec π |> = π.
  Proof. by destruct π. Qed.

  (** The view after committing the folded value [vn] over [v0] at
      slot [l] (and advancing the cursor past it). *)
  Definition commit_slot (π : domains.view) (l : label) (v0 vn : domains.val)
      : domains.view :=
    π <| vw_dec := (if val_eqb vn v0 then vw_dec π else dec_add_effect (vw_dec π)) |>
      <| vw_sttst ::= insert l (StEntry vn []) |>
      <| vw_hook_cursor := S l |>.

  (** Folding a pure queue through the [KSttFold] frame. *)
  Lemma wp_sttfold_pure (D : domains.val → Prop) (v : domains.val) (σb : env)
      (l : label) (x xset : var) (e2 : syntax.expr) (v0 : domains.val)
      (q : list domains.val) (fs : list (domains.val → domains.val))
      (p : path) (π : domains.view) (ks : list machine.frame) Φ :
    D v →
    queue_pure D q fs -∗
    render_ctx p π -∗
    (render_ctx p (commit_slot π l v0 (fold_upd fs v)) -∗
     WP ((FExpr PSucc (env_insert xset (VSetter l p)
                        (env_insert x (fold_upd fs v) σb)) e2, ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KSttFold σb l x xset e2 v0 q :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (HD) "[%Hdom Hq] Hr Hwp".
    iInduction q as [|cl q IH] "IH" forall (v fs HD Hdom).
    - iDestruct (big_sepL2_nil_inv_l with "Hq") as %->. cbn.
      iApply (wp_sttfold_nil with "Hr"). iNext. iIntros "Hr".
      by iApply "Hwp".
    - iDestruct (big_sepL2_cons_inv_l with "Hq") as (f fs' ->) "[Hcl Hq]".
      inversion Hdom; subst. cbn.
      destruct cl as [| xi ei σi | | | |]; try done.
      iApply (wp_sttfold_cons with "Hr"). iNext. iIntros "Hr".
      iApply ("Hcl" with "[//]").
      iApply ("IH" $! (f v) fs' with "[%] [//] Hq Hr Hwp"). by apply H1.
  Qed.

  (** ** Derived useState rules *)

  (** STTBIND (Init): the initial value [v] is bound, the slot is
      allocated, and the setter closure is bound. The initial-value
      expression is evaluated by the client through [wp_fill] on the
      [KUseState] frame; this rule covers the common case of an
      already-evaluated initial value. *)
  Lemma wp_usestate_mount (v : domains.val) (σb : env) (x xset : var)
      (e2 : syntax.expr) (p : path) (π : domains.view)
      (ks : list machine.frame) Φ :
    render_ctx p π -∗
    ▷ (render_ctx p (π <| vw_sttst ::= insert (vw_hook_cursor π) (StEntry v []) |>
                       <| vw_hook_cursor := S (vw_hook_cursor π) |>) -∗
       WP ((FExpr PInit (env_insert xset (VSetter (vw_hook_cursor π) p) (env_insert x v σb)) e2,
            ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KUseState σb x xset e2 :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_usestate_bind. Qed.

  (** STTREBIND (Succ) with a pure queue: the re-render sees the fold of
      the queued functions over the committed value; the queue is
      flushed; Effect iff the value changed. *)
  Lemma wp_usestate_succ_pure (D : domains.val → Prop) (x xset : var)
      (e1 e2 : syntax.expr) (σb : env) (p : path)
      (π : domains.view) (v0 : domains.val) (q : list domains.val)
      (fs : list (domains.val → domains.val)) (ks : list machine.frame) Φ :
    vw_sttst π !! vw_hook_cursor π = Some (StEntry v0 q) →
    D v0 →
    queue_pure D q fs -∗
    render_ctx p π -∗
    (render_ctx p (commit_slot π (vw_hook_cursor π) v0 (fold_upd fs v0)) -∗
     WP ((FExpr PSucc (env_insert xset (VSetter (vw_hook_cursor π) p)
                        (env_insert x (fold_upd fs v0) σb)) e2, ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc σb (EUseState x xset e1 e2), ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl HD) "[%Hdom #Hq] Hr Hwp".
    destruct q as [|cl q'].
    - iDestruct (big_sepL2_nil_inv_l with "Hq") as %->. cbn.
      iApply (wp_usestate_succ_nil with "Hr"); first done.
      iNext. iIntros "Hr". iApply "Hwp".
      rewrite /commit_slot /val_eqb bool_decide_eq_true_2 // set_dec_id //.
    - iDestruct (big_sepL2_cons_inv_l with "Hq") as (f fs' ->) "[Hcl Hq']".
      inversion Hdom; subst.
      destruct cl as [| xi ei σi | | | |]; try done.
      iApply (wp_usestate_succ_cons with "Hr"); first done.
      iNext. iIntros "Hr".
      iApply ("Hcl" with "[//]").
      iApply (wp_sttfold_pure D (f v0) _ _ _ _ _ _ q' fs' with "[] Hr Hwp");
        first by apply H1.
      iSplit; [done|iApply "Hq'"].
  Qed.

  (** ** Setter outside rendering (APPSETNORMAL) *)
  Lemma wp_setter_normal (l : label) (p' : path) (π : domains.view)
      (ent : st_entry) (xi : var) (ei : syntax.expr) (σi : env)
      (m : tree_mem) (ks : list machine.frame) Φ :
    m !! p' = Some π →
    vw_sttst π !! l = Some ent →
    mem_auth_frag m -∗ view_ptsto p' π -∗ reg_token None -∗
    ▷ (let π' := π <| vw_dec ::= dec_add_check |>
                   <| vw_sttst ::=
                        insert l (ent <| st_queue ::=
                                          (λ q, q ++ [VClos xi ei σi]) |>) |> in
       mem_auth_frag (<[p':=π']> m) -∗ view_ptsto p' π' -∗ reg_token None -∗
       WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal (VClos xi ei σi), KAppR PNormal (VSetter l p') :: ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hl). iApply wp_mem_write_step; first done.
    intros ω. cbn. rewrite Hp /view_enqueue Hl. done.
  Qed.

End hooks.

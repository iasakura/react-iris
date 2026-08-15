(** * Model layer: logical values of hook slots.

    Design decision D4, first instalment. A hook slot's *logical value*
    is the fold of its (pure) update queue over its committed value —
    what the next render will see. We give it a ghost variable:

    - [model γ a] — the client's half: "the logical value of the slot is
      [a]". This is what component specifications talk about ("the
      display is a function of [a]", "the callback takes [a] to
      [f a]").
    - [slot_res D γ ent] — the runtime's half, tied to the physical slot
      entry [ent]: the queue is pure (realized by functions [fs]) and the
      ghost variable holds [fold fs (committed value)].

    Rules:
    - [slot_alloc]: mounting a hook allocates a model;
    - [wp_setter_normal_model]: a setter call with a pure updater [f]
      takes [model γ a] to [model γ (f a)] — the abstract transition —
      while enqueuing [f] physically;
    - [wp_usestate_succ_model]: on re-render the hook binds exactly the
      logical value [a], commits it, flushes the queue, and the model is
      unchanged (rendering never changes the logical state); the Effect
      decision appears iff [a] differs from the previously committed
      value.

    The purity obligation ([upd_pure]) is exactly what makes the fold —
    and hence [model] — well defined; an impure updater (e.g. the
    printing one of the paper's Counter) cannot enter [slot_res]. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section model.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Implicit Types Φ : mval → iProp Σ.

  Definition model (γ : gname) (a : domains.val) : iProp Σ := ghost_var γ (1/2) a.

  Definition slot_res (D : domains.val → Prop) (γ : gname) (ent : st_entry) : iProp Σ :=
    ∃ fs, ⌜D (st_val ent)⌝ ∗ queue_pure δ D (st_queue ent) fs ∗
          ghost_var γ (1/2) (fold_upd fs (st_val ent)).

  Lemma fold_upd_app fs1 fs2 v :
    fold_upd (fs1 ++ fs2) v = fold_upd fs2 (fold_upd fs1 v).
  Proof. revert v. induction fs1; intros; simpl; auto. Qed.

  (** Mounting a slot at [v] allocates its model. *)
  Lemma slot_alloc D v :
    D v → ⊢ |==> ∃ γ, model γ v ∗ slot_res D γ (StEntry v []).
  Proof.
    iIntros (HD).
    iMod (ghost_var_alloc v) as (γ) "Hγ".
    iEval (rewrite -Qp.half_half) in "Hγ".
    iDestruct (ghost_var_split with "Hγ") as "[H1 H2]".
    iModIntro. iExists γ. iFrame "H1".
    iExists []. iFrame "H2". iSplit; first done.
    iSplit; [iPureIntro; constructor|done].
  Qed.

  (** With an empty queue the model is the committed value. *)
  Lemma model_committed D γ a v :
    model γ a -∗ slot_res D γ (StEntry v []) -∗ ⌜a = v⌝.
  Proof.
    iIntros "Hm (%fs & _ & [_ Hq] & Hγ)".
    iDestruct (big_sepL2_nil_inv_l with "Hq") as %->.
    by iDestruct (ghost_var_agree with "Hm Hγ") as %->.
  Qed.

  (** Enqueuing a pure updater advances the model. *)
  Lemma slot_enqueue D γ a ent cl f :
    (∀ v, D v → D (f v)) →
    upd_pure δ D cl f -∗ model γ a -∗ slot_res D γ ent ==∗
    model γ (f a) ∗ slot_res D γ (ent <| st_queue ::= (λ q, q ++ [cl]) |>).
  Proof.
    iIntros (Hf) "Hcl Hm (%fs & %HD & [%Hdom Hq] & Hγ)".
    iDestruct (ghost_var_agree with "Hm Hγ") as %->.
    iMod (ghost_var_update_halves (f (fold_upd fs (st_val ent))) with "Hm Hγ")
      as "[Hm Hγ]".
    iModIntro. iFrame "Hm". iExists (fs ++ [f]). destruct ent; simpl.
    rewrite fold_upd_app /=. iFrame "Hγ". iSplit; first done.
    iSplit.
    - iPureIntro. apply Forall_app; split; [done|by constructor].
    - iApply (big_sepL2_app with "Hq"). by iSplit.
  Qed.

  (** ** Setter outside rendering, in model form (APPSETNORMAL) *)
  Lemma wp_setter_normal_model D γ a f l p' π ent xi ei σi m ks Φ :
    m !! p' = Some π →
    vw_sttst π !! l = Some ent →
    (∀ v, D v → D (f v)) →
    upd_pure δ D (VClos xi ei σi) f -∗
    model γ a -∗ slot_res D γ ent -∗
    mem_auth_frag m -∗ view_ptsto p' π -∗ reg_token None -∗
    ▷ (let ent' := ent <| st_queue ::= (λ q, q ++ [VClos xi ei σi]) |> in
       let π' := π <| vw_dec ::= dec_add_check |> <| vw_sttst ::= insert l ent' |> in
       model γ (f a) -∗ slot_res D γ ent' -∗
       mem_auth_frag (<[p':=π']> m) -∗ view_ptsto p' π' -∗ reg_token None -∗
       WP ((FVal (VConst CUnit), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal (VClos xi ei σi), KAppR PNormal (VSetter l p') :: ks)
        : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hl Hf) "Hcl Hm Hs Hmem Hv Hr Hwp".
    iMod (slot_enqueue with "Hcl Hm Hs") as "[Hm Hs]"; first done.
    iApply (wp_setter_normal with "Hmem Hv Hr"); [done|done|].
    iNext. iIntros "Hmem Hv Hr".
    by iApply ("Hwp" with "Hm Hs Hmem Hv Hr").
  Qed.

  (** ** useState on re-render, in model form (STTREBIND) *)
  Lemma wp_usestate_succ_model D γ a l x xset e1 e2 σb p π ent ks Φ :
    vw_sttst π !! l = Some ent →
    model γ a -∗ slot_res D γ ent -∗
    render_ctx p π -∗
    (model γ a -∗ slot_res D γ (StEntry a []) -∗
     render_ctx p (commit_slot π l (st_val ent) a) -∗
     WP ((FExpr PSucc (env_insert xset (VSetter l p) (env_insert x a σb)) e2, ks)
         : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FExpr PSucc σb (EUseState l x xset e1 e2), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hl) "Hm (%fs & %HD & #Hq & Hγ) Hr Hwp".
    iDestruct (ghost_var_agree with "Hm Hγ") as %->.
    destruct ent as [v0 q]; simpl in *.
    iPoseProof "Hq" as "[%Hdom _]".
    iApply (wp_usestate_succ_pure with "Hq Hr"); [done|done|].
    iIntros "Hr".
    iApply ("Hwp" with "Hm [Hγ] Hr").
    iExists []. iFrame "Hγ". iSplit.
    { iPureIntro. simpl. by apply fold_upd_dom. }
    iSplit; [iPureIntro; constructor|done].
  Qed.

  (** ** useState on mount, in model form (STTBIND) *)
  Lemma wp_usestate_mount_model D v σb l x xset e2 p π ks Φ :
    D v →
    render_ctx p π -∗
    ▷ (∀ γ, model γ v -∗ slot_res D γ (StEntry v []) -∗
       render_ctx p (π <| vw_sttst ::= insert l (StEntry v []) |>) -∗
       WP ((FExpr PInit (env_insert xset (VSetter l p) (env_insert x v σb)) e2,
            ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FVal v, KUseState σb l x xset e2 :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (HD) "Hr Hwp".
    iMod (slot_alloc D v HD) as (γ) "[Hm Hs]".
    iApply (wp_usestate_mount with "Hr"). iNext. iIntros "Hr".
    by iApply ("Hwp" with "Hm Hs Hr").
  Qed.
End model.

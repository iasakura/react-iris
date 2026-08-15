(** * Runtime lemmas: mounting, checking, and committing a component,
    parameterized by specifications of its body and effects.

    The redex rules ([step_rules.v], [runtime_rules.v]) execute one step
    each. This file packages the recurring multi-step patterns of the
    runtime "once", in continuation-passing style, so that a component
    proof only supplies specifications of its own code:

    - [wp_init_component]: INITCOM up to the point where the settled view
      is mounted and the child view spec is about to be initialized;
    - [wp_check_component]: CHECK* up to the write-back, branching on the
      Effect decision (reconcile the child / keep checking below);
    - [wp_commit_effects]: running an effect queue in Normal phase with a
      client-chosen resource threaded through the effect specs;
    - [wp_event_dispatch] / [wp_events_done]: the event driver.

    Body specifications are stated in the same CPS shape as the rules:
    "from the render context, the body evaluates to a value and a
    settled view, and the continuation is invoked with them". The
    settled view carries no Check decision (no own-setter call during
    the last round); bodies that retry are handled by [wp_retry_again]
    at the rule level and can be packaged later with a measure (D3). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section runtime.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Implicit Types Φ : mval → iProp Σ.

  (** ** Event driver *)

  (** STEPEVENT: dispatch the [i]-th handler of the quiescent tree. *)
  Lemma wp_event_dispatch t i evs hs x e σ m ks Φ :
    handlers_of m t = Ok hs →
    hs !! i = Some (VClos x e σ) →
    mem_auth_frag m -∗
    ▷ (mem_auth_frag m -∗
       WP ((FExpr PNormal (env_insert x (VConst CUnit) σ) e,
            KPostEvent t :: KEvents evs :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FIdle t, KEvents (i :: evs) :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hhs Hi). iApply wp_mem_read_step; first done.
    intros r ω. cbn. by rewrite Hhs /= Hi.
  Qed.

  (** Trace exhausted: pop the driver frame. *)
  Lemma wp_events_done t ks Φ :
    ▷ WP ((FIdle t, ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FIdle t, KEvents [] :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. iApply wp_pure_step; [done|by intros]. Qed.

  (** ** Body specifications (CPS) *)

  (** [body_spec φ p π0 σ body Ψ]: in phase [φ], from the render context
      [π0], the body evaluates to a view spec [s] leaving a settled view
      [π'] (no Check decision), and [Ψ π' s] holds. *)
  Definition body_spec (φ : phase) (p : path) (π0 : domains.view) (σ : env)
      (body : syntax.expr) (Ψ : domains.view → domains.val → iProp Σ) : iProp Σ :=
    ∀ ks Φ,
      render_ctx p π0 -∗
      (∀ s π', ⌜dec_check (vw_dec π') = false⌝ -∗
               render_ctx p π' -∗ Ψ π' s -∗
               WP ((FVal s, ks) : expr (reactLang δ)) {{ Φ }}) -∗
      WP ((FExpr φ σ body, ks) : expr (reactLang δ)) {{ Φ }}.

  (** The register content on body entry (Fig. 6, round entry). *)
  Definition enter_view (π : domains.view) : domains.view :=
    π <| vw_dec ::= dec_rm_check |> <| vw_effq := [] |>.

  (** Running a body through the retry frame, single round. *)
  Lemma wp_body_once φ p π σ body Ψ ks Φ :
    body_spec φ p (enter_view π) σ body Ψ -∗
    reg_token None -∗
    (∀ s π', ⌜dec_check (vw_dec π') = false⌝ -∗
             render_ctx p π' -∗ Ψ π' s -∗
             WP ((FVal s, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FBody φ p π σ body, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "Hbody Hr Hk".
    iApply (wp_body_enter with "Hr"). iNext. iIntros "Hr".
    iApply ("Hbody" with "Hr"). iIntros (s π' Hc) "Hr HΨ".
    iApply (wp_retry_done with "Hr"); first done. iNext. iIntros "Hr".
    by iApply ("Hk" with "[//] Hr HΨ").
  Qed.

  (** ** Mounting a component (INITCOM) *)

  (** From [FInit ⟨C, v⟩]: allocate the fresh path [p], run the body in
      Init phase, mount the settled view at [p], and hand over the child
      view spec [s] for initialization ([KInitChild p] on the stack;
      [wp_init_finish] completes once the child tree returns). *)
  Lemma wp_init_component C v x body m Ψ ks Φ :
    δ !! C = Some (CompDef x body) →
    body_spec PInit (fresh_path m)
      (enter_view (MkView C v dec_empty ∅ [] (TConst CUnit))) [(x, v)] body Ψ -∗
    mem_auth_frag m -∗ reg_token None -∗
    (∀ s π', ⌜dec_check (vw_dec π') = false⌝ -∗
             mem_auth_frag (<[fresh_path m := π']> m) -∗
             view_ptsto (fresh_path m) π' -∗ reg_token None -∗ Ψ π' s -∗
             WP ((FInit s, KInitChild (fresh_path m) :: ks)
                 : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FInit (VCompSpec C v), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (HC) "Hbody Hm Hr Hk".
    iApply (wp_init_comp with "Hm"); first done. iNext. iIntros "Hm".
    iApply (wp_body_once with "Hbody Hr").
    iIntros (s π' Hc) "Hr HΨ".
    iApply (wp_mount with "Hm Hr"); first apply fresh_path_fresh.
    iNext. iIntros "Hm Hp Hr".
    by iApply ("Hk" with "[//] Hm Hp Hr HΨ").
  Qed.

  (** ** Checking a component (CHECKEFFECT / CHECKNOEFFECT) *)

  (** From [FCheck (TPath p)] on a view with the Check decision: run the
      body in Succ phase, write back, then either reconcile the old child
      against the new view spec (Effect: state changed) or keep checking
      below (no Effect). *)
  Lemma wp_check_component p π x body m Ψ ks Φ :
    m !! p = Some π →
    dec_check (vw_dec π) = true →
    δ !! vw_comp π = Some (CompDef x body) →
    body_spec PSucc p (enter_view π) [(x, vw_arg π)] body Ψ -∗
    mem_auth_frag m -∗ view_ptsto p π -∗ reg_token None -∗
    (∀ s π', ⌜dec_check (vw_dec π') = false⌝ -∗
             mem_auth_frag (<[p:=π']> m) -∗ view_ptsto p π' -∗ reg_token None -∗
             Ψ π' s -∗
             (if dec_effect (vw_dec π') then
                WP ((FRecon (vw_child π) s, KCheckRecon p :: ks)
                    : expr (reactLang δ)) {{ Φ }}
              else
                WP ((FCheck (vw_child π), ks) : expr (reactLang δ)) {{ Φ }})) -∗
    WP ((FCheck (TPath p), ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hp Hc Hδ) "Hbody Hm Hv Hr Hk".
    iApply (wp_check_enter with "Hm"); [done|done|done|]. iNext. iIntros "Hm".
    iApply (wp_body_once with "Hbody Hr").
    iIntros (s π' Hc') "Hr HΨ".
    destruct (dec_effect (vw_dec π')) eqn:He.
    - iApply (wp_check_writeback_eff with "Hm Hv Hr"); first done.
      iNext. iIntros "Hm Hv Hr".
      iSpecialize ("Hk" with "[//] Hm Hv Hr HΨ"). by rewrite He.
    - iApply (wp_check_writeback_noeff with "Hm Hv Hr"); first done.
      iNext. iIntros "Hm Hv Hr".
      iSpecialize ("Hk" with "[//] Hm Hv Hr HΨ"). by rewrite He.
  Qed.

  (** ** Running an effect queue (COMMITEFFSPATH, after the child) *)

  (** [effect_spec S cl]: the effect thunk [cl], run in Normal phase, takes
      the resource [S] to [S] again (a client-chosen frame threaded through
      the queue, e.g. ownership of the memory and the views it updates). *)
  Definition effect_spec (S : iProp Σ) (cl : domains.val) : iProp Σ :=
    match cl with
    | VClos _ e σ =>
        ∀ ks Φ, S -∗ (∀ v, S -∗ WP ((FVal v, ks) : expr (reactLang δ)) {{ Φ }}) -∗
                WP ((FExpr PNormal σ e, ks) : expr (reactLang δ)) {{ Φ }}
    | _ => False
    end.

  (** The two return foci that reach a [KCommitEffs] frame: [FUnit]
      (after the child commit) and [FVal v] (after an effect). *)
  Definition commit_ret (f : focus) : Prop := f = FUnit ∨ ∃ v, f = FVal v.

  Lemma wp_commit_effects S p q f ks Φ :
    commit_ret f →
    ([∗ list] cl ∈ q, effect_spec S cl) -∗
    S -∗
    (∀ f', ⌜commit_ret f'⌝ -∗ S -∗
           WP ((f', KCommitEffs p [] :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((f, KCommitEffs p q :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hf) "Hq HS Hk".
    iInduction q as [|cl q IH] "IH" forall (f Hf).
    - by iApply ("Hk" with "[//] HS").
    - iDestruct "Hq" as "[Hcl Hq]".
      destruct cl as [| xi ei σi | | | |]; try done.
      iApply (wp_pure_step _ _ (FExpr PNormal σi ei, KCommitEffs p q :: ks)).
      { by destruct Hf as [-> | [v ->]]. }
      { intros σ. by destruct Hf as [-> | [v ->]]. }
      iNext.
      iApply ("Hcl" with "HS"). iIntros (v) "HS".
      iApply ("IH" $! (FVal v) with "[%] Hq HS Hk"). by right; eexists.
  Qed.

  (** Clearing the Effect decision from either return focus. *)
  Lemma wp_commit_finish_any f p π m ks Φ :
    commit_ret f →
    m !! p = Some π →
    mem_auth_frag m -∗ view_ptsto p π -∗
    ▷ (mem_auth_frag (<[p := π <| vw_dec ::= dec_rm_effect |>]> m) -∗
       view_ptsto p (π <| vw_dec ::= dec_rm_effect |>) -∗
       WP ((FUnit, ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((f, KCommitEffs p [] :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    intros [-> | [v ->]] Hp.
    - by iApply wp_commit_finish_u.
    - by iApply wp_commit_finish_v.
  Qed.

End runtime.

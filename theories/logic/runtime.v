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
  Lemma wp_event_dispatch (t : tree) (i : nat) (evs : list nat)
      (hs : list domains.val) (x : var) (e : syntax.expr) (σ : env)
      (m : tree_mem) (ks : list machine.frame) Φ :
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
  Lemma wp_events_done (t : tree) (ks : list machine.frame) Φ :
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
  Lemma wp_body_once (φ : phase) (p : path) (π : domains.view) (σ : env)
      (body : syntax.expr) (Ψ : domains.view → domains.val → iProp Σ)
      (ks : list machine.frame) Φ :
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
  Lemma wp_init_component (C : comp_name) (v : domains.val) (x : var)
      (body : syntax.expr) (m : tree_mem)
      (Ψ : domains.view → domains.val → iProp Σ)
      (ks : list machine.frame) Φ :
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
  Lemma wp_check_component (p : path) (π : domains.view) (x : var)
      (body : syntax.expr) (m : tree_mem)
      (Ψ : domains.view → domains.val → iProp Σ)
      (ks : list machine.frame) Φ :
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

  (** [effect_spec S S' cl]: the effect thunk [cl], run in Normal phase,
      takes the resource [S] to [S'] (client-chosen frames, e.g. ownership
      of the memory and the views the effect updates through setters, and
      the output). *)
  Definition effect_spec (S S' : iProp Σ) (cl : domains.val) : iProp Σ :=
    match cl with
    | VClos _ e σ =>
        ∀ ks Φ, S -∗ (∀ v, S' -∗ WP ((FVal v, ks) : expr (reactLang δ)) {{ Φ }}) -∗
                WP ((FExpr PNormal σ e, ks) : expr (reactLang δ)) {{ Φ }}
    | _ => False
    end.

  (** The two return foci that reach a [KCommitEffs] frame: [FUnit]
      (after the child commit) and [FVal v] (after an effect). *)
  Definition commit_ret (f : focus) : Prop := f = FUnit ∨ ∃ v, f = FVal v.

  (** Running an effect queue: the [i]-th effect takes [Ss i] to
      [Ss (i+1)]; the whole queue takes [Ss 0] to [Ss (length q)]. *)
  Lemma wp_commit_effects (Ss : nat → iProp Σ) (p : path)
      (q : list domains.val) (f : focus) (ks : list machine.frame) Φ :
    commit_ret f →
    ([∗ list] i ↦ cl ∈ q, effect_spec (Ss i) (Ss (S i)) cl) -∗
    Ss 0 -∗
    (∀ f', ⌜commit_ret f'⌝ -∗ Ss (length q) -∗
           WP ((f', KCommitEffs p [] :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((f, KCommitEffs p q :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hf) "Hq HS Hk".
    iInduction q as [|cl q IH] "IH" forall (Ss f Hf).
    - by iApply ("Hk" with "[//] HS").
    - iDestruct "Hq" as "[Hcl Hq]".
      destruct cl as [| xi ei σi | | | |]; try done.
      iApply (wp_pure_step _ _ (FExpr PNormal σi ei, KCommitEffs p q :: ks)).
      { by destruct Hf as [-> | [v ->]]. }
      { intros σ. by destruct Hf as [-> | [v ->]]. }
      iNext.
      iApply ("Hcl" with "HS"). iIntros (v) "HS".
      iApply ("IH" $! (λ i, Ss (S i)) (FVal v) with "[%] Hq HS [Hk]").
      { by right; eexists. }
      iIntros (f' Hf') "HS". by iApply ("Hk" with "[//] HS").
  Qed.

  (** Clearing the Effect decision from either return focus. *)
  Lemma wp_commit_finish_any (f : focus) (p : path) (π : domains.view)
      (m : tree_mem) (ks : list machine.frame) Φ :
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

(** ** Path-free subtrees

    Children that contain no component (no [TPath]) are committed and
    checked without touching the state, and a component-free view spec is
    initialized / reconciled to the tree it denotes, all in pure steps.
    These lemmas replace step counting for constant / closure / list
    children in component proofs. *)
Section pure_subtrees.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Implicit Types Φ : mval → iProp Σ.

  Fixpoint tree_size (t : tree) : nat :=
    match t with
    | TList ts => S (list_sum (map tree_size ts))
    | _ => 1
    end.

  Fixpoint val_size (v : domains.val) : nat :=
    match v with
    | VList vs => S (list_sum (map val_size vs))
    | _ => 1
    end.

  (** Trees without paths. *)
  Fixpoint path_free (t : tree) : Prop :=
    match t with
    | TConst _ | TClos _ _ _ => True
    | TList ts => Forall id (map path_free ts)
    | TPath _ => False
    end.

  (** View specs without components, and the trees they denote. *)
  Fixpoint spec_free (s : domains.val) : Prop :=
    match s with
    | VConst _ | VClos _ _ _ => True
    | VList ss => Forall id (map spec_free ss)
    | _ => False
    end.

  Fixpoint tree_of (s : domains.val) : tree :=
    match s with
    | VConst k => TConst k
    | VClos x e σ => TClos x e σ
    | VList ss => TList (map tree_of ss)
    | _ => TConst CUnit
    end.

  Local Lemma list_sum_elem (t : tree) (ts : list tree) :
    t ∈ ts → tree_size t ≤ list_sum (map tree_size ts).
  Proof.
    induction ts as [|t' ts IH]; intros Hin; first by inversion Hin.
    inversion Hin; subst; simpl; [lia|]. specialize (IH H1). lia.
  Qed.

  Local Lemma val_sum_elem (v : domains.val) (vs : list domains.val) :
    v ∈ vs → val_size v ≤ list_sum (map val_size vs).
  Proof.
    induction vs as [|v' vs IH]; intros Hin; first by inversion Hin.
    inversion Hin; subst; simpl; [lia|]. specialize (IH H1). lia.
  Qed.

  (** *** Commit *)
  Lemma wp_commit_free_gen (n : nat) :
    ∀ t ks Φ, tree_size t ≤ n → path_free t →
    WP ((FUnit, ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FCommit t, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    induction n as [|n IH]; intros t ks Φ Hsz Hpf.
    { destruct t; simpl in Hsz; lia. }
    destruct t as [k|x e σ|ts|p]; simpl in *; try done.
    - iIntros "H". wp_pure. by iApply "H".
    - iIntros "H". wp_pure. by iApply "H".
    - (* [FCommit (TList ts)]: elements in turn through [KCommitList] *)
      iIntros "H".
      destruct ts as [|t ts].
      { wp_pure. by iApply "H". }
      iApply (wp_pure_step _ _ (FCommit t, KCommitList ts :: ks)); [done|intros ?; cbn; reflexivity|].
      iNext.
      (* generic tail: from [FUnit] with [KCommitList todo] *)
      iAssert (∀ todo, ⌜Forall id (map path_free todo)⌝ -∗
                 ⌜list_sum (map tree_size todo) ≤ n⌝ -∗
                 WP ((FUnit, ks) : expr (reactLang δ)) {{ Φ }} -∗
                 WP ((FUnit, KCommitList todo :: ks) : expr (reactLang δ)) {{ Φ }})%I
        as "Htail".
      { iIntros (todo). iInduction todo as [|t' todo] "IHl"; iIntros (Hpf' Hsz') "H".
        - wp_pure. by iApply "H".
        - inversion Hpf' as [|?? Hpt' Hpts']; subst. simpl in Hsz'.
          iApply (wp_pure_step _ _ (FCommit t', KCommitList todo :: ks)); [done|intros ?; cbn; reflexivity|].
          iNext.
          iApply (IH t' with "[H]"); [lia|done|].
          iApply ("IHl" with "[%] [%] H"); [done|lia]. }
      inversion Hpf as [|?? Hpt Hpts]; subst. simpl in Hsz.
      iApply (IH t with "[H]"); [lia|done|].
      iApply ("Htail" with "[%] [%] H"); [done|lia].
  Qed.

  Lemma wp_commit_free (t : tree) (ks : list machine.frame) Φ :
    path_free t →
    WP ((FUnit, ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FCommit t, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. apply (wp_commit_free_gen (tree_size t)); lia. Qed.

  (** *** Check: a path-free tree never re-renders *)
  Lemma wp_check_free_gen (n : nat) :
    ∀ t ks Φ, tree_size t ≤ n → path_free t →
    WP ((FBool false, ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FCheck t, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    induction n as [|n IH]; intros t ks Φ Hsz Hpf.
    { destruct t; simpl in Hsz; lia. }
    destruct t as [k|x e σ|ts|p]; simpl in *; try done.
    - iIntros "H". wp_pure. by iApply "H".
    - iIntros "H". wp_pure. by iApply "H".
    - iIntros "H".
      destruct ts as [|t ts].
      { wp_pure. by iApply "H". }
      iApply (wp_pure_step _ _ (FCheck t, KCheckList false ts :: ks)); [done|intros ?; cbn; reflexivity|].
      iNext.
      iAssert (∀ todo, ⌜Forall id (map path_free todo)⌝ -∗
                 ⌜list_sum (map tree_size todo) ≤ n⌝ -∗
                 WP ((FBool false, ks) : expr (reactLang δ)) {{ Φ }} -∗
                 WP ((FBool false, KCheckList false todo :: ks) : expr (reactLang δ)) {{ Φ }})%I
        as "Htail".
      { iIntros (todo). iInduction todo as [|t' todo] "IHl"; iIntros (Hpf' Hsz') "H".
        - wp_pure. by iApply "H".
        - inversion Hpf' as [|?? Hpt' Hpts']; subst. simpl in Hsz'.
          iApply (wp_pure_step _ _ (FCheck t', KCheckList false todo :: ks)); [done|intros ?; cbn; reflexivity|].
          iNext.
          iApply (IH t' with "[H]"); [lia|done|].
          iApply ("IHl" with "[%] [%] H"); [done|lia]. }
      inversion Hpf as [|?? Hpt Hpts]; subst. simpl in Hsz.
      iApply (IH t with "[H]"); [lia|done|].
      iApply ("Htail" with "[%] [%] H"); [done|lia].
  Qed.

  Lemma wp_check_free (t : tree) (ks : list machine.frame) Φ :
    path_free t →
    WP ((FBool false, ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FCheck t, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. apply (wp_check_free_gen (tree_size t)); lia. Qed.

  (** *** Init of a component-free view spec *)
  Lemma wp_init_free_gen (n : nat) :
    ∀ s ks Φ, val_size s ≤ n → spec_free s →
    WP ((FTree (tree_of s), ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FInit s, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    induction n as [|n IH]; intros s ks Φ Hsz Hsf.
    { destruct s; simpl in Hsz; lia. }
    destruct s as [k|x e σ|C|C v|ss|l p]; simpl in *; try done.
    - iIntros "H". wp_pure. by iApply "H".
    - iIntros "H". wp_pure. by iApply "H".
    - iIntros "H".
      destruct ss as [|s ss].
      { wp_pure. by iApply "H". }
      iApply (wp_pure_step _ _ (FInit s, KInitList [] ss :: ks));
        [done|intros ?; cbn; reflexivity|].
      iNext.
      (* tail: [FTree t] with [KInitList done todo] accumulates the trees *)
      iAssert (∀ done todo, ⌜Forall id (map spec_free todo)⌝ -∗
                 ⌜list_sum (map val_size todo) ≤ n⌝ -∗
                 ∀ t, WP ((FTree (TList (done ++ [t] ++ map tree_of todo)), ks)
                          : expr (reactLang δ)) {{ Φ }} -∗
                      WP ((FTree t, KInitList done todo :: ks) : expr (reactLang δ)) {{ Φ }})%I
        as "Htail".
      { iIntros (done todo). iInduction todo as [|s' todo] "IHl" forall (done);
          iIntros (Hsf' Hsz' t) "H".
        - wp_pure. by iApply "H".
        - inversion Hsf' as [|?? Hps' Hpts']; subst. simpl in Hsz'.
          iApply (wp_pure_step _ _ (FInit s', KInitList (done ++ [t]) todo :: ks));
            [done|intros ?; cbn; reflexivity|].
          iNext.
          iApply (IH s' with "[H]"); [lia|done|].
          iApply ("IHl" $! (done ++ [t]) with "[%] [%] [H]"); [done|lia|].
          by rewrite -app_assoc. }
      inversion Hsf as [|?? Hps Hpss]; subst. simpl in Hsz.
      iApply (IH s with "[H]"); [lia|done|].
      by iApply ("Htail" $! [] ss with "[%] [%] H"); [done|lia].
  Qed.

  Lemma wp_init_free (s : domains.val) (ks : list machine.frame) Φ :
    spec_free s →
    WP ((FTree (tree_of s), ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FInit s, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. apply (wp_init_free_gen (val_size s)); lia. Qed.

  (** *** Reconciliation of a path-free tree against a component-free
      view spec: the result is the tree the spec denotes. *)
  Lemma wp_recon_free_gen (n : nat) :
    ∀ t s ks Φ, val_size s ≤ n → path_free t → spec_free s →
    WP ((FTree (tree_of s), ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FRecon t s, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    induction n as [|n IH]; intros t s ks Φ Hsz Hpf Hsf.
    { destruct s; simpl in Hsz; lia. }
    iIntros "H".
    destruct t as [k|x e σ|ts|p]; simpl in Hpf; try done;
      destruct s as [k'|x' e' σ'|C|C v|ss|l p']; simpl in Hsf; try done.
    (* all non-(list,list) combinations: RECONCILEOTHER, then init *)
    all: try (iApply (wp_pure_step _ _ (FInit _, ks)); [done|intros ?; cbn; reflexivity|];
              iNext; by iApply (wp_init_free with "H")).
    (* (TList ts, VList ss) *)
    destruct (decide (length ts = length ss)) as [Hlen|Hlen]; last first.
    { iApply (wp_pure_step _ _ (FInit (VList ss), ks)).
      { done. }
      { intros ?; cbn. by destruct (decide (length ts = length ss)). }
      iNext. by iApply (wp_init_free with "H"). }
    destruct ts as [|t ts], ss as [|s ss]; simpl in Hlen; try done.
    { iApply (wp_pure_step _ _ (FTree (TList []), ks)); [done|intros ?; by cbn|].
      by iNext. }
    iApply (wp_pure_step _ _ (FRecon t s, KReconList [] ts ss :: ks)).
    { done. }
    { intros ?; cbn. by destruct (decide (S (length ts) = S (length ss))). }
    iNext.
    iAssert (∀ done ttodo stodo, ⌜length ttodo = length stodo⌝ -∗
               ⌜Forall id (map path_free ttodo)⌝ -∗ ⌜Forall id (map spec_free stodo)⌝ -∗
               ⌜list_sum (map val_size stodo) ≤ n⌝ -∗
               ∀ t', WP ((FTree (TList (done ++ [t'] ++ map tree_of stodo)), ks)
                         : expr (reactLang δ)) {{ Φ }} -∗
                     WP ((FTree t', KReconList done ttodo stodo :: ks) : expr (reactLang δ)) {{ Φ }})%I
      as "Htail".
    { iIntros (done ttodo). iInduction ttodo as [|t2 ttodo] "IHl" forall (done);
        iIntros (stodo Hlen' Hpf' Hsf' Hsz' t') "H".
      - destruct stodo; last done. wp_pure. by iApply "H".
      - destruct stodo as [|s2 stodo]; first done. simpl in Hlen'.
        inversion Hpf' as [|?? Hpt2 Hpts]; subst.
        inversion Hsf' as [|?? Hps2 Hpss]; subst. simpl in Hsz'.
        iApply (wp_pure_step _ _ (FRecon t2 s2, KReconList (done ++ [t']) ttodo stodo :: ks));
          [done|intros ?; cbn; reflexivity|].
        iNext.
        iApply (IH t2 s2 with "[H]"); [lia|done|done|].
        iApply ("IHl" $! (done ++ [t']) stodo with "[%] [%] [%] [%] [H]"); [lia|done|done|lia|].
        by rewrite -app_assoc. }
    inversion Hpf as [|?? Hpt Hpts]; subst.
    inversion Hsf as [|?? Hps Hpss]; subst. simpl in Hsz.
    iApply (IH t s with "[H]"); [lia|done|done|].
    by iApply ("Htail" $! [] ts ss with "[%] [%] [%] [%] H"); [lia|done|done|lia].
  Qed.

  Lemma wp_recon_free (t : tree) (s : domains.val)
      (ks : list machine.frame) Φ :
    path_free t → spec_free s →
    WP ((FTree (tree_of s), ks) : expr (reactLang δ)) {{ Φ }} -∗
    WP ((FRecon t s, ks) : expr (reactLang δ)) {{ Φ }}.
  Proof. apply (wp_recon_free_gen (val_size s)); lia. Qed.
End pure_subtrees.

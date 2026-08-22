(** * The root render loop for a leaf component.

    A *leaf root* is a program whose main expression mounts one
    component whose rendered child never contains a component (constants,
    handlers, lists of these) and which registers no effects. For such a
    program the render loop of the machine — mount, and for each event:
    dispatch, re-render if the handler turned Check on, reconcile if the
    state changed, commit, check — is run *once and for all* here, so
    that the [root_obligations] of [component.v] follow from three
    specifications the client proves with the hook rules alone
    ([leaf_obligations]):

    - the body in Init phase, from the empty render context, ends in the
      slot table [ld_st a] of some initial abstract state [a] and returns
      the view spec [ld_spec a];
    - the [i]-th handler of the rendered tree, from quiescence in [a],
      leaves the view in a state satisfying the client's [ld_hpost a i]
      (typically: the updaters enqueued on the slots, Check on);
    - the body in Succ phase, from that view, ends in the slot table of
      some [a'] with [rs_step a i a'] and returns [ld_spec a'].

    The invariant [leaf_inv a m ω] is the memory holding exactly the
    quiescent view [qview a] at path 0. Everything else — trees, display,
    handler lookup, decisions — is computed generically for path-free
    children ([display_free], [handlers_free]). *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting step_rules runtime_rules hooks runtime
  component.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** ** Path-free trees: display and handlers, computed *)

Fixpoint display_free (t : tree) : dtree :=
  match t with
  | TConst k => DConst k
  | TClos _ _ _ => DHandler
  | TList ts => DList (map display_free ts)
  | TPath _ => DConst CUnit
  end.

Fixpoint handlers_free (t : tree) : list domains.val :=
  match t with
  | TConst _ => []
  | TClos x e σ => [VClos x e σ]
  | TList ts => concat (map handlers_free ts)
  | TPath _ => []
  end.

Section free_trees.
  Lemma tree_of_path_free_gen (n : nat) :
    ∀ s, val_size s ≤ n → spec_free s → path_free (tree_of s).
  Proof.
    induction n as [|n IH]; intros s Hsz Hsf.
    { destruct s; simpl in Hsz; lia. }
    destruct s as [k|x e σ|C|C v|ss|l p]; simpl in *; try done.
    rewrite !Forall_map. rewrite Forall_map in Hsf.
    apply Forall_forall. intros s Hin. simpl.
    apply IH; [|by eapply Forall_forall in Hsf].
    pose proof (val_sum_elem s ss Hin). lia.
  Qed.

  Lemma tree_of_path_free (s : domains.val) :
    spec_free s → path_free (tree_of s).
  Proof. apply (tree_of_path_free_gen (val_size s)); lia. Qed.

  Lemma tree_size_tree_of_gen (n : nat) :
    ∀ s, val_size s ≤ n → tree_size (tree_of s) = val_size s.
  Proof.
    induction n as [|n IH]; intros s Hsz.
    { destruct s; simpl in Hsz; lia. }
    destruct s as [k|x e σ|C|C v|ss|l p]; simpl in *; try done.
    f_equal. rewrite map_map. f_equal.
    apply map_ext_in. intros s Hin. apply IH.
    pose proof (val_sum_elem s ss (proj2 (list_elem_of_In _ _) Hin)). lia.
  Qed.

  Lemma tree_size_tree_of (s : domains.val) :
    tree_size (tree_of s) = val_size s.
  Proof. apply (tree_size_tree_of_gen (val_size s)); lia. Qed.

  Lemma display_t_free (n : nat) :
    ∀ m t, tree_size t ≤ n → path_free t →
    display_t n m t = Ok (display_free t).
  Proof.
    induction n as [|n IH]; intros m t Hsz Hpf.
    { destruct t; simpl in Hsz; lia. }
    destruct t as [k|x e σ|ts|p]; simpl in *; try done.
    assert (∀ ts', Forall id (map path_free ts') →
                   list_sum (map tree_size ts') ≤ n →
                   (fix go (ts : list tree) : res (list dtree) :=
                      match ts with
                      | [] => mret []
                      | t :: ts' => d ← display_t n m t; ds ← go ts'; mret (d :: ds)
                      end) ts' = Ok (map display_free ts')) as Hgo.
    { intros ts'. induction ts' as [|t ts' IHl]; intros Hpf' Hsz'; first done.
      inversion Hpf' as [|?? Hpt Hpts]; subst. simpl in Hsz'.
      rewrite IH; [|lia|done]. rewrite IHl; [|done|lia]. done. }
    rewrite Hgo; [done|done|lia].
  Qed.

  Lemma handlers_h_free_gen (n : nat) :
    ∀ h m t, tree_size t ≤ n → path_free t →
    handlers_h (S h) m t = Ok (handlers_free t).
  Proof.
    induction n as [|n IH]; intros h m t Hsz Hpf.
    { destruct t; simpl in Hsz; lia. }
    destruct t as [k|x e σ|ts|p]; simpl in *; try done.
    induction ts as [|t ts IHl]; first done.
    inversion Hpf as [|?? Hpt Hpts]; subst. simpl in Hsz.
    specialize (IH h m t ltac:(lia) Hpt). simpl in IH. rewrite IH.
    rewrite IHl; [done|lia|done].
  Qed.

  Lemma handlers_h_free (h : nat) (m : tree_mem) (t : tree) :
    path_free t → handlers_h (S h) m t = Ok (handlers_free t).
  Proof. apply (handlers_h_free_gen (tree_size t)); lia. Qed.

  (** At the root: the memory holds a view at path 0 with a path-free
      child. *)
  Lemma handlers_of_leaf (m : tree_mem) (π : domains.view) :
    m !! (0:path) = Some π → path_free (vw_child π) →
    handlers_of m (TPath 0) = Ok (handlers_free (vw_child π)).
  Proof.
    intros Hp Hpf. unfold handlers_of.
    destruct (map_size m) as [|h] eqn:Hsz.
    { apply map_size_empty_inv in Hsz. by rewrite Hsz in Hp. }
    simpl. rewrite Hp. by apply handlers_h_free.
  Qed.

  (** One fuel step on a path (stated to avoid [simpl] on the unary
      fuel numeral). *)
  Lemma display_t_path_S (n : nat) (m : tree_mem) (p : path) :
    display_t (S n) m (TPath p)
      = match m !! p with
        | Some π => display_t n m (vw_child π)
        | None => Stuck "display: dangling path"
        end.
  Proof. reflexivity. Qed.

  Lemma display_leaf (m : tree_mem) (π : domains.view) :
    m !! (0:path) = Some π → path_free (vw_child π) → tree_size (vw_child π) ≤ 999 →
    display_t 1000 m (TPath 0) = Ok (display_free (vw_child π)).
  Proof.
    intros Hp Hpf Hsz. change 1000 with (S 999).
    rewrite display_t_path_S. rewrite Hp. by apply display_t_free.
  Qed.
End free_trees.

(** ** The leaf-root data and obligations *)

Record leaf_data (S : root_spec) := LeafData {
  ld_C : comp_name;                     (* the root component *)
  ld_x : var;
  ld_body : syntax.expr;
  ld_v : domains.val;                   (* its argument *)
  ld_st : rs_A S → stt_store;           (* the slot table at quiescence *)
  ld_spec : rs_A S → domains.val;       (* the view spec it renders *)
  ld_hpost : rs_A S → nat → domains.view → Prop;  (* the view after handler [i] *)
}.
Arguments ld_C {S} _. Arguments ld_x {S} _. Arguments ld_body {S} _.
Arguments ld_v {S} _. Arguments ld_st {S} _. Arguments ld_spec {S} _.
Arguments ld_hpost {S} _.

Section leaf_root.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).
  Context (S : root_spec) (L : leaf_data S).

  Implicit Types Φ : mval → iProp Σ.

  (** The view with slot table [ld_st a] and child [t] (no decisions, no
      effects, all slots visited). *)
  Definition bview (a : rs_A S) (t : tree) : domains.view :=
    {|
       vw_comp := ld_C L;
       vw_arg := ld_v L;
       vw_dec := dec_empty;
       vw_sttst := ld_st L a;
       vw_effq := [];
       vw_child := t;
       vw_hook_cursor := map_size (ld_st L a)
     |}.

  (** The quiescent view at [a]. *)
  Definition qview (a : rs_A S) : domains.view := bview a (tree_of (ld_spec L a)).

  Definition leaf_inv (a : rs_A S) (m : tree_mem) (ω : out_buf) : iProp Σ :=
    ⌜m = <[(0:path) := qview a]> ∅⌝ ∗
    mem_auth_frag m ∗ view_ptsto 0 (qview a) ∗ render_idle ∗ out_frag ω.

  (** The initial render context of the root. *)
  Definition init_ctx : domains.view :=
    enter_view ({|
       vw_comp := ld_C L;
       vw_arg := ld_v L;
       vw_dec := dec_empty;
       vw_sttst := ∅;
       vw_effq := [];
       vw_child := TConst CUnit;
       vw_hook_cursor := 0
     |}).

  Definition leaf_obligations : iProp Σ :=
    (* the component and its rendered specs *)
    ⌜δ !! ld_C L = Some (CompDef (ld_x L) (ld_body L))⌝ ∗
    ⌜∀ a, spec_free (ld_spec L a) ∧ val_size (ld_spec L a) ≤ 999⌝ ∗
    ⌜∀ a, rs_disp S a = display_free (tree_of (ld_spec L a))⌝ ∗
    ⌜∀ a i, rs_valid S a i →
            ∃ x e σ, handlers_free (tree_of (ld_spec L a)) !! i = Some (VClos x e σ)⌝ ∗
    (* the shape of the view a handler leaves: same component, no
       effects, the child untouched; if it did not turn Check on it is
       already quiescent in a successor state *)
    ⌜∀ a i π, ld_hpost L a i π →
              vw_comp π = ld_C L ∧ vw_arg π = ld_v L ∧ vw_effq π = [] ∧
              dec_effect (vw_dec π) = false ∧ vw_child π = tree_of (ld_spec L a)⌝ ∗
    ⌜∀ a i π, ld_hpost L a i π → dec_check (vw_dec π) = false →
              ∃ a', rs_step S a i a' ∧ π = qview a'⌝ ∗
    (* the body in Init phase *)
    □ (∀ ω ks Φ,
       render_ctx 0 init_ctx -∗ out_frag ω -∗
       (∀ a ω', ⌜rs_init S a⌝ -∗
          render_ctx 0 (bview a (TConst CUnit)) -∗ out_frag ω' -∗
          WP ((FVal (ld_spec L a), ks) : expr (reactLang δ)) {{ Φ }}) -∗
       WP ((FExpr PInit [(ld_x L, ld_v L)] (ld_body L), ks) : expr (reactLang δ)) {{ Φ }}) ∗
    (* the handlers, from quiescence *)
    □ (∀ a i x e σ ω ks Φ,
       ⌜rs_valid S a i⌝ -∗
       ⌜handlers_free (tree_of (ld_spec L a)) !! i = Some (VClos x e σ)⌝ -∗
       mem_auth_frag (<[(0:path) := qview a]> ∅) -∗ view_ptsto 0 (qview a) -∗
       render_idle -∗ out_frag ω -∗
       (∀ v π ω', ⌜ld_hpost L a i π⌝ -∗
          mem_auth_frag (<[(0:path) := π]> ∅) -∗ view_ptsto 0 π -∗
          render_idle -∗ out_frag ω' -∗
          WP ((FVal v, ks) : expr (reactLang δ)) {{ Φ }}) -∗
       WP ((FExpr PNormal (env_insert x (VConst CUnit) σ) e, ks) : expr (reactLang δ)) {{ Φ }}) ∗
    (* the body in Succ phase, after a handler that turned Check on: it
       settles in a successor state [a'] with the Effect decision [eff]
       (and if no Effect, the rendered spec is unchanged) *)
    □ (∀ a i π ω ks Φ,
       ⌜ld_hpost L a i π⌝ -∗ ⌜dec_check (vw_dec π) = true⌝ -∗
       render_ctx 0 (enter_view π) -∗ out_frag ω -∗
       (∀ a' (eff : bool) ω', ⌜rs_step S a i a'⌝ -∗
          ⌜eff = false → ld_spec L a' = ld_spec L a⌝ -∗
          render_ctx 0 (bview a' (tree_of (ld_spec L a))
                          <| vw_dec := Decisions false eff |>) -∗
          out_frag ω' -∗
          WP ((FVal (ld_spec L a'), ks) : expr (reactLang δ)) {{ Φ }}) -∗
       WP ((FExpr PSucc [(ld_x L, ld_v L)] (ld_body L), ks) : expr (reactLang δ)) {{ Φ }}).

  Global Instance leaf_obligations_persistent : Persistent leaf_obligations.
  Proof. apply _. Qed.

  (** *** Auxiliary facts *)

  Local Lemma qview_child (a : rs_A S) :
    vw_child (qview a) = tree_of (ld_spec L a).
  Proof. done. Qed.

  (** *** Mount *)

  (** From [FInit ⟨C, v⟩] in rendered mode to quiescence in an initial
      state. *)
  Lemma leaf_mount (ks : list machine.frame) Φ :
    leaf_obligations -∗
    mem_auth_frag ∅ -∗ render_idle -∗ out_frag [] -∗
    (∀ a m ω, ⌜rs_init S a⌝ -∗ leaf_inv a m ω -∗
       WP ((FIdle (TPath 0), ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FInit (VCompSpec (ld_C L) (ld_v L)), KMainMounted :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros "(%Hδ & %Hfree & %Hdisp & %Hhs & %Hshape & %Hidle & #Hinit & #Hhandler & #Hsucc)".
    iIntros "Hm Hr Ho Hk".
    iApply (wp_init_component _ _ _ _ _ _
              (λ π' s, ∃ a ω', ⌜rs_init S a⌝ ∗ ⌜π' = bview a (TConst CUnit)⌝ ∗
                               ⌜s = ld_spec L a⌝ ∗ out_frag ω')%I
              with "[Ho] Hm Hr").
    { done. }
    { iIntros (ks' Φ') "Hr Hk'".
      iEval (change (fresh_path ∅) with (0:path)) in "Hr".
      iEval (change (fresh_path ∅) with (0:path)).
      iApply ("Hinit" with "Hr Ho").
      iIntros (a ω' Hinit) "Hr Ho".
      iApply ("Hk'" $! (ld_spec L a) (bview a (TConst CUnit)) with "[%] Hr [Ho]").
      { split; [done|]. by rewrite /bview. }
      iExists a, ω'. by iFrame. }
    iIntros (s π' _) "Hm Hp Hr (%a & %ω' & %Hinit & -> & -> & Ho)".
    iEval (change (fresh_path ∅) with (0:path)) in "Hm Hp".
    iEval (change (fresh_path ∅) with (0:path)).
    destruct (Hfree a) as [Hsf Hsz].
    pose proof (tree_of_path_free _ Hsf) as Hpf.
    (* the child view spec initializes to the tree it denotes *)
    iApply wp_init_free; first done.
    iApply (wp_init_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    (* rendered: commit (no effects), check (idle), quiescent *)
    wp_pure.
    iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm". cbn [vw_child vw_effq set bview].
    iApply wp_commit_free; first done.
    iApply (wp_commit_finish_any with "Hm Hp");
      [by left|by rewrite lookup_insert_eq|].
    iNext. iIntros "Hm Hp".
    iEval (rewrite insert_insert_eq) in "Hm".
    wp_pure.
    iApply (wp_check_idle with "Hm"); [by rewrite lookup_insert_eq|done|].
    iNext. iIntros "Hm". cbn [vw_child set bview].
    iApply wp_check_free; first done.
    wp_pure.
    iApply ("Hk" $! a with "[//]"). rewrite /leaf_inv /qview /bview. by iFrame.
  Qed.

  (** *** Event *)

  (** From quiescence in [a], dispatching a valid event [i] returns to
      quiescence in a successor [a']. *)
  Lemma leaf_event (a : rs_A S) (m : tree_mem) (ω : out_buf) (i : nat)
      (evs : list nat) (ks : list machine.frame) Φ :
    rs_valid S a i →
    leaf_obligations -∗
    leaf_inv a m ω -∗
    (∀ a' m' ω', ⌜rs_step S a i a'⌝ -∗ leaf_inv a' m' ω' -∗
       WP ((FIdle (TPath 0), KEvents evs :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
    WP ((FIdle (TPath 0), KEvents (i :: evs) :: ks) : expr (reactLang δ)) {{ Φ }}.
  Proof.
    iIntros (Hvalid).
    iIntros "(%Hδ & %Hfree & %Hdisp & %Hhs & %Hshape & %Hidle & #Hinit & #Hhandler & #Hsucc)".
    iIntros "(-> & Hm & Hp & Hr & Ho) Hk".
    destruct (Hfree a) as [Hsf Hsz].
    pose proof (tree_of_path_free _ Hsf) as Hpf.
    destruct (Hhs a i Hvalid) as (x & e & σ & Hlookup).
    (* dispatch the handler *)
    iApply (wp_event_dispatch _ (TPath 0) i evs _ x e σ with "Hm").
    { by apply (handlers_of_leaf _ (qview a)); [rewrite lookup_insert_eq|]. }
    { done. }
    iNext. iIntros "Hm".
    iApply ("Hhandler" with "[//] [//] Hm Hp Hr Ho").
    iIntros (v πh ω' Hpost) "Hm Hp Hr Ho".
    destruct (Hshape a i πh Hpost) as (Hcomp & Harg & Heffq & Heff & Hchild).
    (* STEPEVENT done: check mode *)
    wp_pure.
    destruct (dec_check (vw_dec πh)) eqn:Hcheck; last first.
    { (* the handler left the view quiescent *)
      destruct (Hidle a i πh Hpost Hcheck) as (a' & Hstep & ->).
      destruct (Hfree a') as [Hsf' _].
      iApply (wp_check_idle with "Hm"); [by rewrite lookup_insert_eq|done|].
      iNext. iIntros "Hm". rewrite qview_child.
      iApply wp_check_free; first by apply tree_of_path_free.
      wp_pure.
      iApply ("Hk" $! a' with "[//]"). rewrite /leaf_inv. by iFrame. }
    (* re-render: CHECK with the Succ-phase body spec *)
    iApply (wp_check_component _ (0:path) πh (ld_x L) (ld_body L) _
              (λ π' s, ∃ a' (eff : bool) ω'', ⌜rs_step S a i a'⌝ ∗
                 ⌜π' = bview a' (tree_of (ld_spec L a))
                         <| vw_dec := Decisions false eff |>⌝ ∗
                 ⌜eff = false → ld_spec L a' = ld_spec L a⌝ ∗
                 ⌜s = ld_spec L a'⌝ ∗ out_frag ω'')%I
              with "[Ho] Hm Hp Hr").
    { by rewrite lookup_insert_eq. }
    { done. }
    { by rewrite Hcomp. }
    { iIntros (ks' Φ') "Hr Hk'". rewrite Harg.
      iApply ("Hsucc" with "[//] [//] Hr Ho").
      iIntros (a' eff ω'' Hstep He') "Hr Ho".
      iApply ("Hk'" $! (ld_spec L a') with "[%] Hr [Ho]").
      { split; reflexivity. }
      iExists a', eff, ω''. iFrame "Ho". iPureIntro. auto. }
    iIntros (s π' _) "Hm Hp Hr (%a' & %eff & %ω'' & %Hstep & -> & %He' & -> & Ho)".
    iEval (rewrite insert_insert_eq) in "Hm".
    destruct (Hfree a') as [Hsf' Hsz'].
    pose proof (tree_of_path_free _ Hsf') as Hpf'.
    rewrite Hchild.
    destruct eff.
    - (* Effect: reconcile the old child against the new spec, commit,
         check — quiescent in [a'] *)
      iApply wp_recon_free; [done|done|].
      iApply (wp_check_finish with "Hm Hp"); first by rewrite lookup_insert_eq.
      iNext. iIntros "Hm Hp".
      iEval (rewrite insert_insert_eq) in "Hm".
      wp_pure.
      iApply (wp_commit_enter with "Hm"); [by rewrite lookup_insert_eq|done|].
      iNext. iIntros "Hm".
      iApply wp_commit_free; first done.
      iApply (wp_commit_finish_any with "Hm Hp");
        [by left|by rewrite lookup_insert_eq|].
      iNext. iIntros "Hm Hp".
      iEval (rewrite insert_insert_eq) in "Hm".
      wp_pure.
      iApply (wp_check_idle with "Hm"); [by rewrite lookup_insert_eq|done|].
      iNext. iIntros "Hm".
      iApply wp_check_free; first done.
      wp_pure.
      assert (bview a' (tree_of (ld_spec L a))
                <| vw_dec := Decisions false true |>
                <| vw_child := tree_of (ld_spec L a') |>
                <| vw_dec ::= dec_rm_effect |> = qview a') as Hq by reflexivity.
      rewrite Hq.
      iApply ("Hk" $! a' with "[//]"). rewrite /leaf_inv. by iFrame.
    - (* no Effect: the spec (hence the child and the view) is unchanged *)
      pose proof (He' eq_refl) as Hspec.
      iApply wp_check_free; first done.
      wp_pure.
      assert (bview a' (tree_of (ld_spec L a))
                <| vw_dec := Decisions false false |> = qview a') as Hq
        by (rewrite /qview Hspec; reflexivity).
      rewrite Hq.
      iApply ("Hk" $! a' with "[//]"). rewrite /leaf_inv. by iFrame.
  Qed.

  (** *** The root obligations *)

  (** Evaluation of the main expression to the root's component spec is
      the only program-specific step of the mount. *)
  Definition main_spec (P : prog) : iProp Σ :=
    □ (∀ ks Φ,
       WP ((FInit (VCompSpec (ld_C L) (ld_v L)), KMainMounted :: ks) : expr (reactLang δ)) {{ Φ }} -∗
       WP ((FExpr PNormal [] (p_main P), KMainInit :: ks) : expr (reactLang δ)) {{ Φ }}).

  Theorem leaf_root_obligations (P : prog) :
    main_spec P -∗ leaf_obligations -∗ root_obligations δ P S leaf_inv.
  Proof.
    iIntros "#Hmain #Hob".
    iPoseProof "Hob" as "(%Hδ & %Hfree & %Hdisp & %Hhs & %Hshape & %Hidle & _ & _ & _)".
    iSplit; [|iSplit].
    - (* mount *)
      iIntros "!>" (evs Φ) "(Hm & _ & Hr & Ho) Hk".
      iEval (rewrite /machine_init_cfg /cfg_expr;
             cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd]) in "Hm Hr Ho".
      iEval (rewrite /machine_init_cfg /cfg_expr;
             cbn [mc_focus mc_stack mc_mem mc_reg mc_out fst snd]).
      iApply "Hmain".
      iApply (leaf_mount with "Hob Hm Hr Ho").
      iIntros (a m ω Hinit) "HI". by iApply ("Hk" with "[//] HI").
    - (* event *)
      iIntros "!>" (a m ω i evs ks Φ Hvalid) "HI Hk".
      by iApply (leaf_event with "Hob HI Hk").
    - (* display *)
      iIntros "!>" (a m ω) "(-> & Hm & Hp & Hr & Ho)". iFrame. iPureIntro.
      destruct (Hfree a) as [Hsf Hsz].
      rewrite Hdisp -qview_child.
      apply display_leaf; [by rewrite lookup_insert_eq| |].
      + rewrite qview_child. by apply tree_of_path_free.
      + rewrite qview_child tree_size_tree_of. lia.
  Qed.

  (** The main expression [Comp C k]: a component applied to a constant. *)
  Lemma main_spec_const (P : prog) (k : syntax.const) :
    p_main P = EApp (ECompName (ld_C L)) (EConst k) →
    ld_v L = VConst k →
    ⊢ main_spec P.
  Proof.
    iIntros (Hmain Hv). iIntros "!>" (ks Φ) "Hwp". rewrite Hmain Hv.
    do 6 wp_pure. iApply "Hwp".
  Qed.
End leaf_root.

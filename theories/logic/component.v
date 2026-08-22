(** * Root component specifications: refinement of an abstract LTS.

    Design decision D7 / §5.2, generic form. A *root specification*
    [root_spec] is an abstract labelled transition system over abstract
    states [A]: initial states, a step relation indexed by the event
    (handler index), and a display function. A component satisfies it if
    the client discharges three obligations, all stated on the machine
    through an invariant [Inv a m ω] tying an abstract state to the
    physical memory and output at quiescence:

    - [mount]: from the initial configuration, the machine reaches
      quiescence in some initial abstract state;
    - [event]: from quiescence in [a], dispatching a valid event [i]
      returns to quiescence in some [a'] with [step a i a'];
    - [display]: at quiescence in [a], the display of the root is
      [disp a] (and [Inv] exposes the memory/output ownership needed by
      adequacy).

    Then [root_adequacy]: for every trace of valid events, the machine
    never gets stuck, and any reached value is quiescent in a *reachable*
    abstract state whose display is shown — with no Iris in the
    statement. The Counter instance is in [examples/counter_modular.v]. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst lifting adequacy runtime.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import proofmode.

Record root_spec := RootSpec {
  rs_A : Type;
  rs_init : rs_A → Prop;
  rs_valid : rs_A → nat → Prop;              (* which events may fire in [a] *)
  rs_step : rs_A → nat → rs_A → Prop;
  rs_disp : rs_A → dtree;
}.

(** Reachability in the abstract LTS along a trace. *)
Inductive rs_reach (S : root_spec) : rs_A S → list nat → rs_A S → Prop :=
  | rs_reach_nil a : rs_reach S a [] a
  | rs_reach_cons a i a' evs a'' :
      rs_valid S a i → rs_step S a i a' → rs_reach S a' evs a'' →
      rs_reach S a (i :: evs) a''.

(** A trace is admissible from [a] if every event is valid when it fires,
    along every abstract run (the LTS may be nondeterministic). *)
Inductive rs_admissible (S : root_spec) : rs_A S → list nat → Prop :=
  | rs_adm_nil a : rs_admissible S a []
  | rs_adm_cons a i evs :
      rs_valid S a i →
      (∀ a', rs_step S a i a' → rs_admissible S a' evs) →
      rs_admissible S a (i :: evs).

Section component.
  Context `{!invGS Σ, !reactGS Σ}.
  Context (δ : def_table).

  Definition root_obligations (P : prog) (S : root_spec)
      (Inv : rs_A S → tree_mem → out_buf → iProp Σ) : iProp Σ :=
    (* mount *)
    □ (∀ evs Φ,
       own_cfg (machine_init_cfg P evs) -∗
       (∀ a m ω, ⌜rs_init S a⌝ -∗ Inv a m ω -∗
          WP ((FIdle (TPath 0), [KEvents evs]) : expr (reactLang δ)) {{ Φ }}) -∗
       WP (cfg_expr (machine_init_cfg P evs) : expr (reactLang δ)) {{ Φ }}) ∗
    (* event *)
    □ (∀ a m ω i evs ks Φ,
       ⌜rs_valid S a i⌝ -∗ Inv a m ω -∗
       (∀ a' m' ω', ⌜rs_step S a i a'⌝ -∗ Inv a' m' ω' -∗
          WP ((FIdle (TPath 0), KEvents evs :: ks) : expr (reactLang δ)) {{ Φ }}) -∗
       WP ((FIdle (TPath 0), KEvents (i :: evs) :: ks) : expr (reactLang δ)) {{ Φ }}) ∗
    (* display and ownership at quiescence *)
    □ (∀ a m ω, Inv a m ω -∗
       mem_auth_frag m ∗ out_frag ω ∗
       ⌜display m (TPath 0) = Ok (rs_disp S a)⌝).

  Global Instance root_obligations_persistent P S Inv :
    Persistent (root_obligations P S Inv).
  Proof. apply _. Qed.

  Lemma root_run (P : prog) (S : root_spec)
      (Inv : rs_A S → tree_mem → out_buf → iProp Σ)
      (evs : list nat) (a : rs_A S) (m : tree_mem) (ω : out_buf) :
    rs_admissible S a evs →
    root_obligations P S Inv -∗
    Inv a m ω -∗
    WP ((FIdle (TPath 0), [KEvents evs]) : expr (reactLang δ)) {{ w,
      ∃ m' ω', mem_auth_frag m' ∗ out_frag ω' ∗
        ⌜∃ a', rs_reach S a evs a' ∧ w = MIdle (TPath 0) ∧
               display m' (TPath 0) = Ok (rs_disp S a')⌝ }}.
  Proof.
    revert a m ω. induction evs as [|i evs IH]; intros a m ω Hadm.
    - iIntros "(_ & _ & #Hdisp) HI".
      iApply wp_events_done. iNext.
      iApply (wp_value' _ _ _ (MIdle (TPath 0))).
      iDestruct ("Hdisp" with "HI") as "(Hm & Ho & %Hd)".
      iExists m, ω. iFrame. iPureIntro.
      exists a. split_and!; [constructor|done|done].
    - inversion Hadm as [|? ? ? Hvalid Hnext]; subst.
      iIntros "#Hob HI".
      iPoseProof "Hob" as "(_ & #Hev & _)".
      iApply ("Hev" with "[//] HI").
      iIntros (a1 m1 ω1 Hstep) "HI".
      iApply (wp_wand with "[HI]").
      { iApply (IH with "Hob HI"). by apply Hnext. }
      iIntros (w) "(%m' & %ω' & Hm & Ho & %a2 & %Hr & -> & %Hd)".
      iExists m', ω'. iFrame. iPureIntro. exists a2. split_and!; [|done|done].
      by econstructor.
  Qed.

  Lemma root_wp (P : prog) (S : root_spec)
      (Inv : rs_A S → tree_mem → out_buf → iProp Σ) (evs : list nat) :
    (∀ a, rs_init S a → rs_admissible S a evs) →
    root_obligations P S Inv -∗
    own_cfg (machine_init_cfg P evs) -∗
    WP (cfg_expr (machine_init_cfg P evs) : expr (reactLang δ)) {{ w,
      ∃ m ω, mem_auth_frag m ∗ out_frag ω ∗
        ⌜∃ a0 a', rs_init S a0 ∧ rs_reach S a0 evs a' ∧ w = MIdle (TPath 0) ∧
                  display m (TPath 0) = Ok (rs_disp S a')⌝ }}.
  Proof.
    iIntros (Hadm) "#Hob Hown".
    iPoseProof "Hob" as "(#Hmount & _ & _)".
    iApply ("Hmount" with "Hown").
    iIntros (a m ω Hinit) "HI".
    iApply (wp_wand with "[HI]"); first by iApply (root_run with "Hob HI"); auto.
    iIntros (w) "(%m' & %ω' & Hm & Ho & %a' & %Hr & -> & %Hd)".
    iExists m', ω'. iFrame. iPureIntro. by exists a, a'.
  Qed.
End component.

(** The generic top-level theorem: a component satisfying [root_obligations]
    refines its abstract LTS along every admissible trace. *)
Theorem root_adequacy (Σ : gFunctors) `{!reactGpreS Σ} (P : prog)
    (S : root_spec)
    (Inv : ∀ `{!invGS Σ} `{!reactGS Σ}, rs_A S → tree_mem → out_buf → iProp Σ)
    (evs : list nat) :
  (∀ a, rs_init S a → rs_admissible S a evs) →
  (∀ (HI : invGS Σ) (HR : reactGS Σ),
     ⊢ root_obligations (prog_def_table P) P S Inv) →
  adequate NotStuck
    (cfg_expr (machine_init_cfg P evs) : expr (reactLang (prog_def_table P)))
    (cfg_state (machine_init_cfg P evs))
    (λ w σ, ∃ a0 a', rs_init S a0 ∧ rs_reach S a0 evs a' ∧ w = MIdle (TPath 0) ∧
                     display (ls_mem σ) (TPath 0) = Ok (rs_disp S a')).
Proof.
  intros Hadm Hob.
  apply (react_adequacy_state Σ _ _
           (λ w m ω, ∃ a0 a', rs_init S a0 ∧ rs_reach S a0 evs a' ∧ w = MIdle (TPath 0) ∧
                              display m (TPath 0) = Ok (rs_disp S a'))).
  intros HI HR. iIntros "Hown".
  iApply (root_wp with "[] Hown"); first done.
  iApply Hob.
Qed.

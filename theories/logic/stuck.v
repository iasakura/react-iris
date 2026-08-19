(** * Certifying non-safety: a stuck run refutes adequacy.

    The counterpart of [react_adequacy]: if the executable machine reaches
    a configuration on which no rule applies (and which is not a value),
    then no weakest-precondition proof exists for the program — since one
    would give adequacy, hence not-stuck. [stuck_nonval] computes the
    witness, so a Rules-of-React violation is refuted by [vm_compute]:
    the flagship instance is the paper's [Cond] (a hook under a
    conditional), see [examples/rules_of_hooks.v]. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.logic Require Import inst.
From iris.program_logic Require Import language adequacy.

Section stuck.
  Context (δ : def_table).

  (** The first stuck configuration along the deterministic run, if the
      run gets stuck within [n] steps. *)
  Fixpoint stuck_at (n : nat) (c : mcfg) : option mcfg :=
    match n with
    | O => None
    | S n =>
        match lto_val (cfg_expr c) with
        | Some _ => None
        | None =>
            match mstep δ c with
            | Ok c' => stuck_at n c'
            | Stuck _ => Some c
            | OOF => None
            end
        end
    end.

  Lemma stuck_at_sound (n : nat) (c c' : mcfg) :
    stuck_at n c = Some c' →
    rtc erased_step ([cfg_expr c : expr (reactLang δ)], cfg_state c)
                    ([cfg_expr c'], cfg_state c') ∧
    lto_val (cfg_expr c') = None ∧
    ∀ c'', mstep δ c' ≠ Ok c''.
  Proof.
    revert c. induction n as [|n IH]; intros c Hs; first done.
    change (match lto_val (cfg_expr c) with
            | Some _ => None
            | None => match mstep δ c with
                      | Ok c1 => stuck_at n c1 | Stuck _ => Some c | OOF => None end
            end = Some c') in Hs.
    destruct (lto_val (cfg_expr c)) eqn:Hval; first done.
    destruct (mstep δ c) as [c1|msg|] eqn:Hstep; try done.
    - destruct (IH c1 Hs) as (Hrtc & Hnv & Hstuck).
      split_and!; [|done|done].
      eapply rtc_l; last exact Hrtc.
      exists [].
      eapply (step_atomic (cfg_expr c) (cfg_state c) (cfg_expr c1) (cfg_state c1) [] [] []);
        [done|done|].
      split_and!; [done|done|]. by rewrite !glue_split.
    - simplify_eq. split_and!; [constructor|done|]. by rewrite Hstep.
  Qed.

  (** A stuck non-value refutes adequacy, for any postcondition. *)
  Theorem stuck_not_adequate (n : nat) (c c' : mcfg)
      (φ : mval → lstate → Prop) :
    stuck_at n c = Some c' →
    ¬ adequate NotStuck (cfg_expr c : expr (reactLang δ)) (cfg_state c) φ.
  Proof.
    intros Hs Had.
    destruct (stuck_at_sound _ _ _ Hs) as (Hrtc & Hnv & Hstuck).
    assert (cfg_expr c' ∈ [cfg_expr c' : expr (reactLang δ)]) as Hin by set_solver.
    pose proof (adequate_not_stuck _ _ _ _ Had _ _ (cfg_expr c') eq_refl Hrtc Hin)
      as [[v Hv]|(κ & e2 & σ2 & efs & Hp)].
    - change (lto_val (cfg_expr c') = Some v) in Hv. by rewrite Hnv in Hv.
    - destruct Hp as (_ & _ & Hp). rewrite glue_split in Hp. by eapply Hstuck.
  Qed.

  (** Executable form: [vm_compute] decides it. *)
  Definition stuck_within (n : nat) (c : mcfg) : bool :=
    match stuck_at n c with Some _ => true | None => false end.

  Corollary stuck_within_not_adequate (n : nat) (c : mcfg)
      (φ : mval → lstate → Prop) :
    stuck_within n c = true →
    ¬ adequate NotStuck (cfg_expr c : expr (reactLang δ)) (cfg_state c) φ.
  Proof.
    rewrite /stuck_within. destruct (stuck_at n c) eqn:Hs; last done.
    intros _. by eapply stuck_not_adequate.
  Qed.
End stuck.

(** * End-to-end WP for the Counter component (M2 prototype).

    Validates the language instance and state-interpretation plumbing on a
    concrete program: from the client's configuration resources, the
    machine running [counter_prog] satisfies a weakest precondition whose
    postcondition pins the quiescent display — safety (no Rules-of-React
    violation) plus the rendered view, transported through Iris.

    The proof is "by computation" ([wp_mrun_ok]); the modular proof via
    hook and component specifications is the goal of M3. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine tests.
From react_iris.logic Require Import inst lifting.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.

Section counter.
  Context `{!invGS Σ, !reactGS Σ}.

  Local Definition δ : def_table := prog_def_table counter_prog.
  Local Definition c0 : mcfg := machine_init_cfg counter_prog.

  Lemma counter_wp :
    own_cfg c0 -∗
    WP (cfg_expr c0 : expr (reactLang δ)) {{ w,
      ∃ t cf, ⌜w = MIdle t⌝ ∗ own_cfg cf ∗
        ⌜display_t 1000 (mc_mem cf) t
           = Ok (DList [DConst (CInt 0); DHandler])⌝ }}.
  Proof.
    destruct (mrun δ 20000 c0) as [c'|msg|] eqn:HE;
      [|by vm_compute in HE..].
    iIntros "Hown".
    iApply (wp_mrun_ok _ _ _ _ _ HE with "Hown").
    iIntros (t Hval) "Hown".
    iExists t, c'. iFrame "Hown". iSplit; first done.
    iPureIntro.
    vm_compute in HE. simplify_eq.
    vm_compute in Hval. simplify_eq.
    by vm_compute.
  Qed.
End counter.

(** * Rules of Hooks: a violator has no weakest-precondition proof.

    Under cursor semantics (design decision D2) hooks are identified by
    their position among the hook calls of a render. The paper's [Cond]
    (§1) calls a second [useState] only after its state has been toggled,
    so the re-render asks for a slot that does not exist and the machine
    is stuck. [cond_not_adequate] certifies, by computation, that no
    postcondition is adequate for it — hence no WP proof of the program
    can exist (any WP would yield adequacy by [react_adequacy]). This is
    the concrete content of "WP ⇒ Rules of Hooks": the syntactic Rules of
    Hooks are not assumed; a program that breaks them is simply
    unverifiable, and one that respects them (all other examples,
    including a custom hook: tests.v [custom_prog]) is verifiable. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine tests.
From react_iris.logic Require Import inst stuck.
From iris.program_logic Require Import adequacy.

Theorem cond_not_adequate φ :
  ¬ adequate NotStuck
      (cfg_expr (machine_init_cfg cond_prog [0%nat])
         : expr (reactLang (prog_def_table cond_prog)))
      (cfg_state (machine_init_cfg cond_prog [0%nat])) φ.
Proof.
  apply (stuck_within_not_adequate _ 20000).
  by vm_compute.
Qed.

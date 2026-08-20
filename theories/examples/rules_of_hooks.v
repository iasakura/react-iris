(** * Rules of Hooks: a violator has no weakest-precondition proof.

    The program ([programs.v]):

<<
let Cond x =
  let (b, setB) = useState false in
  if b then (let (s, setS) = useState 0 in s)
  else button (fun _ -> setB (fun b -> not b));;
Cond ()
>>

    What is verified: [cond_not_adequate] — for every postcondition φ,
    the run of [Cond] with one click is not adequate; hence no WP proof
    of it exists.

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
    including a custom hook, [custom_hook.v]) is verifiable. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains interp machine.
From react_iris.examples Require Import programs.
From react_iris.logic Require Import inst stuck.
From iris.program_logic Require Import adequacy.

Theorem cond_not_adequate (φ : mval → lstate → Prop) :
  ¬ adequate NotStuck
      (cfg_expr (machine_init_cfg cond_prog [0%nat])
         : expr (reactLang (prog_def_table cond_prog)))
      (cfg_state (machine_init_cfg cond_prog [0%nat])) φ.
Proof.
  apply (stuck_within_not_adequate _ 20000).
  by vm_compute.
Qed.

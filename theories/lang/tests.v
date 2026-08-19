(** * Executable conformance tests for the interpreter.

    Runs the programs of [lang/programs.v] (the paper's running examples)
    and checks the observable behavior (output buffer, hook state,
    displays, view counts) by computation. These play the role of the
    react-trace test suite until the differential-testing harness against
    the OCaml interpreter ([vendor/react-trace]) is in place. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains notation programs interp machine.

Local Definition vint (n : Z) : val := VConst (CInt n).
Local Definition vstr (s : string) : val := VConst (CString s).

Local Definition FUEL : nat := 200.

(** Projection helpers (compute a small comparable piece of the result). *)
Local Definition run_out (P : prog) (evs : list nat) : res out_buf :=
  c_out <$> run_prog FUEL P evs.
Local Definition run_mode (P : prog) (evs : list nat) : res mode :=
  c_mode <$> run_prog FUEL P evs.
Local Definition run_state (P : prog) (evs : list nat) (p : path) (l : label)
    : res (option val) :=
  (λ c, state_at c p l) <$> run_prog FUEL P evs.
Local Definition run_display (P : prog) (evs : list nat) : res dtree :=
  run_prog FUEL P evs ≫= display_of FUEL.
Local Definition run_nviews (P : prog) (evs : list nat) : res nat :=
  (λ c, map_size (c_mem c)) <$> run_prog FUEL P evs.

(** ** Counter (§2.1): queued functional updates, update timing *)

Example counter_wf : comp_def_wf (CompDef "x" counter_body) = true.
Proof. vm_compute. reflexivity. Qed.

(** Initial render: "Counter", "Return"; state 0; quiescent. *)
Example counter_init_out :
  run_out counter_prog [] = Ok [vstr "Counter"; vstr "Return"].
Proof. vm_compute. reflexivity. Qed.

Example counter_init_display :
  run_display counter_prog [] = Ok (DList [DConst (CInt 0); DHandler]).
Proof. vm_compute. reflexivity. Qed.

(** One click: the queued updates run during the next render — after
    "Counter", before "Return" (the update-timing puzzle of §2.1) — and
    both updaters apply: s = 2. *)
Example counter_click_out :
  run_out counter_prog [0%nat] =
    Ok [vstr "Counter"; vstr "Return";
        vstr "Counter"; vstr "Update"; vstr "Return"].
Proof. vm_compute. reflexivity. Qed.

Example counter_click_state :
  run_state counter_prog [0%nat] 0 0 = Ok (Some (vint 2)).
Proof. vm_compute. reflexivity. Qed.

Example counter_click_mode : run_mode counter_prog [0%nat] = Ok MEvent.
Proof. vm_compute. reflexivity. Qed.

(** Two clicks: the updates accumulate across events (s = 4). *)
Example counter_two_clicks_state :
  run_state counter_prog [0; 0]%nat 0 0 = Ok (Some (vint 4)).
Proof. vm_compute. reflexivity. Qed.

(** ** SelfCounter (§2.2): an Effect creating an autonomous render cycle.
    Expected console: 0 Return Effect 1 Return Effect 2 Return Effect
    3 Return Effect. *)

Example selfcounter_out :
  run_out selfcounter_prog [] =
    Ok [vint 0; vstr "Return"; vstr "Effect";
        vint 1; vstr "Return"; vstr "Effect";
        vint 2; vstr "Return"; vstr "Effect";
        vint 3; vstr "Return"; vstr "Effect"].
Proof. vm_compute. reflexivity. Qed.

Example selfcounter_state :
  run_state selfcounter_prog [] 0 0 = Ok (Some (vint 3)).
Proof. vm_compute. reflexivity. Qed.

(** ** Inf2 (§3.1.2): unconditional top-level setter call — an infinite
    retry loop. The unbounded semantics diverges; the interpreter reports
    fuel exhaustion (never a [Stuck], never an [Ok]). *)

Example inf2_diverges : run_prog FUEL inf2_prog [] = OOF.
Proof. vm_compute. reflexivity. Qed.

(** ** Demo (§4.3): retry during init, effect-driven re-render, and
    reconciliation of the child view from () to a button. *)

(** Quiescent at s = 2 with the button mounted (paper's step (5)). *)
Example demo_state : run_state demo_prog [] 0 0 = Ok (Some (vint 2)).
Proof. vm_compute. reflexivity. Qed.

Example demo_display : run_display demo_prog [] = Ok DHandler.
Proof. vm_compute. reflexivity. Qed.

Example demo_mode : run_mode demo_prog [] = Ok MEvent.
Proof. vm_compute. reflexivity. Qed.

(** Clicking the button increments once more; the button stays. *)
Example demo_click_state :
  run_state demo_prog [0%nat] 0 0 = Ok (Some (vint 3)).
Proof. vm_compute. reflexivity. Qed.

(** ** Bin (Fig. 2): recursive components, array views, fresh paths.
    Bin 2 mounts a complete binary tree: 1 + 2 + 4 = 7 views. *)

Example bin_nviews : run_nviews bin_prog [] = Ok 7%nat.
Proof. vm_compute. reflexivity. Qed.

Example bin_display :
  run_display bin_prog [] =
    Ok (DList [DList [DConst CUnit; DConst CUnit];
               DList [DConst CUnit; DConst CUnit]]).
Proof. vm_compute. reflexivity. Qed.

(** ** Rules-of-React violations are [Stuck], not silent

    A child calling its parent's setter during render (scenario S12 of the
    paper's test suite errors in both React and React-tRace): Parent
    passes its setter to Child, and Child calls it at the top level of its
    body (Init phase, foreign path ⇒ APPSETCOMP inapplicable). *)

Example cross_setter_stuck :
  run_prog FUEL cross_setter_prog []
    = Stuck "setter of another component during render".
Proof. vm_compute. reflexivity. Qed.

(** ** Parent / Child (§3.2): the child's effect updates the parent's state
    (allowed, Normal phase), the parent re-renders and drops the child
    (reconciliation ()-branch); the child's state is gone. *)

Example eff_cross_state :
  run_state eff_cross_prog [] 0 0 = Ok (Some (VConst (CBool false))).
Proof. vm_compute. reflexivity. Qed.

Example eff_cross_display : run_display eff_cross_prog [] = Ok (DConst CUnit).
Proof. vm_compute. reflexivity. Qed.

(** ** Machine / interpreter cross-validation

    The small-step machine ([machine.v]) must produce exactly the same
    quiescent configuration (tree, memory, output) as the interpreter on
    every test program — this validates the machine definition (including
    its eager write-back deviation) before the inductive agreement proof
    exists. Machine fuel counts individual steps, hence the larger bound. *)
Local Definition MFUEL : nat := 20000.

Example agree_counter_init :
  machine_result MFUEL counter_prog [] = interp_result FUEL counter_prog [].
Proof. vm_compute. reflexivity. Qed.

Example agree_counter_click :
  machine_result MFUEL counter_prog [0%nat]
    = interp_result FUEL counter_prog [0%nat].
Proof. vm_compute. reflexivity. Qed.

(** Multi-event: the machine's event driver (one execution over the
    whole trace) agrees with the interpreter's per-event loop. *)
Example agree_counter_two_clicks :
  machine_result MFUEL counter_prog [0; 0]%nat
    = interp_result FUEL counter_prog [0; 0]%nat.
Proof. vm_compute. reflexivity. Qed.

Example agree_selfcounter :
  machine_result MFUEL selfcounter_prog []
    = interp_result FUEL selfcounter_prog [].
Proof. vm_compute. reflexivity. Qed.

Example agree_inf2 : machine_result MFUEL inf2_prog [] = OOF.
Proof. vm_compute. reflexivity. Qed.

Example agree_demo :
  machine_result MFUEL demo_prog [] = interp_result FUEL demo_prog [].
Proof. vm_compute. reflexivity. Qed.

Example agree_demo_click :
  machine_result MFUEL demo_prog [0%nat]
    = interp_result FUEL demo_prog [0%nat].
Proof. vm_compute. reflexivity. Qed.

Example agree_bin :
  machine_result MFUEL bin_prog [] = interp_result FUEL bin_prog [].
Proof. vm_compute. reflexivity. Qed.

Example agree_cross_setter :
  machine_result MFUEL cross_setter_prog []
    = interp_result FUEL cross_setter_prog [].
Proof. vm_compute. reflexivity. Qed.

Example agree_eff_cross :
  machine_result MFUEL eff_cross_prog []
    = interp_result FUEL eff_cross_prog [].
Proof. vm_compute. reflexivity. Qed.

(** * Executable conformance tests for the interpreter.

    Transcribes the paper's running examples in the surface notation and
    checks their observable behavior (output buffer, hook state,
    displays, view counts) by computation. These play the role of the
    react-trace test suite until the differential-testing harness against
    the OCaml interpreter ([vendor/react-trace]) is in place. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax domains notation interp machine.

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

(** ** Counter (§2.1 of the paper) — queued functional updates

<<
let Counter x =
  print "Counter";
  let (s, setS) = useState x in
  print "Return";
  [s, button (fun _ ->
    setS (fun s -> s + 1);
    setS (fun s -> print "Update"; s + 1))];;
Counter 0
>>

    The second updater prints, so its state update is not pure — the
    paper's example of the update-timing puzzle ("Update" is printed
    during the next render). *)
Definition counter_body : expr :=
  (print: Str "Counter" ;;
   let: "s", "setS" := useState "x" in
   print: Str "Return" ;;
   ⟪ "s";
     λ: "_", "setS" (λ: "s", "s" + 1) ;;
             "setS" (λ: "s", print: Str "Update" ;; "s" + 1) ⟫)%r.

Definition counter_prog : prog :=
  Prog [("Counter", CompDef "x" counter_body)] (Comp "Counter" 0)%r.

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

(** ** SelfCounter (§2.2) — an effect creating an autonomous render cycle

<<
let SelfCounter x =
  let (s, setS) = useState x in
  print s;
  useEffect (print "Effect"; if s < 3 then setS (fun s -> s + 1) else ());
  print "Return";
  [s];;
SelfCounter 0
>>

    Console: 0 Return Effect 1 Return Effect 2 Return Effect 3 Return
    Effect. *)
Definition selfcounter_body : expr :=
  (let: "s", "setS" := useState "x" in
   print: "s" ;;
   useEffect: (print: Str "Effect" ;;
               if: "s" < 3 then "setS" (λ: "t", "t" + 1) else #()) ;;
   print: Str "Return" ;;
   ⟪ "s" ⟫)%r.

Definition selfcounter_prog : prog :=
  Prog [("SelfCounter", CompDef "x" selfcounter_body)] (Comp "SelfCounter" 0)%r.

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

(** ** Inf2 (§3.1.2) — an unconditional top-level setter call

<<
let Inf2 x =
  let (s, setS) = useState x in
  setS (fun s -> s);
  s;;
Inf2 0
>>

    Retries forever (a blank screen in React). *)
Definition inf2_body : expr :=
  (let: "s", "setS" := useState "x" in
   "setS" (λ: "t", "t") ;;
   "s")%r.

Definition inf2_prog : prog :=
  Prog [("Inf2", CompDef "x" inf2_body)] (Comp "Inf2" 0)%r.

Example inf2_diverges : run_prog FUEL inf2_prog [] = OOF.
Proof. vm_compute. reflexivity. Qed.

(** ** Demo (§4.3) — retry during init, effect-driven re-render, and
    reconciliation of the child view from () to a button

<<
let Demo x =
  let (s, setS) = useState x in
  let f = fun s -> s + 1 in
  if s = 0 then setS f else ();
  useEffect (if s = 1 then setS f else ());
  if s <= 1 then () else button (fun _ -> setS f);;
Demo 0
>> *)
Definition demo_body : expr :=
  (let: "s", "setS" := useState "x" in
   let: "f" := λ: "t", "t" + 1 in
   (if: "s" = 0 then "setS" "f" else #()) ;;
   useEffect: (if: "s" = 1 then "setS" "f" else #()) ;;
   if: "s" ≤ 1 then #() else λ: "_", "setS" "f")%r.

Definition demo_prog : prog :=
  Prog [("Demo", CompDef "x" demo_body)] (Comp "Demo" 0)%r.

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

(** ** Bin (Fig. 2) — recursive components, array views, fresh paths

<<
let Bin n = if n = 0 then () else [Bin (n-1), Bin (n-1)];;
Bin 2
>> *)
Definition bin_body : expr :=
  (if: "n" = 0 then #()
   else ⟪ Comp "Bin" ("n" - 1); Comp "Bin" ("n" - 1) ⟫)%r.

Definition bin_prog : prog :=
  Prog [("Bin", CompDef "n" bin_body)] (Comp "Bin" 2)%r.

Example bin_nviews : run_nviews bin_prog [] = Ok 7%nat.
Proof. vm_compute. reflexivity. Qed.

Example bin_display :
  run_display bin_prog [] =
    Ok (DList [DList [DConst CUnit; DConst CUnit];
               DList [DConst CUnit; DConst CUnit]]).
Proof. vm_compute. reflexivity. Qed.

(** ** A child calling its parent's setter during render (a Rules-of-React
    violation; scenario S12 of the paper's test suite errors in both React
    and React-tRace)

<<
let Parent x = let (b, setB) = useState true in [Child setB];;
let Child set = set (fun t -> t); ();;
Parent ()
>> *)
Definition parent_body : expr :=
  (let: "b", "setB" := useState true in
   ⟪ Comp "Child" "setB" ⟫)%r.

Definition child_body : expr :=
  ("set" (λ: "t", "t") ;; #())%r.

Definition cross_setter_prog : prog :=
  Prog [("Parent", CompDef "x" parent_body); ("Child", CompDef "set" child_body)]
       (Comp "Parent" #())%r.

Example cross_setter_stuck :
  run_prog FUEL cross_setter_prog []
    = Stuck "setter of another component during render".
Proof. vm_compute. reflexivity. Qed.

(** ** Parent / Child (§3.2) — a child's effect updates the parent, which
    re-renders and drops the child

<<
let Parent x = let (b, setB) = useState true in if b then EffChild setB else ();;
let EffChild set = useEffect (set (fun _ -> false)); ();;
Parent ()
>> *)
Definition eff_parent_body : expr :=
  (let: "b", "setB" := useState true in
   if: "b" then Comp "EffChild" "setB" else #())%r.

Definition eff_child_body : expr :=
  (useEffect: "set" (λ: "_", false) ;; #())%r.

Definition eff_cross_prog : prog :=
  Prog [("Parent", CompDef "x" eff_parent_body);
        ("EffChild", CompDef "set" eff_child_body)]
       (Comp "Parent" #())%r.

Example eff_cross_state :
  run_state eff_cross_prog [] 0 0 = Ok (Some (VConst (CBool false))).
Proof. vm_compute. reflexivity. Qed.

Example eff_cross_display : run_display eff_cross_prog [] = Ok (DConst CUnit).
Proof. vm_compute. reflexivity. Qed.

(** ** Cursor semantics (design decision D2)

    Hooks are identified by their position among the hook calls of a
    render, not by the syntactic label. *)

(** [Cond] (§1 of the paper): a hook under a conditional. The first
    render calls one hook; after the click the re-render calls a second
    one, for which no slot exists — the machine is stuck ("Rules of
    Hooks"). The program is rejected by [body_ok] syntactically; the
    semantics catches the violation dynamically, which is what a "WP ⇒
    Rules of Hooks" theorem builds on. *)
Definition cond_body : expr :=
  EUseState 0 "b" "setB" (EConst (CBool false))
    (EIf (EVar "b")
       (EUseState 1 "s" "setS" (intc 0) (EVar "s"))
       (EFun "_" (EApp (EVar "setB") (EFun "b" (EUop UNot (EVar "b")))))).

Definition cond_prog : prog :=
  Prog [("Cond", CompDef "x" cond_body)] (EApp (ECompName "Cond") unit_e).

Example cond_not_wf : comp_def_wf (CompDef "x" cond_body) = false.
Proof. vm_compute. reflexivity. Qed.

Example cond_mounts : run_display cond_prog [] = Ok DHandler.
Proof. vm_compute. reflexivity. Qed.

Example cond_click_stuck :
  run_prog FUEL cond_prog [0%nat]
    = Stuck "Rules of Hooks: more hooks than in the previous render".
Proof. vm_compute. reflexivity. Qed.

(** Two hooks: slots by call order (0 then 1); the second setter updates
    slot 1. Labels are ignored (here deliberately not in order). *)
Definition two_body : expr :=
  EUseState 7 "a" "setA" (intc 1)
    (EUseState 3 "b" "setB" (intc 2)
      (EView [EVar "a"; EVar "b";
              EFun "_" (EApp (EVar "setB")
                          (EFun "v" (EBop BPlus (EVar "v") (intc 10))))])).

Definition two_prog : prog :=
  Prog [("Two", CompDef "x" two_body)] (EApp (ECompName "Two") unit_e).

Example two_slots :
  run_state two_prog [0%nat] 0 0 = Ok (Some (vint 1)) ∧
  run_state two_prog [0%nat] 0 1 = Ok (Some (vint 12)).
Proof. vm_compute. auto. Qed.

Example two_display :
  run_display two_prog [0%nat]
    = Ok (DList [DConst (CInt 1); DConst (CInt 12); DHandler]).
Proof. vm_compute. reflexivity. Qed.

(** A custom hook: a function containing a hook, called from the body.
    Its hook takes slot 0; the component's own hook takes slot 1. *)
Definition custom_body : expr :=
  ELet "useDouble"
    (EFun "init"
       (EUseState 0 "c" "setC" (EVar "init")
          (EBop BPlus (EVar "c") (EVar "c"))))
    (ELet "d" (EApp (EVar "useDouble") (EVar "x"))
      (EUseState 0 "s" "setS" (intc 0)
        (EView [EVar "d"; EVar "s";
                EFun "_" (EApp (EVar "setS")
                            (EFun "v" (EBop BPlus (EVar "v") (intc 1))))]))).

Definition custom_prog : prog :=
  Prog [("Comp", CompDef "x" custom_body)] (EApp (ECompName "Comp") (intc 21)).

Example custom_slots :
  run_state custom_prog [0%nat] 0 0 = Ok (Some (vint 21)) ∧
  run_state custom_prog [0%nat] 0 1 = Ok (Some (vint 1)).
Proof. vm_compute. auto. Qed.

Example custom_display :
  run_display custom_prog [0; 0]%nat
    = Ok (DList [DConst (CInt 42); DConst (CInt 2); DHandler]).
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

Example agree_cond :
  machine_result MFUEL cond_prog [0%nat] = interp_result FUEL cond_prog [0%nat].
Proof. vm_compute. reflexivity. Qed.

Example agree_two :
  machine_result MFUEL two_prog [0%nat] = interp_result FUEL two_prog [0%nat].
Proof. vm_compute. reflexivity. Qed.

Example agree_custom :
  machine_result MFUEL custom_prog [0; 0]%nat
    = interp_result FUEL custom_prog [0; 0]%nat.
Proof. vm_compute. reflexivity. Qed.

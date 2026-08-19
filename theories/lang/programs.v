(** * The programs.

    Every object-language program used in the tests ([lang/tests.v]) and
    verified in the examples ([examples/]), in the surface notation of
    [lang/notation.v], each with its source as in the paper. Reading this
    file first shows what the development is about; the tests and
    examples then only refer to these definitions.

    Conventions of the notation: a string literal is a variable; [Str s]
    is a string constant; numerals are integers; [#()] is unit; [Comp C]
    names a component and [Comp C v] is the component spec ⟨C, v⟩;
    application is juxtaposition; [⟪ e1; …; en ⟫] is a view (array);
    [let: x, xs := useState e in …] binds the state and its setter. *)
From react_iris Require Import prelude.
From react_iris.lang Require Import syntax notation.

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

(** ** A pure Counter — Counter without the printing updater, so that the
    model layer applies

<<
let Counter x =
  let (s, setS) = useState x in
  [s, button (fun _ -> setS (fun s -> s + 1); setS (fun s -> s + 1))];;
>> *)
Definition pure_counter_body : expr :=
  (let: "s", "setS" := useState "x" in
   ⟪ "s"; λ: "_", "setS" (λ: "s", "s" + 1) ;; "setS" (λ: "s", "s" + 1) ⟫)%r.

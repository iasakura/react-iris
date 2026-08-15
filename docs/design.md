# react-iris — Design Document

Specification and verification of React programs in Rocq + Iris, built on the
operational semantics of React-tRace (Lee, Ahn, Yi. OOPSLA 2025).

- Paper: https://arxiv.org/abs/2507.05234 (OOPSLA 2025, 42pp)
- Reference implementation: https://github.com/Zeta611/react-trace (OCaml 5)
- Environment: opam switch `cert-yjs` (Rocq 9.1.1, rocq-iris dev, rocq-stdpp
  dev, iris-named-props, coq-record-update). Proof development uses rocq-mcp.

---

## 1. Goals and Research Questions

We view a React program as an *implementation of an abstract state machine for
a UI*, and build a program logic in Iris where **the displayed value and the
callbacks of a component are specified as iProp assertions**. Five research
questions drive the project.

- **RQ1: Hook contracts** — What do useState / useEffect guarantee, and what
  must the *user* guarantee (updater purity, render purity, dependency-array
  completeness, termination of re-render loops, ...)? We formalize the user
  obligations as separation-logic proof obligations. We treat custom hooks as
  a *new module form* and give them modular specifications (abstract
  representation predicates).
- **RQ2: Component specifications** — Decorate component state with ghost
  state and invariants; specify "the displayed value is a function of the
  abstract state" and "callbacks are transitions of the abstract state" in
  iProp; at the top level obtain adequacy for arbitrary user-event sequences
  (refinement of an abstract LTS).
- **RQ3: Third-party state libraries** — Define what it means for jotai-style
  libraries to "behave correctly" with respect to React, and verify the
  escape-hatch style of low-level programming: external store + subscription +
  setState-forced re-render (the essence of useSyncExternalStore).
- **RQ4: Concurrency and async** — Extend the semantics with the render
  fragmentation, interruption, and prioritization introduced by useTransition
  / Suspense; specify these APIs and verify components that use them. The
  centerpiece: "render purity implies the concurrent machine refines the
  sequential semantics."
- **RQ5: Implementation correctness** — Prove that a simplified React
  implementation (in a JS-like imperative language) that keeps the key
  mechanisms — fibers, hook lists, update queues — refines the abstract
  semantics above.

---

## 2. Starting Point: The React-tRace Semantics

We summarize the structure that matters for this project (notation follows §4
/ Appendix A of the paper).

### 2.1 Two-layer structure

- **Render step transitions (small-step)** `⟨t, m, ω, δ, μ⟩ ↪ ⟨t, m', ω', δ, μ'⟩`
  - StepInit: evaluate the main expression to a view spec and mount it →
    rendered mode ❀
  - StepEffect: `commitEffs` (run effects of views carrying the Effect
    decision, post-order, in Normal phase) → check mode ↺
  - StepCheck: `check` (re-evaluate bodies of views carrying the Check
    decision, reconcile if needed) → re-render ❀ / otherwise • (event loop)
  - StepEvent: nondeterministically pick any handler closure reachable in the
    tree and run it in Normal phase → ↺. **The only nondeterminism = user
    input.**
- **Expression evaluation (big-step)** `Σ, σ ⊢ e ⇓ᵠₚ v, Σ', ω` with phase
  φ ∈ {Init, Succ, Normal} and path p. Component bodies are evaluated by a
  **retrying evaluation** ⇓̄ (EvalOnce / EvalMult: re-evaluate in Succ phase
  until the Check decision disappears, clearing the effect queue each time).
  Retrying may diverge (real React throws after 25 retries).

### 2.2 Semantic objects

- TreeMem `m : Path → View`,
  View `π = {spec: ⟨C,v⟩, dec ⊆ {Check, Effect}, sttst: ρ, effq: q, child: t}`
- SttStore `ρ : Label ℓ → {val: v, sttq: [cl]}` (committed value + queued
  updates)
- Tree `t ::= k | cl | [t̄] | p`; setter closures are `⟨ℓ, p⟩`
- **useState**: In Init, STTBIND (evaluate initial value, allocate a slot).
  In Succ, STTREBIND (*apply* the queued updaters in order and fold; if the
  value changed, add the Effect decision; flush the queue).
- **Setter application**: during rendering (Init/Succ) only the component's
  *own* setter is allowed (AppSetComp; calling another component's setter is
  stuck = the error in real React) and adds Check. In Normal phase
  (AppSetNormal) enqueue at an arbitrary path + Check.
- **useEffect**: only registers the thunk in effq (EFF). Execution happens in
  commitEffs, **only for views carrying the Effect decision (= state actually
  changed, or a setter was called during render)** — Thm 2 characterizes the
  execution condition.
- **reconcile**: same component name → re-evaluate in Succ and recursively
  reconcile the child; if the name/shape changed, re-init from scratch (state
  is dropped, a fresh path is allocated).

### 2.3 Metatheory (candidates for porting)

- Thm 1 (setter during render ⇔ retry occurs), Thm 2 (effect execution
  condition)
- Purity (Def 3) / normalization & similarity (Defs 4, 5) / **validity**
  (Def 6: domain of sttst = the label set of the body) / **stability**
  (Def 12: re-evaluation yields the same view) / **coherence** (Def 13:
  Check ⇔ non-empty queue), and the preservation lemmas (L14, 17, 18).
- Thm 8: React's "skip re-evaluation if the value is unchanged" optimization
  preserves behavior *provided updaters are pure* — the prototype of "a user
  obligation (purity) is what makes an optimization correct", which motivates
  our specification design (making obligations explicit).

### 2.4 Not modeled by the paper (extension candidates)

Dependency arrays and cleanup for useEffect; useRef / useMemo / useContext
(sketched in §7 of the paper); keyed reconciliation; dynamic slot allocation
for custom hooks; concurrent features (lanes / interruption / useTransition /
Suspense); mutable references and async in the base language; the DOM.

---

## 3. Architecture

Layers, bottom-up. Each layer depends only on the interface of the one below.

```
L5  examples/case-studies   counter, forms, useUndo, mini-jotai, transitions
L4  logic/component.v       component-spec pattern, abstract-LTS refinement,
                            adequacy
L3  logic/hooks.v runtime.v hook specs (useState/useEffect), runtime lemmas
                            (init/check/reconcile/commitEffs, proved once)
L2  logic/inst.v lifting.v  Iris language instance, state interpretation,
                            points-to family, basic WP lemmas
L1  lang/machine.v interp.v small-step machine + executable interpreter +
                            agreement with big-step + ported react-trace tests
L0  lang/syntax.v domains.v syntax and semantic objects (stdpp gmap based)
```

- **L1 (the semantics) is the single trusted base.** Everything above is
  proved sound against it.
- The react-trace OCaml implementation serves as an oracle (differential
  testing), pinned under `vendor/`.

---

## 4. Key Design Decisions

### D1: Mechanization style — a small-step machine that internalizes the runtime

To use Iris's WP and adequacy in full we need a small-step `language`
instance. React-tRace is "small-step render transitions + big-step expression
evaluation and semantic functions", so **we internalize the big-step parts
into the expression language and obtain a single small-step machine**.

- Machine expressions `E ::= source exprs (annotated with phase, path) |
  init(s) | reconcile(t,s) | commitEffs(t) | check(t) | retry(p, e) |
  dispatch-event | …`; the recursive structure of the semantic functions is
  represented by evaluation contexts (frame stacks).
- Physical state `σ = {m: gmap Path View; ω: list Val; nextPath;
  (later: heap, queues)}`. One thread. The mode μ is represented by the shape
  of the machine expression (• = waiting on dispatch-event).
- We instantiate Iris `language` directly (no forcing into ectxi). Adequacy
  yields "not stuck = no Rules-of-React violations".

Rejected alternatives:
- **Definitional WP over big-step**: cannot distinguish divergence from
  stuckness, so safety (excluding Rules-of-Hooks violations / setter misuse)
  cannot be a theorem; retry / re-render loops cannot be analyzed either.
- **(Guarded) Interaction Trees**: elegant but higher infrastructure risk.
  Worth revisiting for the async extension (M5).

As a sanity check we prove agreement between the paper's big-step ⇓ and the
machine on expression fragments (started in M2; a complete proof is not a
gate). The executable interpreter plus ported tests are the practical
conformance check.

### D2: Hook identity — static labels first, cursor semantics for custom hooks

- **Phases 1–2**: faithful to the paper: `useState^ℓ` (static labels +
  top-level syntactic restriction). The metatheory (validity / stability /
  coherence) ports directly.
- **Phase 3 (RQ1/RQ3)**: generalize to the **cursor (call-order) semantics**
  of real React. Motivation:
  1. With free composition of custom hooks as functions, static labels
     collide (calling useFoo() twice from one component collides useFoo's
     internal ℓ).
  2. Under cursor semantics, "Rules of Hooks violations" (hooks under
     conditionals etc.) become **stuckness by slot mismatch**, giving the
     theorem **"WP provable ⇒ Rules of Hooks respected"**. This upgrades a
     syntactic restriction into a provable property — a result in itself.
- The static-label fragment (programs satisfying the paper's syntactic
  restriction) is justified by an agreement lemma between the cursor and
  static versions, plus differential tests against react-trace.

### D3: Divergence (infinite retry / infinite re-render)

- The semantics stays **unbounded** as in the paper (divergence allowed).
  Partial-correctness WP does not exclude divergence.
- For convergence we also prove the runtime lemmas (check loop, retry) in a
  **measure-carrying form (total WP / well-founded induction)**: a user who
  supplies a "re-render measure" (e.g. `max(0, 3 − s)` for SelfCounter)
  obtains "after an event is processed, the machine reaches event-loop mode
  in finitely many steps and the display satisfies P". The infinite
  re-render pitfalls of §3 of the paper appear in the logic as "no measure
  exists".
- A React-faithful fueled variant (error = stuck at 25 retries / update depth
  50) is kept available as a parameter of the semantics (in the fueled
  variant, safety proofs imply termination). Default: unbounded.

### D4: State interpretation and ghost design

- Flatten `m : gmap Path View` into a points-to family backed by `ghost_map`:
  `p ↦spec ⟨C,v⟩`, `p ↦dec d`, `p ↦child t`, `p ↦effq q`,
  `(p,ℓ) ↦val v`, `(p,ℓ) ↦sttq [cl]`. View-record updates via
  coq-record-update.
- User-facing abstractions on top:
  - `model γ a` — abstract state attached to a hook instance (user-chosen
    RA). Represents the "logical current value" after the STTREBIND fold.
  - `isSetter s γ` — persistent knowledge that a closure is the setter.
  - `effRegistered p I` — proof-obligation token for a registered effect.
- **Per-mode protocols** (resource transfer across StepEffect / StepCheck /
  StepEvent) are proved once as runtime lemmas; users only see the
  component-spec interface.
- Key constraint: **render bodies are re-evaluated arbitrarily often**
  (retry, check, reconcile). Hence render-body specifications must be
  *idempotent*, of the shape
  `□ (model γ a -∗ WP body {s. model γ a ∗ view_ok a s})`
  (the logical counterpart of Stability, Def 12). Handler closures are
  invoked at adversarial times, so their specs are persistent, with
  resources supplied through invariants.

### D5: Binder representation — named variables, environment semantics

Syntax uses direct-style named binders (strings), not de Bruijn indices,
locally nameless, PHOAS, or nominal sets. This is safe for the planned
metatheory because **the development contains no substitution at all**:
the semantics is environment-based (closures ⟨λx.e, σ⟩), evaluation
never rewrites terms, and β-reduction is environment extension. All the
classic pains of named binders (capture avoidance, α-equivalence,
substitution lemmas) originate in substitution into terms and therefore
never arise. The metatheory we plan — machine/interpreter agreement, the
paper's invariants, hook specs, the fiber refinement (a simulation
between two environment machines, relating closures as "same body +
related environments") — manipulates configurations, not binders. The
worst case on the horizon is environment weakening ("only free variables
matter"), which is a routine structural induction under named syntax.

Precedent: Iris's HeapLang is named (strings + stdpp [binder]) *with*
substitution — naive, shadowing-aware, non-capture-avoiding — sound
because only closed values are ever substituted; its `metatheory.v`
(closedness, parallel [subst_map], substitution lemmas) is explicitly
"not needed for verifying programs" and exists for logical-relations
developments. RustBelt-scale developments run on this. We are strictly
on the safer side: no substitution means no closedness bookkeeping
either. Conversely, the first-order named deep embedding is what keeps
the executable interpreter, the `vm_compute` test suite, and the
correspondence with react-trace source programs readable (PHOAS would
break decidable equality and executability; de Bruijn would obscure the
tests).

Known boundary: verifying *term-rewriting transformations* (e.g., a
React-compiler-style memoization pass, §7 of the paper) would move terms
across binders and reopen the freshness question. If we go there, the
plan is a local detour — compile named syntax to a nameless
representation for that study — rather than changing the base language.

Note one deliberate consequence: STTREBIND's value comparison
([vₙ ≢ v₀]) is syntactic, so α-equivalent-but-distinct closures compare
unequal. This is faithful to JavaScript reference equality on functions
(a callback recreated on each render is a different value in React).

### D6: Conformance with the paper and the real implementation

- Besides the machine, write a **fueled executable interpreter** in Rocq and
  prove it agrees with the machine. Port the react-trace test suite (18
  scenarios, 38 tests; compare output buffer ω and final tree) and run it via
  `vm_compute`.
- After extensions (cursor, deps, cleanup), keep differential tests against
  the OCaml implementation as an oracle on the shared fragment.

### D7: Observations and the shape of the top-level theorem

Observations = the trace ω of `print` + the displayed tree `display(m, t)` in
quiescent states (event-loop mode), realizing constants / closures / arrays
recursively.

The final theorem for a verified component (adequacy-style) is **refinement
of an abstract LTS**:

```
Theorem component_adequacy :
  (⊢ component_spec C M V) →
  ∀ (ev : list Event),                (* any handler choices = user input *)
    run (C, arg) ev is not stuck ∧
    every quiescent state satisfies ∃ a, M.reachable a ∧ display = V a.
```

This makes RQ2's "display is a function of the abstract model; callbacks are
abstract transitions" the top-level claim itself.

---

## 5. Approach per Research Question

### RQ1: useState / useEffect contracts and user obligations

**useState** (shape of the user-facing derived rules):

- Mount (Init):
  `{slot p free} let (x, set) = useState e in k
   {∃γ. model γ v₀ ∗ isSetter set γ ∗ …}` — slot + ghost allocation.
- Re-render (Succ): STTREBIND reads the folded `model γ a` and continues with
  `x = a`. **The queue contents are never exposed to the user** (only the
  folded logical value).
- Setter call (Normal):
  `isSetter set γ ∗ updPure f f̂ ⊢ {model γ a} set f {model γ (f̂ a)}`
  - `updPure f f̂`: the **user obligation** that applying the closure f
    computes the meta-function f̂ deterministically and without side effects
    (the logical form of Def 3). Without it (a) the STTREBIND fold could
    have arbitrary effects and no specification would be possible, and
    (b) React's re-evaluation-skipping optimization (Thm 8) breaks. "Why
    must updaters be pure" thus shows up as a proof obligation.
- Setter during render (Init/Succ): only the component's own setter is
  allowed (anything else is stuck, so WP proofs rule it out automatically).
  Calling it obligates a **retry measure** (D3).

**useEffect**:

- Registration: `{…} useEffect e {effRegistered p (I, E)}` — I an effect
  invariant, E the body spec.
- Execution is handled by the runtime lemma (commitEffs), which demands
  `□ (I -∗ WP e @ Normal {I})` at registration. If the effect calls a
  setter, its contribution to the Check–Effect cycle must be paid by a
  measure (no measure = suspected infinite re-render).
- The execution condition (only views whose state actually changed) becomes
  the logical form of Thm 2, as a derived rule. We provide both the weakest
  guarantee including "the effect may not run", and after the deps
  extension, "the effect runs when deps changed".
- **Extension (M3)**: dependency arrays + cleanup. Stale-closure bugs appear
  naturally in the logic: only specs about the values captured at
  registration time are available, so proofs relying on current state fail.
  Cleanup is the obligation to "return I before the next run / unmount".

**Catalog of user obligations** (= the core of the answer to this RQ):
updater purity / render purity (from M4 on: no external-store writes; in M5
it becomes the premise for interruptibility) / measures for effect-driven
re-renders / deps completeness / cleanup return.

**Status (M3, first instalment — `logic/hooks.v`, `logic/model.v`).**
Realized as follows:

- `updPure` is `upd_pure D cl f`: the updater closure computes the
  meta-function `f` on domain `D`, stated as a *resource-free WP
  implication* (`WP (result) -∗ WP (closure body)`, with no `reg_token` /
  `mem_auth_frag` / `out_frag` in hand). Every state-changing machine step
  needs one of those resources, so only state-preserving evaluation
  satisfies it — printing or calling a setter inside an updater is ruled
  out by construction. Concrete discharge by symbolic execution:
  `upd_pure_inc` (`λt. t+1`).
- STTREBIND for a pure queue is `wp_usestate_succ_pure`: the re-render
  binds the mathematical fold of the queued functions, flushes the queue,
  and gets the Effect decision iff the value changed. The paper's Counter,
  whose second updater prints, is handled only by concrete symbolic
  execution of that queue (`counter_body_succ_click`).
- `model γ a` is the client half of a ghost variable holding the logical
  value; `slot_res D γ ent` is the runtime half tied to the physical slot
  (pure queue realized by `fs`, ghost = `fold fs committed`).
  `wp_setter_normal_model`: `model γ a` ↦ `model γ (f a)` while enqueuing
  `f`; `wp_usestate_succ_model`: the body binds exactly `a`, the model is
  unchanged (rendering never changes the logical state).
- `isSetter` is not yet a separate assertion: setter identity is currently
  the closure value `VSetter ℓ p` itself (static labels, D2 phase 1).
- useEffect: registration is `wp_useeffect`; execution goes through
  `wp_commit_effects` with per-effect `effect_spec Sᵢ Sᵢ₊₁` (a resource
  chain — effects that call setters change state). The measure story of D3
  is instantiated concretely in SelfCounter (`cycle k`, measure `3 − k`).
  `effRegistered`, deps, and cleanup are not yet formalized.

### RQ2: Components = ghost state + invariants; display and callbacks in iProp

The component-spec shape (the central L4 interface):

```
component_spec C (M : LTS A) (V : A → ViewSpec → iProp) :=
  ∃ R : A → iProp,                    (* representation predicate *)
    (* mount: establish the initial abstract state *)
    {True} mount C arg {∃ a₀, ⌜M.init a₀⌝ ∗ R a₀}
  ∗ (* render: idempotent (D4); display is a function of the abstract state *)
    □ ∀ a, R a -∗ WP body @ (Succ) {s. R a ∗ V a s ∗ handlers_ok M a s}
  ∗ (* handlers_ok: for each closure h in the view,
       □ {R a} h () @ Normal {∃ a', ⌜M.step a (label h) a'⌝ ∗ R a'} *)
```

- R bundles the hooks' `model γ` and invariants, tying them to the abstract
  state a.
- Handlers are chosen adversarially (in any quiescent state), hence
  persistent specs.
- The top level is the refinement theorem of D7. Parent/child composition:
  verify the parent assuming the child's component_spec (value passing via
  props; setter passing = passing `isSetter`).

**Status (M3, first instalment).** `component_spec` itself is not yet
defined; its ingredients are: runtime lemmas in CPS
(`logic/runtime.v`: `body_spec`, `wp_init_component`, `wp_check_component`,
`wp_commit_effects`, event driver), and two end-to-end examples with the
D7 theorem shape — `examples/counter_modular.v` (`counter_trace_adequate`:
for every click trace, never stuck, display `2·|evs|`, exact output;
`counter_click_step` is the concrete form of "the callback is the +2
transition") and `examples/selfcounter.v` (`selfcounter_adequate`: the
effect-driven cycle converges at 3 with the exact console of §2.2). In
model form: `examples/pure_counter.v` (`click_model`:
`{model γ n} click {model γ (n+2)}`; `body_succ_model`: display `[a; h]`
from `model γ a`). Adequacy with the final physical state is
`react_adequacy_state`.

### RQ3: Custom hooks as modules, and their modular specification

The specification of a custom hook `useFoo` is a triple:

```
hookSpec useFoo :=
  ∃ fooRep : Ghost → Params → iProp,  (* abstract rep pred (hides slot count) *)
    (* mount rule *)
    {hookCtx Init} useFoo args {r. ∃γ. fooRep γ ∗ retSpec γ r}
  ∗ (* re-render rule *)
    □ {hookCtx Succ ∗ fooRep γ} useFoo args {r. fooRep γ ∗ retSpec γ r}
  ∗ (* effect-side obligations are folded into fooRep as effRegistered *)
```

- `hookCtx` is a "hook-execution permission + cursor" token. Existentially
  quantifying the cursor position hides **how many slots the hook consumes**
  (= implementation independence). This is the core reason D2 needs cursor
  semantics.
- Component verification depends only on hookSpec, so hand-written useState
  and custom hooks compose through the same interface. "A custom hook = a
  new module form whose specification is (representation predicate,
  re-establishment rule, effect obligations)" is the intended answer to
  RQ1/RQ3. Case studies: useCounter, useToggle, usePrevious, useUndo,
  useDebounce (after the deps extension).

### RQ4: jotai / external stores and escape hatches

- Add ML-style references (a heap) to the base language (M4). mini-jotai:
  `store = {atoms: gmap AtomId Val; listeners: gmap AtomId (list cl)}` with
  `get / set / sub / unsub`.
- Verified pattern (the desugared form of useSyncExternalStore):
  `useState(getSnapshot()) + useEffect(sub (λ_. setS (getSnapshot())))` +
  reading the snapshot at render time.
- **Synchronous-mode theorem**: if renders are store-pure (read-only) and
  getSnapshot is pure, then (1) no tearing within a single render pass (the
  store is constant during one pass), and (2) in quiescent states the
  display equals the current store value (eventual consistency).
  "Why is jotai correct" decomposes into: an implementation satisfying the
  store specification (logically atomic set + complete listener
  notification) + adherence to the pattern.
- The store spec is written in the style of Iris concurrent data-structure
  specs (logical atomicity or invariant + ghost map). The "low-level
  programming" of RQ3 is precisely the specification of this layer
  (refs + subscription + forced re-render).

### RQ5 (interest 4): useTransition / Suspense — the concurrent machine

- Machine extension (M5): lane-annotated (priority) update queues, a
  work-in-progress tree (double buffering), **interruption/abort of render
  passes** (StepEvent may preempt an in-progress render), atomic commit.
  Suspense: "body evaluation returns a suspend value → nearest boundary
  displays the fallback; a promise-resolution event retries". Async adds an
  event/microtask queue to the base language.
- **Central theorem: render purity ⇒ the concurrent machine refines the
  synchronous machine (M1)** (observational equivalence). This formalizes
  *why* React demands render purity, connecting back to RQ1's obligation
  list. In the other direction: a counterexample showing the naive
  store-reading pattern tears under concurrency, and a proof that
  useSyncExternalStore's consistency check restores the refinement.
- API specs: `startTransition f` enqueues on the transition lane
  (`{model γ a} … {pendingTransition γ …}`), a display spec for `isPending`,
  and the scheduler property that urgent updates are not blocked by
  transitions (no priority inversion). Since React itself has no formal
  spec here, theorems are stated **parametrically over a family of
  schedulers**.

### RQ6 (interest 5): implementation verification

- FiberLang: implement a mini React in an imperative language with refs,
  records, and linked lists (an extension of the base language): fiber nodes
  (child/sibling/return), hook linked list + cursor, update queues (circular
  lists), workLoop / beginWork / completeWork / commitRoot.
- **Forward simulation into the abstract machine (L1), in Iris**: ReLoC /
  Simuliris style — carry the source (abstract-machine) configuration as a
  ghost resource and drive the simulation through the target WP. Since L1
  configurations are gmap-based, ghost-reflecting them is direct.
- Scope control: synchronous mode, no lanes first. Interruption is a stretch
  goal.

---

## 6. Roadmap

| M | Contents | Acceptance criteria |
|---|----------|---------------------|
| M0 | Infra: `_CoqProject` + Makefile, CI, rocq-mcp flow, vendored react-trace | Iris imports build (sanity done), CI green |
| M1 | L0/L1: syntax, semantic objects, small-step machine, executable interpreter | Ported react-trace tests agree under `vm_compute`. Array-free fragment first → arrays & recursive views |
| M2 | L2: language instance, state interp, WP, adequacy, basic points-tos | Safety (not stuck) + display spec proved for Counter |
| M3 | L3/L4: hook specs, runtime lemmas, component_spec, logical Thm 1/2, **cursor semantics + custom hooks**, deps + cleanup | 3 custom hooks verified modularly; "WP ⇒ Rules of Hooks" theorem. *Done so far:* hook rules + purity obligation, model layer, runtime lemmas, Counter trace theorem, SelfCounter cycle |
| M4 | Refs + mini-jotai + synchronous useSyncExternalStore theorem | Eventual-consistency proof for the jotai pattern |
| M5 | Concurrent machine + refinement theorem + useTransition / Suspense specs | Purity ⇒ refinement; tearing counterexample and recovery via uSES |
| M6 | FiberLang implementation refinement (stretch) | Forward simulation for synchronous mode |

M1 is the heaviest. Its machine frame structure couples with the M2 language
instance, so we validate it early with an M2 prototype (a full WP round trip
on Counter).

## 7. Repository Layout and Development Conventions

```
react-iris/
  _CoqProject             (source of truth for paths and files)
  Makefile                (wrapper around coq_makefile)
  theories/
    prelude.v
    lang/     syntax.v domains.v machine.v interp.v tests/
    logic/    inst.v state_interp.v lifting.v hooks.v runtime.v component.v
    examples/ counter.v ...
  docs/design.md          (this document)
  vendor/react-trace      (git submodule, oracle)
```

- Build: `make` (coq_makefile from `_CoqProject`, in-source `.vo` so that
  coq-lsp / rocq-mcp resolve project modules directly). dune may be adopted
  later for OCaml extraction or vendor composition if needed.
- Proof development: rocq_start (preamble mode) → rocq_check /
  rocq_step_multi for iteration; rocq_compile_file when done. Restart the
  session after file edits.
- **Caveat**: the repository root contains an `_opam` symlink, so the
  rocq-mcp workspace must always contain a `_CoqProject` / `dune-project`
  (otherwise coqc scans `_opam` and the load path breaks; confirmed).
- Readability: use iris-named-props; View updates via coq-record-update.
- Language: development, comments, and committed documentation are in
  English. (A Japanese draft of this document is kept locally as
  `docs/design.ja.md`, untracked.)

## 8. Related Work (positioning)

- React-tRace (OOPSLA25): the foundation. No program logic or mechanization;
  this project takes the "semantics → verification" step.
- λ_react (Madsen et al., ECOOP 2020): a core calculus for the
  class-component generation.
- Crichton & Krishnamurthi (POPL 2024): a document calculus.
- Iris / HeapLang, ReLoC / Simuliris (refinement techniques for M6), gitrees
  (an alternative for async), WebSpec (browser formalization in Rocq).
- Separation-logic verification of UI frameworks is largely unexplored; RQ2's
  "display + callback specs in iProp" alone is novel.

## 9. Risks and Mitigations

1. **Mechanization cost of M1** (mutual recursion of
   init/check/reconcile/commitEffs + array views)
   → stage it: array-free fragment first. Write the executable interpreter
   first and let tests catch distortions early.
2. **Fit with the Iris language interface** (value/expression distinction,
   one thread, representing the mode) → run the M2 prototype alongside M1
   and freeze the frame design early.
3. **Cursor-semantics generalization breaking the metatheory** → keep the
   agreement lemma with the static-label fragment and the ported tests as
   regressions.
4. **The concurrent extension (M5) has no official spec in React itself** →
   schedule a study task on lanes first; parameterize the scheduler and
   state theorems "for a family of schedulers".
5. **Idempotent render specs complicating user-facing specs** → enforce the
   □ form in the library and validate ergonomics on examples (Counter in M2
   is the touchstone).

# react-iris

Specification and verification of React programs in [Rocq](https://rocq-prover.org/)
with [Iris](https://iris-project.org/), based on the operational semantics of
[React-tRace](https://github.com/Zeta611/react-trace)
(Lee, Ahn, Yi. *React-tRace: A Semantics for Understanding React Hooks*,
OOPSLA 2025, [arXiv:2507.05234](https://arxiv.org/abs/2507.05234)).

The goal is a program logic in which the displayed value and the callbacks of
a React component are specified as Iris assertions: hook contracts and their
user obligations (useState / useEffect / custom hooks), component
specifications as refinements of abstract state machines, correctness of
external-store libraries (jotai / useSyncExternalStore), the concurrent
semantics behind useTransition / Suspense, and — as a stretch goal — a
verified fiber-based mini implementation of React.

See [docs/design.md](docs/design.md) for the design document and roadmap.

## Status

Done so far:

- **The React-tRace calculus, executable** (`theories/lang/`): syntax
  and semantic objects, a fueled interpreter and a small-step machine,
  cross-validated against the paper's examples (`tests.v`).
- **A program logic over the machine** (`theories/logic/`): an Iris
  language instance with a per-view points-to state interpretation and
  adequacy; a WP rule per machine step; hook rules carrying the
  updater-purity obligation (`hooks.v`); render-loop lemmas
  (`runtime.v`); the value of a useState slot as ghost state
  (`slots.v`); component specifications as refinements of an abstract
  LTS (`component.v`).
- **Verified examples** (`theories/examples/`): Counter — for every
  click trace, the machine never gets stuck and displays twice the
  number of clicks, with the exact output; SelfCounter (the
  effect-driven render cycle), Parent/Child (a cross-component setter),
  and a pure Counter specified against the ghost state.

In progress: custom hooks and the "WP ⇒ Rules of Hooks" theorem under
cursor semantics; generic render-loop lemmas.

See [docs/design.md](docs/design.md) for the design decisions and the
roadmap.

## Build

Requirements: Rocq 9.1.1 with dev pins of
[stdpp](https://gitlab.mpi-sws.org/iris/stdpp),
[Iris](https://gitlab.mpi-sws.org/iris/iris),
[iris-named-props](https://github.com/tchajed/iris-named-props), and
[coq-record-update](https://github.com/tchajed/coq-record-update)
(see `.github/workflows/ci.yml` for exact commits).

```sh
make        # builds theories/ via coq_makefile
make clean
```

## Layout

```
theories/
  prelude.v      common imports and options
  lang/          syntax, semantic domains, executable interpreter, machine, tests
  logic/         Iris language instance, lifting, redex rules, hook layer,
                 runtime lemmas, slot layer, component specs, adequacy
  examples/      verified example components
docs/design.md   design document
vendor/react-trace  reference interpreter (oracle for differential tests)
```

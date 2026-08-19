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

- **M0–M2 done.** Syntax and semantic objects; a fueled executable
  interpreter and a small-step machine for the React-tRace semantics,
  cross-validated on the paper's examples (`theories/lang/tests.v`); an
  Iris language instance with a per-view points-to state interpretation,
  `wp_bind`, and adequacy (`theories/logic/{inst,lifting,adequacy}.v`).
- **M3 in progress.** Redex rules for every machine step, a hook layer
  with the updater-purity obligation (`hooks.v`), runtime lemmas
  (`runtime.v`), a slot layer for the logical values of hook slots
  (`slots.v`), and root component specifications as refinements of an
  abstract LTS (`component.v`). Verified examples: Counter (a trace
  theorem: for every click trace, safe and displaying twice the number
  of clicks), SelfCounter (the effect-driven cycle), Parent/Child, and a
  pure Counter in slot form (`theories/examples/`).

See the roadmap in [docs/design.md](docs/design.md) §6.

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

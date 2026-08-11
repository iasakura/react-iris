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

Early stage: project infrastructure (M0) and the formalization of the
React-tRace core calculus (M1) are in progress.

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
  lang/          syntax, semantic domains, machine, executable interpreter
  logic/         Iris language instance, program logic, hook/component specs
  examples/      verified example components
docs/design.md   design document
vendor/react-trace  reference interpreter (oracle for differential tests)
```

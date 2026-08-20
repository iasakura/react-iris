# WP rule inventory and reorganization plan

Status: proposal (nothing moved yet). Motivation: the current file split
(`step_rules.v` / `runtime_rules.v` / `runtime.v`) is arbitrary — the first
two are the same kind of thing cut in half, and `runtime.v` sounds like
`runtime_rules.v` while being a different kind of thing.

## 1. What kinds of WP rules exist

Every rule in the development is one of four kinds:

| kind | shape | reasoning content |
|---|---|---|
| **K1 footprint** | parametric in the redex: "a deterministic step that touches only the register / only view `p` / only the output" | owns exactly the state-interp update; proved once against `state_interp` |
| **K2 redex** | one rule per machine redex, literally transcribing `mstep` | zero — each is a one-line instance of a K1 rule |
| **K3 derived spec** | a hook or phase with a *specification* (fold of a pure queue, CPS through a whole body/mount/check/commit) | real proofs; where obligations (`upd_pure`) and abstraction (`next_state`) appear |
| **K4 top theorem** | abstract LTS refinement, generic render loops, adequacy export | the D7 theorem shape |

## 2. Inventory (per current file)

### `lifting.v` — resources + some K1
K1: `wp_mstep_det` (full state), `wp_pure_step` (state-free), `wp_print`
(output only), `wp_fill` (bind), `wp_mrun_ok` (whole run by computation).
Resources: `view_ptsto`, `mem_auth_frag`, `reg_token` (+ `render_ctx` /
`render_idle`), `out_frag`, `own_cfg`.

### `step_rules.v` — the rest of K1, then K2 for in-body evaluation
K1 (misplaced here): `wp_reg_step`, `wp_mem_read_step`, `wp_mem_write_step`,
`wp_mem_alloc_step`.
K2 (Fig. 5/6, evaluation & hooks): `wp_body_enter`, `wp_usestate_init`,
`wp_usestate_bind`, `wp_usestate_succ_nil`, `wp_usestate_succ_cons`,
`wp_sttfold_nil`, `wp_sttfold_cons`, `wp_useeffect`, `wp_setter_comp`,
`wp_retry_done`, `wp_retry_again`.

### `runtime_rules.v` — K2 for the tree transitions
K1 (misplaced here): `wp_mem_only_write_step`, `mem_lookup`.
K2 (Fig. 7/8): init `wp_init_comp` / `wp_mount` / `wp_init_finish`;
reconcile `wp_recon_comp_same` / `wp_recon_comp_new` / `wp_recon_writeback`
/ `wp_recon_finish`; check `wp_check_idle` / `wp_check_enter` /
`wp_check_writeback_eff` / `wp_check_writeback_noeff` / `wp_check_finish`;
commit `wp_commit_idle` / `wp_commit_enter` / `wp_commit_finish_u` /
`wp_commit_finish_v`.

### `hooks.v` — K3, hook rules with obligations
`upd_pure` / `queue_pure` / `fold_upd`; `wp_usestate_mount`,
`wp_usestate_succ_pure`, `wp_sttfold_pure`, `wp_setter_normal`.

### `slots.v` — K3, ghost layer for slot values
`next_state` / `slot_res`; `slot_alloc`, `slot_enqueue`,
`next_state_committed`; `wp_usestate_mount_slot`, `wp_usestate_succ_slot`,
`wp_setter_normal_slot`.

### `runtime.v` — K3, CPS lemmas per lifecycle phase
`body_spec` / `wp_body_once`; `wp_init_component` (mount);
`wp_check_component` (re-render); `effect_spec` / `wp_commit_effects` /
`wp_commit_finish_any` (effects); `wp_event_dispatch` / `wp_events_done`
(event driver); path-free subtree lemmas `wp_commit_free` /
`wp_check_free` / `wp_init_free` / `wp_recon_free`.

### `component.v`, `root.v` — K4
`root_spec` / `root_obligations` / `root_adequacy`;
`leaf_data` / `leaf_obligations` / `leaf_root_obligations`.

## 3. Usage audit — what is currently dead

Counting uses outside the defining lemma, on `cursor-hooks` (superset):

| rule | uses | verdict |
|---|---|---|
| `wp_recon_comp_same/new`, `wp_recon_writeback`, `wp_recon_finish` | 0 | the RECONCILECOM* path — needed for *non-leaf* roots (a component child that re-renders); no example reaches it yet |
| `wp_setter_comp` | 0 | setter called *during* rendering; no example does this yet (it is how "render reads a fresh setter" works) |
| `wp_commit_idle` | 0 | commit passing an Effect-off path; unreached because examples commit only the root, with Effect on |
| `next_state_committed` | 0 | agreement helper, never needed so far |
| `wp_usestate_mount_slot` | 0 | slot-form mount; `pure_counter.v` only exercises click + re-render |
| everything else | ≥ 1 | in use |

Recommendation: **keep all K2 rules** (each is the unique logical
transcription of one machine redex; deleting them loses Fig. 7 coverage and
they cost one line each) but group the unexercised ones under an explicit
"not yet exercised — needed for non-leaf roots" header. Drop or keep
`next_state_committed` / `wp_usestate_mount_slot` freely; they are two
lines and complete the slot API, so keeping is suggested.

There are no duplicated rules: `wp_usestate_succ_pure` (K3) *derives from*
`wp_usestate_succ_nil/cons` + `wp_sttfold_nil/cons` (K2), and
`wp_commit_finish_any` (K3) from `wp_commit_finish_u/v` (K2) — the K2 forms
are the base cases of those inductions, not redundancy.

## 4. Proposed layout

One file per kind, named by what it contains:

| file | content | change |
|---|---|---|
| `inst.v` | language instance | unchanged |
| `lifting.v` | resources + **all** K1 footprint rules (`wp_reg_step`, `wp_mem_*_step`, `mem_lookup` move in) | absorb strays |
| `redex_rules.v` | **all** K2 rules, one section per machine dispatch: evaluation & hooks (Fig. 5/6), init, reconcile, check, commit (Fig. 7/8), with the unexercised group marked | = `step_rules.v` ∪ `runtime_rules.v`, minus the strays |
| `hooks.v` | K3 hook rules + obligations | unchanged |
| `slots.v` | K3 ghost slot layer | unchanged |
| `lifecycle.v` | K3 CPS phase lemmas + path-free subtree lemmas | renamed from `runtime.v` |
| `component.v`, `root.v` | K4 | unchanged |

Reading order = dependency order:
`inst → lifting → redex_rules → hooks → slots → lifecycle → component → root`.

Rationale for the names: "redex rules" says exactly what the K2 file is
(one rule per redex, no reasoning); "lifecycle" is the React word for what
`runtime.v` proves (mount / re-render / effects / events). The
`*_rules`-vs-`*` confusion disappears because only one file keeps the
`_rules` suffix, and it is the one that is nothing but rules.

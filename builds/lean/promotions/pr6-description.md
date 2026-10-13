# PR-6 — Curve-bootstrapping module (new FixedIncome/Bootstrapping.lean, 34 public declarations)

**Branch**: `ito-drift-expectation` (fork: leafyoung/formal-mathfin) — apply
`pr6-bootstrapping-module-porttest.lean` as
`mathfin/MathFin/FixedIncome/Bootstrapping.lean` (lines 1–666, i.e. minus the
port-test audit appendix) + one root-import line after `YieldCurve` in
`MathFin.lean`.

## Statement

New module promoting the workspace curve-bootstrapping build (provenance: course
lesson 0030; `builds/lean/hw_bootstrap.lean`, QUEUE.md item 13) into
`namespace MathFin.Bootstrapping`:

- **Private search engine + public geometry**: `bisectStep`/`bisect`/`bisectMid`
  definitions with the 8 engine facts private; FRA and swap **threshold bridges**
  (`threshold_affine`, `threshold_of_strictMonoOn/AntiOn`), the affine bootstrap
  step with its ⌈log₂⌉ step budget (`affineStep_*`), root-identification
  (`fraRoot_parForward`, `swapRoot_is_par`, …), the repricing induction
  (`boot_reprices_all`, `boot_reprices_range`), and the flat-curve capstone
  (`fraBootstrap_flatCurve`).
- **Boundary (one sentence, mirrored in the docstring)**: `FixedIncome/YieldCurve.lean`
  owns the closed-form `bootstrap_solve*` names; this module owns the
  *search-based* bootstrap for models without closed forms.

## Disclosure (bisection engine)

The workspace build pin predates `Foundations/Bisection.lean`, so the module
self-contains a private bisection engine; its three definitions are public because
the module's own statements name them (the AC-face module system forbids private
names in public statement positions), and its eight facts are private. Under the
two-level namespace these are `MathFin.Bootstrapping.*` — shadow-free against the
public flat-`MathFin` `Bisection` names. **Switching the engine to the now-existing
public `Foundations/Bisection` module is the natural follow-up** (the source was
verified present at mathfin HEAD; names cited in `builds/lean/memos/pr-6-memo.md`).

## Verification transcript

- Local gate (AC build face, toolchain v4.32.0 / mathlib 81a5d257): built
  incrementally in 5 checkpoint compiles, each exit 0; final
  `lake env lean ../builds/lean/port-test-boot.lean` → exit 0, no warnings; **34**
  `#print axioms` lines, every one `[propext, Classical.choice, Quot.sound]`; zero
  sorry/admit. All consumed MathFin names verified on the face (`fraForwardRate`,
  `fraValue*`, `annuity`, `payerSwapValue*`, `parSwapRate`, `zcb`, `zcb_pos` — with
  one memo line-number drift corrected: `zcb` at ZCB.lean:39 on this face).
- Canonical gate: the CI trio in the verify container (this PR); local face is
  v4.32.0 vs CI's v4.33.0-rc1 — the trio retires the residual.

## Bookkeeping

Course-neutral docstrings (zero grep hits for lesson/Bagaria/desk/pin markers);
46 scratch declarations all present, scratch order preserved; deltas are exactly
header/namespace/privatization/audit. Coverage tables are benchmark-id-keyed with
no Bootstrapping rows; no rows added.

## Provenance

Course lesson 0030. Workspace: `builds/lean/hw_bootstrap.lean` (QUEUE.md item 13),
dep-map `builds/lean/memos/pr-6-memo.md`.

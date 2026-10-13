# PR-2 — HullWhite: calibration delta (3 theorems + calibMean refactor)

**Branch**: `ito-drift-expectation` (fork: leafyoung/formal-mathfin) — apply
`pr2-hullwhite-delta.patch` (or commit the staged working-tree change).

## Statement

Extends `MathFin/Foundations/HullWhiteCalibration.lean` by the final three-lemma
landing of the workspace Hull–White build (provenance: course lesson 0020;
`builds/lean/hw_scratch.lean`):

- `deterministic_const_closed_form` — closed-form corollary of `deterministic_const`
  (one rewrite + the definitional unfold of `vasicekDeterministic`).
- `mean_eq_forward` — the calibration mean identity generalized to `κ ≠ 0`; the
  previously landed `calibMean` (κ > 0) now routes through it, replacing its
  standalone uniqueness proof with a one-line application (one proof body, same
  statement).
- `calibCorrection_integral` — the integrated calibration-correction identity,
  packaged via the existing private `calibVar_key`.

## Honest hypothesis list

Unchanged from the module's existing theorems: `ContDiff ℝ 1 f0` packaging the
derivative + continuity conditions (via `contDiff_one_iff_deriv`), `κ ≠ 0` vs `κ > 0`
splits, and the continuity hypotheses FTC needs. No new hypotheses are introduced by
this delta.

## Verification transcript

- Local gate (AC build face, toolchain v4.32.0 / mathlib 81a5d257):
  `cd AmericanPutConvexity && lake env lean ../builds/lean/port-test-hw-delta.lean`
  → exit 0; `#print axioms` on all **27** public theorems (24 committed + 3 delta) →
  `[propext, Classical.choice, Quot.sound]` only; zero `sorry`. The port-test's
  module region is byte-aligned with this file except the six contracted delta hunks
  (checked by `diff`).
- Canonical gate: the CI trio in the verify container (this PR) — note the local
  face is v4.32.0 vs CI's v4.33.0-rc1; the trio retires that residual.

## Coverage / audit bookkeeping

No `docs/coverage.md` or `AxiomAuditGen.lean` changes accompany this delta: the
coverage tables are benchmark-id-keyed and contain no HullWhite rows today (so CI
requires none), and `AxiomAuditGen` is benchmark-keyed. All rows that exist for this
family would be faithfulness `full` (no `library_wrapper` content in PR-2).

## Provenance

Course: "Machine-Checked Math for Quants", lesson 0020 (Hull–White calibration and
exact repricing). Workspace: `builds/lean/hw_scratch.lean` (QUEUE.md item 16),
dep-map `builds/lean/memos/pr-2-memo.md`.

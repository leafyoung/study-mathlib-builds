# PR-3 — MonteCarloPricer: call-variant layer + multi-D seed (24 theorems)

**Branch**: `ito-drift-expectation` (fork: leafyoung/formal-mathfin) — apply
`pr3-montecarlo-delta.patch`.

## Statement

Extends `MathFin/Foundations/MonteCarloPricer.lean` (the committed put-only module)
with the final landing of the workspace MC-pricer build (provenance: course lesson
0023; `builds/lean/mc_pricer.lean`, QUEUE.md item 12):

- **Terminal-moment cross-checks**: `mc_terminal_secondMoment`, `mc_terminal_variance`
  (cross-checked against `MathFin.BlackScholes.LognormalMoments`' closed forms).
- **Call-variant layer**: `mcCallPayoff` through `mc_call_variance` — the exact
  analogues of the put half (integrability, L² membership, mean = Black–Scholes call
  via `mean_mcCallPayoff_eq_bsCall`, pairwise/iid consistency, library-CLT and
  identified-variance CLT).
- **Multi-D seed**: `multiGauss` (+ named `IsProbabilityMeasure` instance and joint
  `HasLaw`), `multiD_consistency`, `multiD_consistency_iid`,
  `multiD_integrable_of_bounded` — the d-dimensional starting point for path-dependent
  payoffs.

Helper declarations that mirror the put half's private layer land `private`, per the
existing module convention; two memo-flagged helpers land public (`integrable_exp_of_hasLaw`,
`integrable_sq_terminal`) as reusable law-level facts.

## Honest hypothesis list

Unchanged from the put half: the i.i.d. ensemble is **hypothesized** — the pin's
`MathFin.Probability.ProductMeasure` is a broken phantom and Mathlib's
product-measure construction is the recorded future substrate. Call half additionally
consumes the BS-call closed form (`bs_call_formula`) and terminal law facts via the
existing `Put`→`Call` import chain.

## Substrate change (disclosed)

One import insertion: `import MathFin.BlackScholes.LognormalMoments` (the
terminal-moment cross-checks consume its closed forms; the baseline did not import
it transitively). One baseline docstring line updated in the module result list.
Two scratch-side private names mapped to the baseline's existing `terminal_nonneg`
(the scratch's `bsTerminal_nonneg` has no baseline counterpart under that name).

## Verification transcript

- Local gate (AC build face, toolchain v4.32.0 / mathlib 81a5d257):
  `cd AmericanPutConvexity && lake env lean ../builds/lean/port-test-mc-delta.lean`
  → exit 0; `#print axioms` on all **36** public theorems (12 baseline + 24 delta) →
  `[propext, Classical.choice, Quot.sound]` only; zero `sorry`. Baseline region
  byte-identical except the contracted hunks (`diff`-checked).
- Canonical gate: the CI trio in the verify container (this PR); local face is
  v4.32.0 vs CI's v4.33.0-rc1 — the trio retires the residual.

## Coverage / audit bookkeeping

No `docs/coverage.md` rows: the tables are benchmark-id-keyed and hold no
MonteCarloPricer rows today. `AxiomAuditGen.lean` regeneration rides CI.

## Provenance

Course lesson 0023 (MC pricer theorem, Etemadi-strengthened pairwise-SLLN
consistency + CLT). Workspace: `builds/lean/mc_pricer.lean` (QUEUE.md item 12),
dep-map `builds/lean/memos/pr-3-memo.md`.

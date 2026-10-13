# PR-4 — Cox-intensity credit module (new FixedIncome/Cox.lean, 22 public theorems + 7 defs)

**Branch**: `ito-drift-expectation` (fork: leafyoung/formal-mathfin) — apply
`pr4-cox-module.lean` as `mathfin/MathFin/FixedIncome/Cox.lean` +
`pr4-rootimport.patch` (one root-import line after `CDSTimeVarying`).

## Statement

New module promoting the workspace Cox-intensity credit build (provenance: course
lesson 0032; `builds/lean/cox_scratch.lean`, QUEUE.md item 15) into
`namespace MathFin.Cox`:

- **Layer 1–2 (constant λ)**: `riskyAnnuity_eq`/`_pos`, `protectionLeg_const`,
  `cdsLegs_balance_const` (the pin's abstract `cds_leg_equality` realized at the
  concrete integrals), `cdsFairSpread_const_balances`.
- **Layer 3 (deterministic λ(t))**: `cumHazard` machinery (deriv/zero/nonneg/
  continuous/strictMono), `coxDefaultTime` (constructed default time for a
  unit-exponential clock), the time-varying legs and `cdsFairSpread_TV`.
- **Layer 4 (stochastic headline + restricted mixing)**: the stochastic CDS spread
  identity and the restricted-Cox mixing stretch.
- **Faithfulness disclosure** (in the theorem's own docstring, kept verbatim):
  `cdsFairSpread_TV_balances` is `library_wrapper`-shaped — a direct instantiation of
  the in-tree `cdsFairSpread_TV_cash_flow_balance` at the concrete integrals, with
  annuity-positivity discharged via `cdsAnnuity_pos`. All other theorems are `full`.

## Honest hypothesis list

Constant-λ results consume the pin's Poisson machinery
(`PoissonInterarrival.survival_eq`, `.map_firstArrival_eq_expMeasure`); the
deterministic-λ bridge uses the novel a.e. set-equality mechanism; the stochastic
headline is restricted to the constructed-process scoping recorded in the course
(enlargement out of scope).

## Verification transcript

- Local gate (AC build face, toolchain v4.32.0 / mathlib 81a5d257):
  `cd AmericanPutConvexity && lake env lean ../builds/lean/port-test-cox.lean`
  → exit 0; `#print axioms` on all **29** public declarations (22 theorems + 7
  noncomputable defs) → `[propext, Classical.choice, Quot.sound]` only; zero `sorry`.
  Early probe compile of imports + `@`-references confirmed every consumed MathFin
  name resolves (`survival_eq`, `map_firstArrival_eq_expMeasure`, `cdsFairSpread`,
  `cds_leg_equality`, `cdsFairSpread_TV_cash_flow_balance`, `cumHazard`,
  `hazardSurvival*`).
- Canonical gate: the CI trio in the verify container (this PR); local face is
  v4.32.0 vs CI's v4.33.0-rc1 — the trio retires the residual.

## Bookkeeping

- Module content is course-neutral (no lesson references); helpers private (13
  total); section banners mirror the house idiom.
- Coverage tables are benchmark-id-keyed and hold no Cox rows; if rows are wanted,
  the `cdsFairSpread_TV_balances` row takes `library_wrapper` + an
  `UPSTREAM_CITATIONS` entry naming `cdsFairSpread_TV_cash_flow_balance`
  (`FixedIncome/CDSTimeVarying.lean`); all other rows are `full`.

## Provenance

Course lesson 0032. Workspace: `builds/lean/cox_scratch.lean` (QUEUE.md item 15),
dep-map `builds/lean/memos/pr-4-memo.md` (one correction applied by the builder: the
nested-namespace precedent lives at `MathFin/Actuarial/SurvivalModel.lean`, not
`FixedIncome/Actuarial/`).

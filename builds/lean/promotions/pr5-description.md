# PR-5 — CMS convexity-adjustment module (new FixedIncome/CMS.lean, 15 public declarations)

**Branch**: `ito-drift-expectation` (fork: leafyoung/formal-mathfin) — apply
`pr5-cms-module-porttest.lean` as `mathfin/MathFin/FixedIncome/CMS.lean` (lines
1–499, i.e. minus the port-test audit appendix) + one root-import line
`import MathFin.FixedIncome.CMS` after `InterestRateSwap` in `MathFin.lean`.

## Statement

New module promoting the workspace CMS build (provenance: course lesson 0031;
`builds/lean/cms_scratch.lean`, QUEUE.md item 14) into `namespace MathFin.CMS`:

- **Par-rate functional**: `cmsCurveRate` + `payerSwapValue_update_eq_zero_iff`,
  with the second-derivative calculus (`hasDerivAt_cmsCurveRate`, `_prime`) and
  `cmsCurveRate_convexOn`.
- **Annuity measure**: `annuityMeasure` (+ probability-measure proof) and
  `annuityMeasure_price` — the numeraire engine's third execution.
- **Headlines**: `cms_adjustment_nonneg` (via `ConvexOn.map_integral_le`),
  `cms_adjustment_delta_nonneg`, plus spanning/strip/nonneg lemma support
  (`cmsCurveRate_spanning`, `cmsCurveRate_strip_nonneg`, `convexityNumerator_nonneg`)
  and the Carr–Madan replication seed.

All 15 public declarations are faithfulness `full`; no `library_wrapper` content.

## Honest hypothesis list

Convexity of the CMS rate curve is proved via the scratch's hand-derived
`convexOn_inv_shift` (private); the two heavy computations
(`cms_adjustment_nonneg`, `cmsCurveRate_spanning`) carry scoped
`set_option maxHeartbeats 1000000` with why-comments (house idiom per
`PoissonCompensatedIntegralOperator.lean`). One to-additive-generated Mathlib name
(`Finset.sum_erase_add`) is consumed and compiles on the local face.

## Verification transcript

- Local gate (AC build face, toolchain v4.32.0 / mathlib 81a5d257; AC's MathFin
  package re-confirmed at 784a831 with all four consumed-module oleans present):
  `cd AmericanPutConvexity && lake env lean ../builds/lean/port-test-cms.lean`
  → exit 0 first compile, zero warnings; `#print axioms` on all **15** public
  declarations → `[propext, Classical.choice, Quot.sound]` only; zero sorry/admit.
- Canonical gate: the CI trio in the verify container (this PR); local face is
  v4.32.0 vs CI's v4.33.0-rc1 — the trio retires the residual.

## Bookkeeping

Course-neutral docstrings (grep for lesson/tier/desk markers: 0 hits); helpers
private (7); header/result-list idiom mirrors the landed HullWhite/MonteCarlo/Cox
promotions. Coverage tables are benchmark-id-keyed with no CMS rows; no rows added.

## Provenance

Course lesson 0031. Workspace: `builds/lean/cms_scratch.lean` (QUEUE.md item 14),
dep-map `builds/lean/memos/pr-5-memo.md`.

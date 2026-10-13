# PR-4 memo — promoting `cox_scratch.lean` to a standalone MathFin Cox module

*E-pass (flash-explorer, read-only), 2026-10-13. Source: `builds/lean/cox_scratch.lean`
(709 lines, `wc -l`). Upstream requirements: `mathfin/CONTRIBUTING.md` +
`.github/PULL_REQUEST_TEMPLATE.md`. Style model: `mathfin/MathFin/FixedIncome/CDSTimeVarying.lean`
(read in full) with `Credit.lean` / `HazardCurve.lean` headers and the PR-1 modules
(`ItoDriftExpectation.lean`, `ItoIntegralCrossHorizon.lean`) as secondary precedent.*

## 0. Faces used (AGENTS.md §Name-verification convention)

- **Face A — compile/build face**: `AmericanPutConvexity/.lake/packages/` — mathlib
  `81a5d257` (toolchain v4.32.0) + MathFin `784a831`. The scratch file is verified to
  compile here (`PUBLISHING.md:38-39`: zero sorry, standard-three at pin 784a831).
- **Face B — CI face**: `mathfin/.lake/packages/` — mathlib `0434c03`
  (`mathfin/lake-manifest.json`, `inputRev` field) + toolchain `v4.33.0-rc1`
  (`mathfin/lean-toolchain`) + MathFin upstream HEAD (3559d7a per `PUBLISHING.md:57`,
  plus uncommitted PR-1 modules).
- Face C (workspace `mathlib4/` clone) — not used in this memo.

Every headline consumed name was grep-verified on **both** Face A and Face B (§1);
the five import modules were compared across the two MathFin faces by read-only
`cmp`/`diff` (§1.3).

## 1. External dependencies (every non-file name the module consumes)

### 1.1 MathFin names — verified on Face A (AC-packaged MathFin 784a831); Face-B status in §1.3

| Consumed name | Face A location (file:line) | Face B (upstream tree) |
|---|---|---|
| `PoissonInterarrival.survival_eq` | `MathFin/Foundations/PoissonInterarrival.lean:50` | statement identical (diff §1.3) |
| `PoissonInterarrival.survival_factorizes` | same file `:71` | **header-mention only — not used in code** |
| `PoissonInterarrival.map_firstArrival_eq_expMeasure` | same file `:99` | statement identical |
| `PoissonCounting.map_count_eq_poissonMeasure` | `MathFin/Foundations/PoissonCounting.lean:191` | **header-mention only — not used in code** (import itself unused, §4 item 5) |
| `Credit.survivalProbability` | `MathFin/FixedIncome/Credit.lean:45` | **header-mention only** (reached transitively via `hazardSurvival_eq_const_survival`) |
| `Credit.creditSpread_eq_hazard` | same file `:58` | header-mention only |
| `Credit.cdsFairSpread` | same file `:86` | used (`cox_scratch.lean:232,239,594,599`) |
| `Credit.cds_leg_equality` | same file `:94` | used (`cox_scratch.lean:233`) |
| `HazardCurve.cumHazard` | `MathFin/FixedIncome/HazardCurve.lean:45` | used throughout |
| `HazardCurve.hazardSurvival` | same file `:51` | used throughout |
| `HazardCurve.hazardSurvival_at_zero` | same file `:55` | used (`cox_scratch.lean:498`) |
| `HazardCurve.hazardSurvival_pos` | same file `:62` | used (`cox_scratch.lean:450,616`) |
| `HazardCurve.hazardSurvival_eq_const_survival` | same file `:91` | used (`cox_scratch.lean:561,578`) |
| `CDSTimeVarying.cdsFairSpread_TV_cash_flow_balance` | `MathFin/FixedIncome/CDSTimeVarying.lean:69` | used (`cox_scratch.lean:551`) — the library_wrapper basis |

The scratch resolves these bare (`open MathFin` at `cox_scratch.lean:122`) via the
import chain `CDSTimeVarying → HazardCurve → {Credit, ExponentialDiscount}`; the
header's claim of a "`FixedIncome.CDS` re-export" (`cox_scratch.lean:108-109`) is
inaccurate — `MathFin.FixedIncome.CDS` is **not** imported; the names come through
the `CDSTimeVarying` chain.

### 1.2 Mathlib names — verified on Face A (81a5d257) and re-grepped on Face B (0434c03)

| Consumed name | Face A | Face B |
|---|---|---|
| `expMeasure` | `Mathlib/Probability/Distributions/Exponential.lean:96` | same file:line ✓ |
| `isProbabilityMeasure_expMeasure` | same file `:98` | same file:line ✓ |
| `cdf_expMeasure_eq` | same file `:165` | present (doc ref `:25`) ✓ |
| `poissonMeasure` (type in hincr hyps) | `Mathlib/Probability/Distributions/Poisson/Basic.lean:41` | present ✓ |
| `poissonMeasure_singleton` | same file `:50` | same file:line ✓ (**header-mention only — not used in code**) |
| `Measure.prod_apply` | `Mathlib/MeasureTheory/Measure/Prod.lean:223` | present ✓ |
| `intervalIntegral.integral_same` | `IntervalIntegral/Basic.lean:680` | `:681` ✓ |
| `intervalIntegral.integral_nonneg` | same file `:1385` | present ✓ |
| `intervalIntegral.integral_pos` | same file `:1392` (`lemma`) | present ✓ |
| `intervalIntegral.integral_const_mul` | same file `:816` | present ✓ |
| `intervalIntegral.integral_congr` | same file `:1076` | present ✓ |
| `intervalIntegral.integral_add_adjacent_intervals` | same file `:1094` | **header-mention only — not used in code** |
| `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `FundThmCalculus.lean:1148` | same file:line ✓ |
| `intervalIntegral.integral_hasDerivAt_right` | `FundThmCalculus.lean:725` | present ✓ |
| `measure_congr` | `Mathlib/MeasureTheory/OuterMeasure/AE.lean:270` | `:276` ✓ |
| `Function.invFun_eq` | `Mathlib/Logic/Function/Basic.lean:527` | present ✓ |
| `strictMono_of_hasDerivAt_pos` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:403` | same file:line ✓ |
| `HasDerivAt.differentiableAt` | `Mathlib/Analysis/Calculus/Deriv/Basic.lean:392` | present ✓ |
| `intermediate_value_Icc` | `Mathlib/Topology/Order/IntermediateValue.lean:553` | present (used unqualified in `Analysis/Polynomial/Order.lean:60`) ✓ |
| `lintegral_congr` / `lintegral_mono` / `lintegral_one` / `Measure.map_apply` / `cdf_eq_real` / `measureReal_def` / `ae_iff` / `Filter.Tendsto.eventually_ge_atTop` / `Measure.prod` API (`measurable_fst`/`prodMk`/`measurableSet_lt`) / `Continuous.intervalIntegrable` / `hasDerivAt_id` / `ENNReal.ofReal_*` / `Real.exp_*` | **verified in aggregate** — the file compiles at Face A (PUBLISHING.md:38-39), which requires every one of these to resolve; individually spot-checked where load-bearing above | same-mathlib-era API; residual risk flagged (§7 flag 1) |

No BrownianMotion name is consumed: `Credit.lean`, `ExponentialDiscount.lean` and
`PoissonInterarrival.lean` each `public import Mathlib` only (verified headers), so
the module's whole MathFin import closure is Mathlib + in-tree FixedIncome/Foundations.

### 1.3 Import modules across the two MathFin faces (read-only `cmp`/`diff`, this session)

- `FixedIncome/Credit`, `FixedIncome/HazardCurve`, `FixedIncome/CDSTimeVarying`,
  `Foundations/PoissonCounting`: **byte-identical** between
  `mathfin/MathFin/` and `AmericanPutConvexity/.lake/packages/MathFin/MathFin/`.
- `Foundations/PoissonInterarrival`: differs in exactly one proof-internal tactic
  line (`:87`, `Set.mem_ofPred_eq` vs `Set.mem_setOf_eq` — a simp-lemma rename);
  all consumed statements (`:50/:71/:99`) identical.
- `Foundations/ExponentialDiscount`: the **pin-side copy has an extra lemma**
  (`discount_strictAnti`) absent upstream — additive only; no consumed name
  (`cumulativeIntensity`/`survivalFromIntensity` definitions) changed.

## 2. Private helpers that must ship (upstream style: helpers `private`)

Already `private` in the scratch (keep private): `expClock_Iic` (:305), `expClock_Ioi`
(:316), `invFun_on_halfline` (:356), `coxDefaultTime_survSet` (:374),
`coxDefaultTime_cdfSet` (:397), `hazardSurvival_continuous` (:462).

Recommended additional privatization (pure infrastructure, no standalone finance
content; shrinks the public API 29 → 22 and the coverage rows accordingly):
`hazardSurvival_eq_exp` (:255, `rfl` one-liner), `cumHazard_zero` (:259),
`cumHazard_nonneg` (:264), `cumHazard_deriv` (:269), `cumHazard_continuous` (:275),
`expClock_null_neg` (:332), `expClock_nonneg_ae` (:344).

Keep public (finance-meaningful or load-bearing for the headline statements):
`cdsAnnuity_pos` (discharges positivity in the wrapper theorem),
`defaultDensity_antideriv` + `clockTail_eq_defaultDensity` (density-pricing
calculus), `cdsAnnuity_eq_riskyAnnuity` + `cdsLosses_eq_riskyAnnuity_mul` (the
constant-λ regression bridge), and all headline theorems.

Duplication note: `Cox.cumHazard_deriv` re-derives `HasDerivAt (cumHazard h) (h t) t`
by FTC exactly as the proof of upstream `HazardCurve.hazard_eq_neg_log_deriv_survival`
(`HazardCurve.lean:71-81`) does internally. No name conflict; keep it private in
PR-4 and mention the possible future extraction in the PR body.

## 3. Name conflicts against the existing mathfin tree — NONE

Checks run (read-only greps over `mathfin/MathFin/`, this session):

- `Foundations/Cox.lean` / `FixedIncome/Cox.lean`: do not exist (`ls` → both absent).
- Namespace `Cox`: no hits anywhere (only Cox–Ross–Rubinstein prose in
  `Binomial/CRR*.lean` and a Cox-process mention in `Credit.lean:25` — the module
  is precisely the unblock of `Credit.lean`'s "gated ... not formalized here" note).
- All 13 distinctive public names grepped (`riskyAnnuity`, `cdsAnnuity`, `cdsLosses`,
  `premiumLeg`, `protectionLeg`, `cdsFairSpread_TV`, `coxDefaultTime`, `cox_*`,
  `defaultSurvival_const`, `defaultTimeLaw_const`, `expClock_*`,
  `defaultDensity_antideriv`, `clockTail_eq_defaultDensity`) plus
  `cumHazard_deriv/_zero/_nonneg/_continuous/_strictMono` and
  `hazardSurvival_eq_exp`: **zero hits** in `mathfin/MathFin/`.
- The only near-collision candidate, upstream's `cdsFairSpread_TV_cash_flow_balance`,
  is a distinct name from the module's `cdsFairSpread_TV_balances` / `cdsFairSpread_TV`.

Proposed home per `PUBLISHING.md:20,71-72`: **`MathFin/FixedIncome/Cox.lean`**.
Root import: one line `import MathFin.FixedIncome.Cox` in `MathFin.lean`'s
`-- FixedIncome` section (`MathFin.lean:377-486`; natural slot after the
`CDSTimeVarying` line at `:402`) — the PR-1 precedent added root-import lines the
same way. Namespace: `namespace MathFin.Cox` preserves every internal name
unchanged, with upstream precedent (`Actuarial/SurvivalModel.lean:51`,
`BlackScholes/AmericanPut/Boundary/*`); the flat alternative
(`namespace MathFin` + prefixed names, as `CDSTimeVarying.lean:55`) is also viable
since no bare name conflicts — S-pass decides (recommend `MathFin.Cox`).

## 4. House-style deltas — scratch vs `CONTRIBUTING.md` + style model (concrete)

1. **Header block**: replace `import Mathlib` + plain imports with the upstream
   shape — copyright/license/authors comment, `module`, `public import Mathlib`,
   `public import MathFin.*` (style model `CDSTimeVarying.lean:1-9`; PR-1 modules
   show workspace-promoted files keep the tree's `Authors: Raphael Coelho` header).
2. **`@[expose] public section`** after the module docstring — explicit PR-template
   checklist item; absent from the scratch.
3. **Namespace** `Cox` → `MathFin.Cox` (§3).
4. **Module docstring**: compress the 115-line scratch docstring to the style
   model's shape (`# title`, short prose, `Results:` bullet list of public names).
   Move the "Scope fences" content into the PR description (PUBLISHING.md checklist
   item 6: "the honest hypothesis list"). Delete or correct the "Stack consumed"
   list — it names six symbols not used in code (`survival_factorizes`,
   `map_count_eq_poissonMeasure`, `Credit.survivalProbability`,
   `Credit.creditSpread_eq_hazard`, `ExponentialDiscount.*`,
   `poissonMeasure_singleton`, `integral_add_adjacent_intervals`) and a wrong CDS
   re-export claim (§1.1).
5. **Drop `import MathFin.Foundations.PoissonCounting`** — unused by the code
   (grep: no occurrence outside the docstring prose and the import line).
6. **Strip the trailing `#print axioms` block** (`cox_scratch.lean:690-709`, 20
   entries): style models end at `end MathFin`; axiom cleanliness is enforced by
   CI via `python3 -m tools.verify.axiom_audit_gen --write` (PR template).
7. **Privatize** the 7 infrastructure lemmas (§2) per CONTRIBUTING.md:101-102
   ("Helper lemmas can live in the same file as `private`").
8. **Def docstrings**: all 7 `noncomputable def`s already carry docstrings — keep
   (`lake lint` fails a build on any missing `def` docstring, PR template).
9. **Section banners** `/-! ## Layer N -/`: no upstream precedent in the style
   models; fold the layering into the Results docstring or drop.
10. **Tactic style**: already conforms — `field_simp; ring` close-outs
    (`cox_scratch.lean:195-196, 599-600`), no forbidden tactics; no `bs_identity`
    needed (not BS-family).
11. **`open` line**: keep only what the code uses (`MeasureTheory ProbabilityTheory
    Real MathFin` + `open scoped NNReal ENNReal`); style models open fewer
    (`CDSTimeVarying.lean:57`).
12. **Imports at the promoted home must exist upstream**: all five do (§1.3), and
    PUBLISHING.md's queue note (`QUEUE.md:19-24`) — "agents import only
    pin-verified modules" — is satisfied.

## 5. Local compile-verification feasibility (BEFORE opening the PR)

Facts established this session (read-only):

- `mathfin/.lake/build` **does not exist** (`ls`/`du` → absent): there are **no
  MathFin oleans** in the upstream clone. Any `lake env lean` on a file importing
  `MathFin.*` fails until the import chain is built.
- `mathfin/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean` **exists**:
  the CI-face mathlib (0434c03) oleans are built. `BrownianMotion`'s build dir is
  empty — irrelevant here, since the Cox import closure needs no BrownianMotion (§1.2).
- Toolchain `v4.33.0-rc1` **is installed** (`ls ~/.elan/toolchains`).
- Therefore `cd mathfin && lake env lean MathFin/FixedIncome/Cox.lean` would require
  first building the chain `Credit` + `ExponentialDiscount` → `HazardCurve` →
  `CDSTimeVarying` (≈ `lake build MathFin.FixedIncome.CDSTimeVarying`) — a **mathfin
  lake build**, which this E-pass is barred from running (task constraint), and
  which for any agent is gated by `mathfin/AGENTS.md`'s host-safety doctrine (one
  Lean-loaded process; never local `docker compose build`).

Concrete pre-PR verification plan (PR-1 precedent, `PUBLISHING.md:24-26,33-35`):

1. **Port-test at Face A**: materialize the promoted module as
   `builds/lean/cox-port-test.lean` and run
   `cd AmericanPutConvexity && lake env lean ../builds/lean/cox-port-test.lean`.
   With the cross-face evidence of §1.3 (four import modules byte-identical, two
   with benign diffs) and the dual-face greps of §1.2, this is strong content
   verification — but at v4.32.0/81a5d257/784a831, **not** the CI face.
   Optionally the port-test can carry the upstream header shape (`module`,
   `public import`, `@[expose]`) since the pin's toolchain demonstrably supports
   that syntax (the AC-packaged MathFin modules themselves use it) — if it chokes
   outside a Lake target, fall back to the plain-import port-test and let CI check
   the header.
2. **Everything else rides the docker CI trio** (`docker compose pull verify` +
   `lake build` + `pytest tests/ -q` + `python3 -m tools.verify.ledger status` +
   `lake lint`): the linter, the three test suites, ledger freshness, and
   `AxiomAuditGen` regeneration are CI-side only. Never build images locally
   (`mathfin/AGENTS.md` doctrine).

## 6. coverage.md rows

`docs/coverage.md` is a dated narrative audit (sections like "### Girsanov: ...
(2026-09-25)"), not a mechanical table; CONTRIBUTING.md step 5 asks for "a row ...
describing the theorem, the file path, and its faithfulness status". Proposal:
one new dated section "Cox-intensity credit (PR-4)" listing the public theorems
with file path + status:

- **29 public theorems/lemmas** (§2 census: 20 headline theorems matching the
  scratch's `#print axioms` block at `cox_scratch.lean:690-709` — the count
  PUBLISHING.md:71 quotes — plus 9 auxiliary public lemmas), **28 × `full`**,
- **1 × `library_wrapper`**: `cdsFairSpread_TV_balances`
  (`cox_scratch.lean:547-551`) — direct instantiation of the in-tree
  `cdsFairSpread_TV_cash_flow_balance` (`CDSTimeVarying.lean:69-72`) with
  annuity-positivity discharged via `cdsAnnuity_pos`; the disclosed exception per
  `PUBLISHING.md:86-93`, requiring an **`UPSTREAM_CITATIONS` entry** in
  `tools/verify/axiom_audit_gen.py` naming `MathFin.cdsFairSpread_TV_cash_flow_balance`
  fully-qualified. The invariant is bidirectional
  (`tests/test_values.py:533-546` `test_library_wrapper_citations_are_pinned`:
  every wrapper entry must have a citation row AND a citation row implies a
  wrapper entry), and it is keyed by **benchmark entry id** — so the citation
  obligation actually triggers only if a benchmark entry for the wrapper is added
  (§7 flag 2).
- If the §2 privatization is taken: **22 rows** (21 `full` + 1 `library_wrapper`).
- The 7 `noncomputable def`s are not theorems: they go in the module docstring's
  Results list, not coverage rows.

## 7. Flags for the S-pass

1. **Residual face risk**: the module has only ever been *compiled* at Face A;
   Face B (0434c03 / v4.33.0-rc1 / upstream HEAD) is verified by source greps and
   `cmp`/`diff` only. The observed faces are near-identical for every consumed
   name, but the aggregate-verified routine Mathlib API (§1.2 last row) carries
   the residual churn risk. First B-pass checkpoint: re-elaborate the promoted
   file (port-test or in-tree) and confirm zero errors before touching statements.
2. **Wrapper mechanics**: decide whether PR-4 adds a benchmark re-export entry for
   `cdsFairSpread_TV_balances` (PR template requires "Benchmark re-export shim
   added (or updated)"; precedent `cds_leg_equality_thm` at
   `benchmarks/mathematical_finance.json:3034`). If yes → `UPSTREAM_CITATIONS`
   row keyed by that entry id, naming `MathFin.cdsFairSpread_TV_cash_flow_balance`,
   and `formalization_status: library_wrapper` with a `description` that states
   the narrowing. If no benchmark entry, the coverage row still says
   `library_wrapper` but check with maintainers whether a citation row is expected
   anyway (PUBLISHING.md:86-93 says yes).
3. **Privatization decision** (§2): 29→22 public API. All 7 candidates are used
   only inside the module (verified by reading), so privatization is safe.
4. **Namespace choice**: `MathFin.Cox` (recommended; `SurvivalModel.lean:51`
   precedent, zero renames) vs flat `MathFin` with prefixing (style-model shape).
5. **`cdsFairSpread_TV_cash_flow_balance` arity check at the CI face**: the
   wrapper call passes `(c, R, annuity, losses, h_annuity_ne)` positionally
   (`cox_scratch.lean:551`); `CDSTimeVarying.lean` is byte-identical across faces,
   so this is safe — but the B-pass should still confirm the `unfold`+
   instantiation compiles verbatim after the namespace change.
6. **Root-import slot** in `MathFin.lean` (after `:402` `CDSTimeVarying`) and PR
   branch base: `mathfin` HEAD 3559d7a + the uncommitted PR-1 modules — do not
   disturb the PR-1 working-tree content (task constraint; it must land as PR-1
   first).
7. **Unused-import hygiene**: drop `PoissonCounting`; re-check after the namespace
   change that `open` lines stay minimal.
8. **`rfl`-backed lemma**: `hazardSurvival_eq_exp` is proved by `rfl` — fine as a
   private helper, but never attach a benchmark `full` entry to it
   (test_values forbids `rfl`-backed `full`).

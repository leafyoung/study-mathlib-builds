# PR-5 E-pass memo — promoting `builds/lean/cms_scratch.lean` → MathFin `FixedIncome/CMS`

E-pass (Explorer·PR-5), 2026-10-13. Read-only. Sources read: the scratch file, `mathfin/CONTRIBUTING.md`, `builds/lean/PUBLISHING.md`, `builds/lean/QUEUE.md:43`, mathfin `AGENTS.md`/`CLAUDE.md`, `docs/coverage.md`, `tests/test_router.py`, `tests/test_values.py`, `.github/PULL_REQUEST_TEMPLATE.md`, `tools/verify/axiom_audit_gen.py`, the two landed promotion modules (`HullWhiteCalibration.lean`, `MonteCarloPricer.lean`), and the build faces. Every name below was verified in this session by grep/run as cited.

## 0. Headline state (one correction to the dispatch brief)

- mathfin HEAD is **`b46e9b4`** ("feat: add Hull–White calibration and Monte Carlo pricer modules", 2026-10-12) — **PR-2 and PR-3 content has landed**; the dispatch brief's premise "the working tree has uncommitted PR-1 content" is **stale**: `git status --short` in `mathfin/` shows only untracked `v.val`. Working tree effectively clean. PR-5 branches from current HEAD.
- The two landed modules are the **freshest style model** for a scratch→module promotion; `InterestRateSwap.lean` remains the domain (rates) model.
- Proposed home (per PUBLISHING.md:19,73): **`mathfin/MathFin/FixedIncome/CMS.lean`**, namespace **`MathFin.CMS`**, root import line in `MathFin.lean` (FixedIncome block ends at `MathFin.lean:485-486`; the b46e9b4 diff shows the exact pattern: a plain `import MathFin.…` line with a one-line comment above it).

## 1. External dependencies (every imported name from outside the file)

### 1a. MathFin names — verified on the BUILD FACE (`AmericanPutConvexity/.lake/packages/MathFin`, pin 784a831 confirmed live via `git log` in that dir)

Consumed by `cms_scratch.lean` (file header's own substrate list, lines 65–75, re-verified by grep):

| Name | Kind | Build-face site | Also in mathfin tree |
|---|---|---|---|
| `annuity` | def | `FixedIncome/InterestRateSwap.lean:35` | byte-identical (`diff -q` IDENTICAL) |
| `payerSwapValue` | def | `InterestRateSwap.lean:39` | byte-identical |
| `parSwapRate` | noncomputable def | `InterestRateSwap.lean:43` | byte-identical |
| `annuity_pos` | theorem | `InterestRateSwap.lean:47` | byte-identical |
| `payerSwapValue_eq_zero_iff` | theorem | `InterestRateSwap.lean:53` | byte-identical |
| `numeraireMeasure` | noncomputable def | `Foundations/Numeraire.lean:86` | byte-identical |
| `numeraireMeasure_isProbabilityMeasure` | theorem | `Numeraire.lean:97` | byte-identical |
| `changeOfNumeraire` | theorem | `Numeraire.lean:124` | byte-identical |
| `carrMadan_spanning` | theorem | `Foundations/CarrMadan.lean:76` | byte-identical |
| `convexityNumerator` | noncomputable def | `FixedIncome/ConvexitySensitivity.lean:57` | byte-identical |

**Zero pin↔HEAD drift on the consumed surface**: `diff -q` of all four consumed module files between the AC-face package (784a831) and the mathfin working tree (b46e9b4) → all four IDENTICAL. (Ran in this session; output quoted in the transcript.)

**Import pruning**: scratch line 5 `import MathFin.FixedIncome.ForwardMeasure` is **unconsumed** — grep of the scratch shows `forwardMeasure` only in comments (lines 33, 70–71, 291; the file itself says "pattern reference … not consumed directly"). Drop this import in the promoted module. Promoted imports: `public import Mathlib` + `public import` of InterestRateSwap, CarrMadan, Numeraire, ConvexitySensitivity.

### 1b. Mathlib names — verified on the build face (`AmericanPutConvexity/.lake/packages/mathlib`, 81a5d257, toolchain v4.32.0)

Spot-verified this session with file:line (the riskiest/churn-prone names):

- `ConvexOn.map_integral_le` — `Mathlib/Analysis/Convex/Integral.lean:199`
- `ConvexOn.smul` — `Mathlib/Analysis/Convex/Function.lean:909`; `ConvexOn.add_const` — `:216`; `ConvexOn.congr` — `:99`
- `convex_Ici` — `Mathlib/Analysis/Convex/Basic.lean:251`
- `hasDerivAt_inv` — `Mathlib/Analysis/Calculus/Deriv/Inv.lean:55`; `HasDerivAt.fun_div` — `Inv.lean:168`; `HasDerivAt.const_sub` — `Mathlib/Analysis/Calculus/Deriv/Add.lean:434`
- `div_le_iff₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1138`
- `Function.update_of_ne` — `Mathlib/Logic/Function/Basic.lean:646`
- `intervalIntegral.integral_nonneg` — `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1385`; `intervalIntegral.integral_congr_ae` — same file `:1241`; `ae_of_all` — `Mathlib/MeasureTheory/OuterMeasure/AE.lean:92`
- `isClosed_Ici` — `Mathlib/Topology/Order/OrderClosed.lean:82`
- `two_pos` — `alias two_pos := zero_lt_two`, `Mathlib/Algebra/Order/Monoid/NatCast.lean:101`
- `Finset.sum_erase_add` — **constant present on the face** (`strings` hit in `Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean`; 15 in-tree use sites, e.g. `Mathlib/Algebra/Module/ZLattice/Basic.lean:419`) but its declaration is **not plain-greppable in the source** (to_additive-generated name — grep for the string finds uses only). See flags.

Long tail (`Function.update_self`, `Finset.sum_congr`, `Finset.ne_of_mem_erase`, `HasDerivAt.const_mul/.comp/.mul`, `hasDerivAt_id`, `Real.exp_neg/exp_pos`, `div_eq_mul_inv`, `Nat.cast_nonneg`, positivity lemmas, `Finset.sum_nonneg`, `le_max_right`, `sub_nonneg`, the `Continuous*`/`ContinuousOn` chain, `Integrable`/`Measurable`/`IsProbabilityMeasure`): not individually re-grepped this pass. Their build-face validity is carried by the standing verification that `cms_scratch.lean` compiles axiom-clean at exactly this face (PUBLISHING.md:38–39 "All files: zero sorry, `#print axioms` standard-three, verified at the pinned rev 784a831 via `lake env lean` in AmericanPutConvexity"; QUEUE.md:43 item 14 DONE). The promoted module introduces no name outside the scratch's own surface.

## 2. Private helpers that must ship (upstream style: helpers `private`)

Scratch currently declares **zero** `private` (everything is public inside `namespace Cms`). House precedent from the landings: HullWhiteCalibration ships headline theorems public and states "Supporting lemmas … are `private`" (12 `private` decls; MonteCarloPricer has 10). Candidate split (S-pass final call):

**Public** (the module's face): `cmsCurveRate` (the definition), `annuityRandom`, `annuityMeasure` (defs appearing in public signatures), and the **11 audited theorems** (the scratch's own `#print axioms` list, lines 487–497): `payerSwapValue_update_eq_zero_iff`, `hasDerivAt_cmsCurveRate`, `hasDerivAt_cmsCurveRate'`, `cmsCurveRate_convexOn`, `annuityMeasure_isProbabilityMeasure`, `annuityMeasure_price`, `cms_adjustment_nonneg`, `cms_adjustment_delta_nonneg`, `cmsCurveRate_spanning`, `cmsCurveRate_strip_nonneg`, `convexityNumerator_nonneg`. (Optionally `parSwapRate_update_eq` public as the standalone bridge — it has independent meaning.)

**`private` candidates** (each has consumers only inside the file):
- `cmsCurveRate_eq` (consumed by `cmsCurveRate_convexOn`)
- `annuity_update_eq` (consumed by `parSwapRate_update_eq`)
- `differentiableOn_cmsCurveRate`, `continuousOn_cmsCurveRate` (consumed by `cms_adjustment_nonneg`)
- `convexOn_inv_shift` (consumed by `cmsCurveRate_convexOn`)
- `annuityRandom_pos` (consumed in §3–§4 proofs)
- `cmsStrip_weight_pos` (consumed by **no proof** — docstring-only references; smallest footprint is `private`)

## 3. Name conflicts against the existing mathfin tree

**None.** Ran a conflict grep for all 20 public scratch names (`cmsCurveRate`, `cmsCurveRate_eq`, `annuity_update_eq`, `parSwapRate_update_eq`, `payerSwapValue_update_eq_zero_iff`, `hasDerivAt_cmsCurveRate`, `differentiableOn_cmsCurveRate`, `continuousOn_cmsCurveRate`, `convexOn_inv_shift`, `cmsCurveRate_convexOn`, `annuityRandom`, `annuityMeasure`, `annuityMeasure_isProbabilityMeasure`, `annuityMeasure_price`, `cms_adjustment_nonneg`, `cms_adjustment_delta_nonneg`, `cmsStrip_weight_pos`, `cmsCurveRate_spanning`, `cmsCurveRate_strip_nonneg`, `convexityNumerator_nonneg`) against `mathfin/MathFin/**/*.lean`: **zero hits**.

- Home path: `MathFin/FixedIncome/CMS.lean` does **not exist** (directory listing: 24 files, no CMS).
- Root import `import MathFin.FixedIncome.CMS`: absent from `MathFin.lean` (grep of FixedIncome lines 377–486).
- Namespace `MathFin.CMS`: unused. Convention note: all 22 older FixedIncome modules use flat `namespace MathFin`; **the two landed promotions use two-level `namespace MathFin.HullWhite` (HullWhiteCalibration.lean:80) and `namespace MathFin.MonteCarlo` (MonteCarloPricer.lean:76)** — `MathFin.CMS` follows the current convention.
- Caveat: HEAD may move again before the PR opens — re-run the (cheap) grep at branch time.

## 4. House-style deltas (scratch → CONTRIBUTING.md + landed-module practice), per item

1. **Header block** (CONTRIBUTING.md:106–107; InterestRateSwap.lean:1–6): add copyright (`Copyright (c) 2026 Raphael Coelho`, Apache 2.0, Authors), then the literal `module` line, then `public import Mathlib` + explicit `public import` of the four MathFin modules (scratch's plain `import`s → `public import`; b46e9b4-root-file imports stay plain `import`).
2. **`@[expose] public section`** after the module docstring — CI-enforced: `tests/test_router.py:103–116` (`test_mathfin_module_files_expose_public_section`, `MODULE_HEADER_RE` at :103) fails any `module`-header file without it.
3. **Namespace** `Cms` → `MathFin.CMS` (§3).
4. **Docstring**: compress the 70-line scratch header into a module docstring ending in a `## Result` section listing public defs and public lemmas (HullWhiteCalibration.lean:51–77 is the model). The honest-scope paragraph becomes a "Structural note:" paragraph (HullWhiteCalibration.lean:47–52 precedent). Storied docstrings ARE house style — keep them on defs/theorems (the lint *requires* a doc comment on every `def`: PR template, "`lake lint` … a missing `def` docstring … red").
5. **`-- pointers:`/`-- benchmark-id:` comment block** (InterestRateSwap.lean:11–16): **absent from both landed modules** — the current convention omits it (S-pass confirm; recommend omit).
6. **maxHeartbeats**: scratch sets it file-level (line 85). House precedent is **per-declaration** `set_option maxHeartbeats … in` (PoissonCompensatedIntegralOperator.lean:419 with its why-comment at :430; ItoFormulaAdaptedDrift.lean:436,1554,2561); neither landed module sets it file-level. Scope the raise to `cmsCurveRate_spanning` + `cms_adjustment_nonneg` (expand only if the build demands), keep the why-comment.
7. **Audit block stripped**: the trailing `#print axioms` block (scratch lines 485–497) does not ship — neither landed module has one; the axiom audit rides `python3 -m tools.verify.axiom_audit_gen --write` regenerating `MathFin/AxiomAuditGen.lean` (PR template checklist; generator docstring `tools/verify/axiom_audit_gen.py:1–10`: it pins every benchmark-cited MathFin constant).
8. **`private` helpers**: per §2.
9. **Comment discipline** (CONTRIBUTING.md:102–105 "default to no comments"): keep def/theorem docstrings and only the non-obvious why-comments (scratch's certificate comments at :241, :246–247 are keepers); drop tutorial narration from proof bodies.
10. **Tactic style**: already conforming — `field_simp; ring` close-outs (scratch :151, :198, :244); no `bs_identity` needed (not BS-family). `nlinarith`/`linear_combination` are fine: the forbidden-text gate (`tests/test_values.py:58–73`) bans only sorry/admit/native_decide/polyrith/`exact?`/`apply?`/`rw?`/`simp?`/hammer/`#loogle`/leansearch — none present in the scratch (and the file-level grep gate scans `MathFin/` sources only).
11. **`open` placement**: house puts `open` + `variable` lines after the namespace (HullWhiteCalibration.lean:82–87); scratch has a top-level `open MeasureTheory Real MathFin` (:87).
12. **`lake lint` sweep**: PR template demands `lake build && lake lint` clean (batteries runLinter per lakefile.lean:8–17; advisory CI via lint.yml). Watch unused-variable lints (e.g. `hL` in `cmsCurveRate_spanning` feeds `linarith` only via context — builder re-checks on the face).

## 5. Local compile-verification feasibility BEFORE the PR (read-only inspection; I ran no lake build, no docker)

Facts established this session:

- mathfin toolchain `leanprover/lean4:v4.33.0-rc1` (`mathfin/lean-toolchain:1`), **installed** (`~/.elan/toolchains/` lists `leanprover--lean4---v4.33.0-rc1`).
- mathfin's packaged **Mathlib oleans are present**: `mathfin/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean` exists (the expensive layer is cached).
- mathfin's **own oleans are absent**: `mathfin/.lake/` contains only `config` + `packages` — **no `build/` dir**. Therefore `cd mathfin && lake env lean MathFin/FixedIncome/InterestRateSwap.lean` (any MathFin module) **fails at import resolution** until its import closure is built. Verifying the promoted module in mathfin's env first requires a targeted `lake build MathFin.FixedIncome.CMS` (builds the transitive MathFin closure; Mathlib layer cached) — that is a **lake build**: out of my scope, and per host-safety doctrine it may only take the single Lean-loaded-process slot with the daemon down (mathfin/AGENTS.md doctrine 1–2: no local `docker compose build`, ever).
- Docker route: `docker compose pull verify` + run is pull-only and doctrine-legal; the CI trio (`pytest tests/ -q` → `python3 -m tools.verify.ledger status` → `lake build`, CONTRIBUTING.md:39–40) lives there. **I did not run docker** (constraint); the orchestrator owns that step.
- The **zero-new-build alternative — the landed precedent**: port-test at the AC face (`cd AmericanPutConvexity && lake env lean <port-test>.lean`). The AC face has **both layers materialized AND built**: AC mathlib oleans (81a5d257) and AC **MathFin oleans present** (verified: `AmericanPutConvexity/.lake/packages/MathFin/.lake/build/lib/lean/MathFin/FixedIncome/InterestRateSwap.olean` exists). The `module`/`public import` syntax **is supported there** (AC mathlib files carry `module` headers, e.g. `Mathlib/Analysis/Convex/Cone/Closure.lean`; toolchain v4.32.0). b46e9b4's own message records exactly this: "Port-tested at the pinned rev (784a831) via lake env lean."

**Concrete recommendation for the S-pass**: (a) port-test the *promoted* file (house header + `namespace MathFin.CMS` + `private` split) at the AC face — cheap, zero new builds, catches promotion-edit regressions; (b) treat the **CI trio in the pulled verify container** as the authoritative gate — the AC face runs mathlib 81a5d257/v4.32.0 while mathfin now pins v4.33.0-rc1 + a newer mathlib, so the AC port-test cannot catch face-churn of the documented kind (workspace AGENTS.md §Name-verification: `ContDiff.continuous` arity, `HasLaw` shape); (c) optionally, one targeted `lake build MathFin.FixedIncome.CMS` in the mathfin clone when a Lean-process slot is free.

## 6. coverage.md rows (CONTRIBUTING.md:70–77 step 5)

**Tension to resolve first**: the template demands a row ("docs/coverage.md row added/updated") — but the shipped PR-2/3 landing (b46e9b4, `git show --stat`: only `MathFin.lean` + 2 modules) added **no** coverage.md rows (grep for `HullWhiteCalibration|MonteCarloPricer` in `docs/coverage.md`: zero hits; last coverage.md commit is 3559d7a, pre-landing). Follow the template or the precedent — S-pass decision (recommend: add the rows; they are cheap and CONTRIBUTING is explicit).

If added, PR-5's list — **11 rows, all `full`** (the audited surface = the scratch's `#print axioms` list):

| # | Theorem | Faithfulness | Note |
|---|---|---|---|
| 1 | `payerSwapValue_update_eq_zero_iff` | full | par identity transported to the updated curve; honest hypotheses (δ>0, x>0, positive curve) |
| 2 | `hasDerivAt_cmsCurveRate` | full | S′ closed form |
| 3 | `hasDerivAt_cmsCurveRate'` | full | S″ closed form |
| 4 | `cmsCurveRate_convexOn` | full | weakest honest hypotheses δ>0, C>0, P₀+C≥0 |
| 5 | `annuityMeasure_isProbabilityMeasure` | full | normalization as explicit hypothesis (the disclosed honest out); real density-shape work into the numéraire engine |
| 6 | `annuityMeasure_price` | full — **closest-to-wrapper candidate** | congruence rewrite + direct application of MathFin's `changeOfNumeraire`; statement is the annuity-seat instance, not the engine's, and rewriting is real — but S-pass may reclassify |
| 7 | `cms_adjustment_nonneg` | full | Jensen instance with explicit integrability prices |
| 8 | `cms_adjustment_delta_nonneg` | full | corollary of 7 |
| 9 | `cmsCurveRate_spanning` | full | Carr–Madan instantiation, both derivatives supplied |
| 10 | `cmsCurveRate_strip_nonneg` | full | |
| 11 | `convexityNumerator_nonneg` | full | |

**No `library_wrapper` exception here** — the ask's known exception (`cox_scratch.lean`'s `cdsFairSpread_TV_balances`, PUBLISHING.md:86–92) belongs to **PR-4**, not PR-5. Consequently no `UPSTREAM_CITATIONS` row in `tools/verify/axiom_audit_gen.py` is needed unless the S-pass reclassifies row 6.

## 7. Flags for the S-pass

1. **PUBLISHING.md is stale on queue state**: mathfin HEAD = b46e9b4 (PR-2/3 landed, committed 2026-10-12); working tree clean except untracked `v.val` (not mine; left untouched). The "no upstream pin bumps while PR-1 pending" freeze premise is resolved. Branch PR-5 from current HEAD; re-run the §3 conflict grep at open time.
2. **Template vs precedent** (§6): PR template also asks for a `benchmarks/*.json` re-export shim + `metadata.formalization_status` — b46e9b4 added none of those either. Decide once, apply to PR-5.
3. **`annuityMeasure_price` faithfulness call** (§6 row 6) — the one judgment in an otherwise all-`full` set.
4. **`Finset.sum_erase_add` decl not plain-greppable on the build face** (to_additive-generated; existence proven by olean `strings` + 15 in-tree use sites + the scratch's standing clean compile at that face). I did not verify its textual decl on mathfin's newer mathlib face (different rev).
5. **Heartbeat scoping** (§4.6): which decls need raised heartbeats post-header-change is a build-face question; start per-decl on the two named, expand on demand.
6. **`MathFin.CMS` vs `MathFin.Cms`**: no in-tree acronym precedent (HullWhite/MonteCarlo are capitalized words); recommend `MathFin.CMS` matching the filename — trivial to flip.
7. **Verification slot discipline**: any `lake build`/docker run must respect host-safety (one Lean-loaded process, daemon down; docker pull-only). I ran none of them — §5 is an inspection report, not a run log.
8. The scratch's own header claims "grep-verified at the pin 784a831" — pin confirmed live this session (AC package MathFin `git log`: `784a831 feat(foundations): the bracket is adapted…`).

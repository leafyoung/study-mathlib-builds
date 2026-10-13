# PR-2 E-pass memo — Hull–White module promotion (hw_scratch.lean)

*Explorer E-pass, 2026-10-13. Read-only. Every claim below cites a path:line or a
command run in this session. Build face = `AmericanPutConvexity/.lake/packages/`
(AC pin, mathlib 81a5d257, toolchain v4.32.0) per AGENTS.md §Name-verification.*

## 0. Headline finding — the proposed home already exists; PR-2 is a DELTA, not a new module

The dispatch proposed `MathFin/Foundations/HullWhite.lean` (or `FixedIncome/HullWhite.lean`).
**What exists instead is `mathfin/MathFin/Foundations/HullWhiteCalibration.lean` —
the already-promoted PR-2 module**, and it changes the task:

- The file is a faithful port of `hw_scratch.lean` with `hw` prefixes stripped,
  `namespace MathFin.HullWhite` (`HullWhiteCalibration.lean:80`), house header
  (`:1-12`), `@[expose] public section` (`:78`), and the same 9 private helpers.
  787 lines vs scratch's 815.
- It is **committed and pushed**: mathfin clone is on branch `ito-drift-expectation`,
  HEAD `b46e9b407fa512b6bffe30ab78c2edfa473fb19e`; the HEAD tree contains
  `MathFin/Foundations/HullWhiteCalibration.lean` (blob `db54b689…`) byte-identical
  to the working file (zlib decode of `.git` objects, loose objects, this session);
  `refs/remotes/fork/ito-drift-expectation` = same sha (fork =
  `leafyoung/formal-mathfin`). Root import committed too: `MathFin.lean:227`
  `import MathFin.Foundations.HullWhiteCalibration` (HEAD blob `b575c447…` ==
  working; imports of `MonteCarloPricer` at `:228` and the three PR-1 Itô modules at
  `:219/:223/:226` also committed). The dispatch premise "uncommitted PR-1 content in
  the mathfin working tree" is **stale** — index==working for all 7 PR-relevant files
  (`.git/index` parse: coverage.md, AxiomAudit(.Gen).lean, axiom_audit_gen.py,
  MathFin.lean, HullWhiteCalibration.lean, MonteCarloPricer.lean — all match).
- The module is **behind the scratch by exactly the final three-lemma landing**.
  Absent from HullWhiteCalibration.lean (grep: only `forcing_integral_continuous`
  matches among these stems):
  | hw_scratch.lean | module name (after prefix strip) | scratch site |
  |---|---|---|
  | `hwDeterministic_const_closed_form` | `deterministic_const_closed_form` | hw_scratch.lean:142-145 |
  | `hwMean_eq_forward` | `mean_eq_forward` | hw_scratch.lean:670-676 |
  | `hwCalibCorrection_integral` | `calibCorrection_integral` | hw_scratch.lean:741-747 |
  The landed `calibMean` (HullWhiteCalibration.lean:681-693) still has the standalone
  uniqueness proof; scratch's final `hwCalibMean` routes through `hwMean_eq_forward`
  (hw_scratch.lean:684) — the delta port should replicate that refactor.
- **Creating `Foundations/HullWhite.lean` with `namespace MathFin.HullWhite` would be
  a guaranteed total collision** with HullWhiteCalibration.lean (same namespace, all
  public names). PR-2 = extend HullWhiteCalibration.lean in place + coverage/audit
  bookkeeping. No new file, no new root import.

## 1. External dependencies (verified on the build face unless stated)

Compile evidence first — both ran clean in this session:

- `cd AmericanPutConvexity && lake env lean ../builds/lean/port-test-hw.lean` →
  EXIT=0, 3.8s, 24 `#print axioms` lines all `[propext, Classical.choice,
  Quot.sound]`. port-test-hw.lean = committed HullWhiteCalibration.lean
  **byte-identical for lines 1-787** (cmp: only diff is the 27-line port-test-only
  audit appendix at 788-814) — so this run compiles the committed module verbatim.
- `cd AmericanPutConvexity && lake env lean ../builds/lean/hw_scratch.lean` →
  EXIT=0, 4.5s, 17/17 audited theorems standard-three, including the three delta
  theorems.

### MathFin names (pin == workspace clone, byte-identical: cmp on VasicekBondPrice.lean, WienerIntegralGaussian.lean, Vasicek.lean — all "PIN == WORKSPACE")

| Name | Definition site (AC pin = workspace clone) | Used at |
|---|---|---|
| `vasicekDeterministic` (r₀ θ κ t) | `FixedIncome/Vasicek.lean:58` | scratch:127,132,151 |
| `vasicekDeterministic_solves_ODE` | `FixedIncome/Vasicek.lean:69` | docstring only (scratch:13,76) |
| `vasicekDeterministic_tendsto_mean` | `FixedIncome/Vasicek.lean:88` | scratch:155 |
| `vasicekBondB` | `FixedIncome/VasicekBondPrice.lean:73` | throughout HW-3/HW-5 |
| `vasicekBondV` | `FixedIncome/VasicekBondPrice.lean:88` | scratch:506,517,543,569,706,743 |
| `vasicekIntegratedKernel` | `FixedIncome/VasicekBondPrice.lean:78` | scratch:508,714,718 |
| `vasicekIntegratedKernelLp` | `FixedIncome/VasicekBondPrice.lean:117` | scratch:499,505,527,541 |
| `vasicekIntegratedKernel_memLp` | `FixedIncome/VasicekBondPrice.lean:102` | scratch:510 |
| `vasicekIntegratedKernel_integral_sq` | `FixedIncome/VasicekBondPrice.lean:126` | scratch:512,712 |
| `integral_exp_mul_gaussianReal_zero` | **`Foundations/BrownianMartingale.lean:49`** (transitive via VasicekBondPrice's `public import MathFin.Foundations.BrownianMartingale`, VasicekBondPrice.lean:8) | scratch:558 |
| `wienerIntegralLp` (ns `MathFin.WienerIntegralL2`, :53-54) | `Foundations/WienerIntegralL2.lean:411` | scratch:302,313,499,541 |
| `wienerIntegralLp_hasLaw_gaussian` | `Foundations/WienerIntegralGaussian.lean:270` | scratch:304,527 |

Note: an earlier grep round reported `integral_exp_mul_gaussianReal_zero` as
"definition not found" — that was `head` truncation (BrownianMartingale sorts after
BrownianExpMoment). Symbol confirmed in `Foundations/BrownianMartingale.olean` by
olean grep, then in source at :49. Recorded so nobody re-chases it.

### BrownianMotion names (AC pin package `BrownianMotion`)

| Name | Site | Note |
|---|---|---|
| `IsPreBrownianReal` | `Gaussian/BrownianMotion.lean` — section `:173`, lemmas `:179/:188`, `.mk` `:240`, `extends` `:285` | the primary declaration line is not keyword-locatable by grep (multi-line/possibly non-`structure` form); existence and shape pinned by section+lemma sites and by the compile runs. Secondary-face caveat: none — same package is on the AC face. |
| (imported module) `BrownianMotion.Gaussian.BrownianMotion` | `WienerIntegralGaussian.lean:9`, `VasicekBondPrice.lean:7` | — |

### Mathlib names (AC face 81a5d257)

Verified by def-site grep where pinned: `gaussianReal` `Probability/Distributions/Gaussian/Real.lean:222`;
`HasLaw` `Probability/HasLaw.lean:39`; `gaussianReal_const_add` `Gaussian/Real.lean:392`;
`gaussianReal_const_mul` `:404`; `integral_id_gaussianReal` `:539`;
`intervalIntegral.integral_same` `MeasureTheory/Integral/IntervalIntegral/Basic.lean:680`;
`contDiff_one_iff_deriv` `Analysis/Calculus/ContDiff/Deriv.lean:98`;
`Real.exp_le_one_iff` `Analysis/Complex/Exponential.lean:338`;
`hasDerivAt_id` `Analysis/Calculus/Deriv/Basic.lean:681`.
The remaining interval-integral/differentiation/L²/algebra names
(`integral_hasDerivAt_right`, `integral_eq_sub_of_hasDerivAt`, `integral_comp_sub_left`,
`integral_of_le`, `integral_congr(_ae)`, `integral_const(_mul)/sub/add`,
`memLp_top_of_bound`, `MemLp.toLp`/`coeFn_toLp`, `stronglyMeasurableAtFilter`,
`Continuous.intervalIntegrable`, `ae_restrict_iff'`, `measurableSet_Ioc`, `ae_of_all`,
`mul_left_cancel₀`, `eq_of_sub_eq_zero`, `Real.exp_ne_zero`, `Differentiable.continuous`,
`NNReal.coe_injective`, `Real.coe_toNNReal`, `hasDerivAt_const`) resolve in the AC
mathlib tree (usage-site hits in the sweep) and are **compile-verified by the two
EXIT=0 runs above** — that is the binding verification for this face.

## 2. Private helpers that must ship (all already `private` in both faces)

Scratch name → landed module name (namespace-stripped; `HullWhiteCalibration.lean` line):

| scratch | module | module line |
|---|---|---|
| `hwKernelLp_integral_sq` | `kernelLp_integral_sq` | :297 |
| `hwKernelV_nonneg` | `kernelV_nonneg` | :308 |
| `hwKernelWienerLaw` | `kernelWienerLaw` | :316 |
| `hwI_continuous` | `forcing_integral_continuous` (renamed) | :384 |
| `hwVasKernelLp_integral_sq` | `vasKernelLp_integral_sq` | :520 |
| `hwVasKernelV_nonneg` | `vasKernelV_nonneg` | :532 |
| `hwVasKernelWienerLaw` | `vasKernelWienerLaw` | :539 |
| `hwCalib_deriv_eq` | `calib_deriv_eq` | :620 |
| `hwCalibVar_key` | `calibVar_key` | :728 |

The three `vasKernel*` reconstructions duplicate `VasicekBondPrice.lean`'s own
privates (`vasicekIntegratedKernelLp_integral_sq` :177, `vasicekBondV_nonneg` :188,
`vasicekWienerLaw` :196) — forced, since `private` is file-scoped. Upstream
VasicekBondPrice keeps them private, so the new module keeps its copies. The three
delta theorems need only already-present helpers (`calibVar_key` :728,
`var_eq_interval` :708) and Mathlib `intervalIntegral.integral_const_mul`.

## 3. Name conflicts against the existing mathfin tree

- **Total conflict with the proposal as written**: `Foundations/HullWhiteCalibration.lean`
  owns `namespace MathFin.HullWhite` and all public names (`deterministic`, `mean`,
  `theta`, `kernel*`, `bond*`, `calib*`, `reprices_curve`, …). A new
  `Foundations/HullWhite.lean` in the same namespace duplicates every declaration.
  No other file uses the namespace: `grep -rln "MathFin.HullWhite"` over
  `mathfin/MathFin/`, `MathFin.lean`, `mathfin/tests` → HullWhiteCalibration.lean only.
- No `FixedIncome/HullWhite.lean`, no other `*Hull*` file in `mathfin/MathFin/`
  (find -iname `*hull*`).
- The three delta names have **zero hits** in `mathfin/MathFin/`
  (`grep -rn "mean_eq_forward|const_closed_form|calibCorrection_integral"` → empty).
- Root-level (namespace-less) collisions: not applicable — every promoted declaration
  lands inside `namespace MathFin.HullWhite`.

## 4. House-style deltas (scratch → CONTRIBUTING.md + shipped modules)

Ground truth: `mathfin/CONTRIBUTING.md` §Style/§Adding-a-theorem; style model
`FixedIncome/VasicekBondPrice.lean` (shipped, FixedIncome face); landed exemplar
`Foundations/HullWhiteCalibration.lean`.

1. **Header** — scratch has none (`import Mathlib` at line 1). House: copyright
   block (`Copyright (c) 2026 Raphael Coelho`, Apache 2.0, `Authors: Raphael Coelho`,
   VasicekBondPrice.lean:1-6), `module` + `public import Mathlib` + explicit public
   imports (`:7-12`), module docstring with `## Result` listing public
   defs/lemmas (CONTRIBUTING.md:106-107; HullWhiteCalibration.lean:44-75 uses
   `## Result` — note VasicekBondPrice uses `## Main results`; CONTRIBUTING's
   `## Result` wins for the delta edit), then `@[expose] public section`
   (HullWhiteCalibration.lean:78 — CI-enforced: tests/test_router.py:96-116
   module-exposure guard).
2. **Namespace + naming** — scratch is root-level with `hw` prefixes; house is
   `namespace MathFin.HullWhite` with prefixes stripped. The delta lemmas port as
   `deterministic_const_closed_form`, `mean_eq_forward`, `calibCorrection_integral`.
3. **One-theorem-per-file (CONTRIBUTING.md:101-102) vs monolith** — the shipped
   FixedIncome modules are monolithic per model family (VasicekBondPrice carries the
   whole affine term structure). De-facto rule: one file per family; delta extends
   the existing family file. No split.
4. **Private helpers** — scratch already complies (9 `private lemma`s);
   CONTRIBUTING.md:102 satisfied as-is.
5. **Comment discipline** — CONTRIBUTING.md:103-105 says "default to no comments",
   but every shipped module carries full per-declaration docstrings
   (VasicekBondPrice.lean included): de-facto style = documented declarations. The
   delta must, however, **strip lesson/narrative references** from ported
   docstrings ("lesson 0020 step 3/4", "the desk identity", "HW-1…HW-5" at
   scratch:586,660,676-677,686,736,740,782,787) — the landed module's voice is
   course-neutral (its header rewrote the same content without them).
6. **`#print axioms` audit block** — scratch ends with one (hw_scratch.lean:799-815);
   the landed module excludes it by design: port-test appendix comment states "the
   in-tree module stays clean; the canonical audit lives in the generated
   `MathFin/AxiomAuditGen.lean`" (port-test-hw.lean:789-791). Keep the module clean;
   extend the *port-test* appendix with the 3 new audit lines.
7. **Tactic style** — scratch already matches house (`field_simp; ring` close-outs,
   `fun_prop` continuity goals, `simpa` bridging): no delta.
8. **`open`s/variables** — landed module keeps scratch's
   `open MeasureTheory ProbabilityTheory Real Set` / `open scoped NNReal` /
   `open MathFin WienerIntegralL2` and the `variable {Ω …} {B : ℝ≥0 → Ω → ℝ}` block
   (HullWhiteCalibration.lean:82-88): delta needs nothing new.
9. **Placement of the delta** (dependency-ordered, mirroring scratch):
   `deterministic_const_closed_form` after `deterministic_const` (:153);
   `mean_eq_forward` immediately before `calibMean` (it is its `κ ≠ 0`
   generalization; scratch:670-684); optional `calibMean` proof refactor to
   `mean_eq_forward f0 hf0 κ σ hκ.ne' t`; `calibCorrection_integral` after
   `calibVar_key`/:728 (uses it), before `calibIntegratedMean` (:743, which does not
   use it — same relation as scratch). Update the `## Result` list (:56-74) and the
   private-lemma list (:74 needs no change).

## 5. Local compile-verification feasibility (before opening the PR)

- **In mathfin's own env: NOT feasible locally, by design.** `mathfin/.lake/build`
  does not exist (0 `.olean`, 0 `.ilean` — measured this session); a check would
  require a full `lake build` of Mathlib + deps at mathfin's pins, on toolchain
  `leanprover/lean4:v4.33.0-rc1` (`mathfin/lean-toolchain:1`) — `lake build` in
  mathfin is forbidden to this program (dispatch + mathfin AGENTS.md host-safety:
  one Lean-loaded process, never local `docker compose build`), and all docker is
  forbidden to this dispatch. **The canonical gate therefore rides the CI trio**
  (`pytest tests/ -q` → `python3 -m tools.verify.ledger status` → `lake build`,
  CONTRIBUTING.md:39-40) in the verify container, i.e. on GitHub after the PR is
  opened from the fork (`fork` remote already points at
  `leafyoung/formal-mathfin`, and the base branch is already pushed).
- **On the AC build face: feasible and already done here** (two `lake env lean`
  runs, both EXIT=0, §1). This is a strong proxy — same module-system regime, and
  all three Mathlin/MathFin dependency modules are byte-identical between the AC pin
  and the workspace clone — but **not the canonical gate**: AC is v4.32.0/mathlib
  81a5d257 vs mathfin CI v4.33.0-rc1 + mathfin's own pins.
- **B-pass vehicle for the delta** (concrete): the AC pin's MathFin does not contain
  HullWhiteCalibration (Foundations build dir grep: Wiener* only), so nothing on the
  AC face can `import MathFin.Foundations.HullWhiteCalibration`. The vehicle is the
  established one: a single standalone file = module body + 3 appended theorems +
  extended `#print axioms` appendix — i.e. exactly `port-test-hw.lean` with the
  delta folded in (mirror of the existing `cmp`-verified relationship). B-pass
  compiles it once; orchestrator V-pass re-runs it.

## 6. coverage.md rows (faithfulness)

- **Post-delta module content**: 10 public defs + **27 public theorems/lemmas**
  (24 committed + 3 delta) + 9 private helpers (grep counts: scratch 10/27/9,
  module 10/24/9). The `#print axioms` audit covers all 27 publics after the delta
  (24 recorded in port-test-hw-axioms.log + this session's runs; 3 delta theorems
  verified standard-three in the scratch run).
- **Faithfulness**: all rows `full`. No `library_wrapper` in PR-2 — nothing here
  re-exports a named upstream lemma as the whole proof. The known library_wrapper
  exception (`cox_scratch.lean`'s `cdsFairSpread_TV_balances` + `UPSTREAM_CITATIONS`
  row) belongs to **PR-4**, not PR-2 (PUBLISHING.md:87-93).
- Two soft spots to record honestly if rows are added:
  `deterministic_const_closed_form` is a corollary (one `rw` of the proved
  `deterministic_const` bridge + `rfl`-unfold of `vasicekDeterministic`,
  scratch:142-145) — the real work lives in `deterministic_const`; and
  `deterministic_at_zero` is a `simp` initial-condition lemma. Neither is a
  structure-projection; `full` is defensible, but note the coverage vocabulary
  (docs/coverage.md:14-16: "ring/simp/rfl on a structure-projection target does NOT
  qualify") when writing the rows.
- **De-facto practice**: coverage.md's audit tables are benchmark-id-keyed
  (e.g. `cm-thm-4.3.7`, docs/coverage.md:50-53). Greps this session: **0** rows for
  HullWhite, ItoDriftExpectation, CrossHorizon, MonteCarloPricer; **0** benchmark
  files reference HullWhite. So current CI requires **no new rows**; PUBLISHING.md:86
  ("row per theorem") is stricter than upstream practice — S-pass decides which to
  follow (PUBLISHING.md's per-theorem rows are additive and safe; they just don't
  match the file's existing schema).

## 7. Flags for the S-pass

1. **Scope correction (blocking decision)**: extend
   `MathFin/Foundations/HullWhiteCalibration.lean` in place; do NOT create
   `Foundations/HullWhite.lean` or `FixedIncome/HullWhite.lean` (§0, §3).
2. **Tree state**: work happens as new commit(s) on mathfin branch
   `ito-drift-expectation` (HEAD = fork state b46e9b40). Nothing needs
   preserving-by-freezing; the "uncommitted PR-1 content" premise is stale (§0).
   This explorer did not run git (read-only `.git` object/index decodes only).
3. **`calibMean` refactor decision**: scratch's final state routes `hwCalibMean`
   through `hwMean_eq_forward` (scratch:684); landed module has a standalone proof
   (HullWhiteCalibration.lean:688-693). Porting the refactor keeps one proof body;
   keeping both is also sound (both compile).
4. **Docstring voice**: strip "lesson 0020"/"HW-n"/"desk identity" narrative from
   the three ported docstrings (§4.5).
5. **Verification gates**: local = AC-face port-test compile (§5 vehicle); canonical
   = GitHub CI trio on v4.33.0-rc1 + mathfin pins. The toolchain delta (v4.32.0 vs
   v4.33.0-rc1) is a residual risk the CI trio retires.
6. **AxiomAuditGen**: `MathFin/AxiomAuditGen.lean` and `AxiomAudit.lean` contain 0
   HullWhite names (grep). Not regenerated here (regeneration writes into mathfin —
   out of bounds for this explorer). CI `test_values` demands byte-fresh
   regeneration at PR time; whether the generator (tools/verify/axiom_audit_gen.py)
   scans only benchmark-cited theorems (likely, since it is benchmark-keyed) should
   be confirmed by whoever runs the CI trio — if benchmark-keyed, no HullWhite rows
   appear and no `UPSTREAM_CITATIONS` entries are needed (those are for
   `library_wrapper` only, CONTRIBUTING.md:92-97).
7. **Stale numbers in the planning docs**: PUBLISHING.md:63-64 says "the 14 audited
   theorems"; QUEUE.md:81 says "33 declarations". Actuals: scratch 46 decls
   (10 defs / 27 public / 9 private), 17-audit block; module 43 decls, 24-audit
   block; post-delta 27 audited publics. Update PUBLISHING.md/QUEUE.md when PR-2
   lands.
8. **`IsPreBrownianReal` def-site**: declaration line not grep-located in
   `BrownianMotion/Gaussian/BrownianMotion.lean` (section :173, `.mk` :240);
   compile-verified. B-pass may pin the exact line for the record (non-blocking).
9. **Coverage-row decision** (§6): PUBLISHING.md checklist vs benchmark-keyed
   de-facto schema — pick one and note it in the PR description.
10. **PR logistics**: `.github/PULL_REQUEST_TEMPLATE.md` exists (mathfin/.github);
    PR opened from the fork branch (already pushed); PR description should carry the
    honest-hypothesis list (ContDiff ℝ 1 f0 packaging deriv+continuity via
    `contDiff_one_iff_deriv`, κ > 0 vs κ ≠ 0 splits, continuity hypotheses where FTC
    needs them), the verification transcript (this memo's two compile runs + the
    recorded port-test log), and the provenance pointer (course lesson 0020 +
    builds/lean/hw_scratch.lean).

## Session verification transcript (checks actually run)

1. `lake env lean ../builds/lean/port-test-hw.lean` (in AmericanPutConvexity) →
   EXIT=0, 3.8s, 24/24 standard-three. **Run in this session.**
2. `lake env lean ../builds/lean/hw_scratch.lean` (in AmericanPutConvexity) →
   EXIT=0, 4.5s, 17/17 standard-three incl. the 3 delta theorems. **Run in this
   session.**
3. `cmp` pin vs workspace for VasicekBondPrice.lean / WienerIntegralGaussian.lean /
   Vasicek.lean → identical. `cmp` port-test-hw.lean vs committed
   HullWhiteCalibration.lean → identical through line 787.
4. mathfin `.git` HEAD-tree + index decodes (python3/zlib/sha1, read-only) →
   committed-and-pushed state as described in §0.
5. Greps: mathfin tree for delta names (0 hits), `MathFin.HullWhite` namespace users
   (1 file), coverage.md/benchmarks for HullWhite (0), `mathfin/.lake/build` oleans
   (0), sorry counts (scratch: 1 hit = the docstring prose "No `sorry`." at
   hw_scratch.lean:28; module: 0), declaration counts (§6).
6. Not run (and why): `lake build` in mathfin, any docker command, any git command,
   AxiomAuditGen regeneration — all out of bounds for this explorer (dispatch +
   host-safety doctrine).

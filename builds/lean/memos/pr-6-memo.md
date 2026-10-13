# PR-6 E-pass memo — promoting `builds/lean/hw_bootstrap.lean` → MathFin `FixedIncome/Bootstrapping`

E-pass (Explorer·PR-6), 2026-10-13. Read-only; I ran no `lake build`, no docker, no git.
Sources read: the scratch file, `mathfin/CONTRIBUTING.md`, `builds/lean/PUBLISHING.md`,
`builds/lean/QUEUE.md:42`, `mathfin/AGENTS.md`, `docs/coverage.md`, `docs/patterns.md` (head),
`tests/test_router.py` / `test_values.py` / `test_ledger.py` (gate sections),
`tools/verify/axiom_audit_gen.py` (docstring + scan scope), `.github/PULL_REQUEST_TEMPLATE.md`,
`mathfin/lakefile.lean` (lint config), the style models (`FixedIncome/YieldCurve.lean`,
`FixedIncome/FRA.lean`, `FixedIncome/InterestRateSwap.lean`, `FixedIncome/ZCB.lean`,
`Foundations/Bisection.lean`, landed promotion `Foundations/HullWhiteCalibration.lean`),
the sibling memo `memos/pr-5-memo.md`, and the three package faces. Every name below was
verified in this session by grep/ls/diff as cited.

## 0. Headline state (two corrections to the dispatch brief)

1. **mathfin HEAD is `b46e9b4`; PR-1/2/3 have landed.** The dispatch brief's premise "the
   working tree has uncommitted PR-1 content" is **stale** — the same correction the PR-5
   E-pass made (`memos/pr-5-memo.md:7`, which ran `git status --short` in `mathfin/`:
   clean except untracked `v.val`). My own file evidence agrees: the PR-2 module
   `mathfin/MathFin/Foundations/HullWhiteCalibration.lean` and PR-3's
   `mathfin/MathFin/Foundations/MonteCarloPricer.lean` exist and are root-imported
   (`mathfin/MathFin.lean:228`); `MathFin.lean` mtime 2026-10-12 09:33 matches the b46e9b4
   commit date. I did not run git myself (constraint); treat "tree clean" as carried from
   the sibling pass.
2. **The PR-6 flag in PUBLISHING.md is inverted by the evidence: `Foundations/Bisection.lean`
   EXISTS at the PR base.** PUBLISHING.md:74–76 says to flag that "the pin lacks
   `Foundations/Bisection.lean`" and ship a self-contained engine. That is a statement about
   the *workspace build face* (AC-vendored MathFin at pin **784a831**, where
   `AmericanPutConvexity/.lake/packages/MathFin/MathFin/Foundations/Bisection.lean` is
   indeed absent — `ls`: No such file). But at mathfin HEAD the file **exists, is committed,
   and is root-imported**: `mathfin/MathFin/Foundations/Bisection.lean` (mtime 2026-10-01
   17:07 = clone checkout time, unlike the Oct 6–12 Itô batch; `MathFin.lean:97`
   `import MathFin.Foundations.Bisection` sits in the pre-"Phase 13" block), 127 lines,
   namespace `MathFin`, API **byte-equivalent in shape to the scratch's private port**
   (`bisectStep`/`bisect`/`bisectMid`/`bisect_zero`/`bisect_succ`/`bisectStep_snd_sub_fst`/
   `bisect_snd_sub_fst`/`mapsTo_bisectStep`/`bisect_mem`/`abs_bisectMid_sub_le`/
   `tendsto_bisectMid`, Bisection.lean:56–125 vs scratch:88–158; the only textual delta in
   `tendsto_bisectMid` is `one_lt_two` (Bisection.lean:125) vs the scratch's
   `(by norm_num : (1 : ℝ) < 2)` (scratch:157)). **Consequence:** promoting the scratch's
   engine verbatim into `namespace MathFin` is impossible (11 duplicate declarations, §3);
   and carrying it in a sub-namespace duplicates public upstream code a reviewer will
   bounce. Recommendation: **drop the engine, `public import MathFin.Foundations.Bisection`**
   (Option B, §3/§5/§7); the PUBLISHING.md PR-6 flag text should be rewritten when the PR lands.

## 1. External dependencies (every imported name from outside the file)

### 1a. MathFin names — verified on the BUILD FACE (`AmericanPutConvexity/.lake/packages/MathFin`, pin 784a831 per `AmericanPutConvexity/lake-manifest.json`)

Consumed by the scratch (`open MathFin` sections; re-verified by grep):

| Name | Kind | Build-face site | Pin↔HEAD drift |
|---|---|---|---|
| `fraForwardRate` | noncomputable def | `FixedIncome/FRA.lean:46` | none — `diff` FRA.lean IDENTICAL across faces |
| `fraValue` | def | `FixedIncome/FRA.lean:49` | none |
| `fraValue_forwardRate_eq_discount_difference` | theorem | `FixedIncome/FRA.lean:53` | none |
| `fraValue_zcb_eq_zero_iff` | theorem | `FixedIncome/FRA.lean:67` | none |
| `zcb` | noncomputable def | `FixedIncome/ZCB.lean:40` | see note |
| `zcb_pos` | lemma | `FixedIncome/ZCB.lean:48` | see note |
| `annuity` | def | `FixedIncome/InterestRateSwap.lean:35` | none — IRS.lean IDENTICAL |
| `payerSwapValue` | def | `InterestRateSwap.lean:39` | none |
| `parSwapRate` | noncomputable def | `InterestRateSwap.lean:43` | none |
| `payerSwapValue_eq_zero_iff` | theorem | `InterestRateSwap.lean:53` | none |

**Pin↔HEAD drift check (ran `diff` on all four imported modules):** FRA.lean,
InterestRateSwap.lean, YieldCurve.lean byte-IDENTICAL between the AC pin face and the
mathfin working tree; **ZCB.lean differs at HEAD** — HEAD adds
`public import MathFin.Foundations.DerivOfDeriv` and refactors the convexity lemmas
(`hasDerivAt_zcb_r_r` becomes `private`, new `hasDerivAt_deriv_zcb_r`,
`zcb_convexity_eq_time_to_maturity_sq` now via `deriv`). The surface the scratch consumes
(`zcb`, `zcb_pos`) is untouched by that diff. **No drift on the consumed surface.**

**Option-B-only dependency (HEAD face only — NOT on the build face):** the engine names
`bisectStep`, `bisect`, `bisectMid`, `mapsTo_bisectStep`, `bisect_mem`,
`abs_bisectMid_sub_le`, `tendsto_bisectMid` ship at
`mathfin/MathFin/Foundations/Bisection.lean:56–121` (namespace `MathFin`, public).
Verified on the mathfin working tree only; the AC pin face lacks the file, so an
Option-B module **cannot** be port-tested at the AC face (§5).

### 1b. Mathlib names — verified on BOTH mathlib faces (build face `AmericanPutConvexity/.lake/packages/mathlib` 81a5d257 / v4.32.0; upstream face `mathfin/.lake/packages/mathlib` 0434c03 / v4.33.0-rc1)

Ran one grep per name over both faces; every hit landed in the **same file** on both:

- `squeeze_zero` — `Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean:38` (also `squeeze_zero'` :32; verified on both faces)
- `tendsto_iff_dist_tendsto_zero` — `Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `Filter.Tendsto.div_atTop` — `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`
- `tendsto_pow_atTop_atTop_of_one_lt` — `Mathlib/Analysis/AbsoluteValue/Equivalence.lean`
- `tendsto_add_atTop_nat` — `Mathlib/Analysis/Normed/Group/Continuity.lean`
- `StrictMonoOn.lt_iff_lt` — `Mathlib/Order/Monotone/Basic.lean`
- `lt_div_iff₀`, `div_le_iff₀`, `Nat.le_ceil` — `Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`
- `Real.logb_self_eq_one` (`Log/Base.lean:64`), `Real.logb_pow` (`:124`), `Real.logb_le_logb` (`:189` — line numbers from the upstream-face grep; file identical-name hit on both faces)
- `mul_lt_mul_of_pos_right` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `Function.iterate_succ_apply'` — `Mathlib/Algebra/Group/ForwardDiff.lean`
- `abs_sub_le_iff` — `Mathlib/Algebra/Order/AbsoluteValue/Basic.lean`; `abs_mul`, `abs_of_pos`, `dist_nonneg`, `tendsto_const_nhds`, `Nat.cast_add`, `div_pos`, `le_of_not_gt`, `one_lt_two`, `List.cons_ne_nil`, `List.length_cons` — hits on both faces (files as returned by the grep batch)
- `Set.MapsTo.iterate` — `Mathlib/Data/Set/Function.lean`
- `List.head_cons` — **Lean core**, not Mathlib: `Init/Data/List/Basic.lean:367` (`@[simp, grind =] theorem head_cons`) in the installed v4.33.0-rc1 toolchain (`~/.elan/toolchains/`); the scratch's clean compile at the v4.32.0 AC face (below) covers that toolchain.

**`Real.log₂` does not exist on EITHER face** (grep of `Mathlib/Analysis/SpecialFunctions/Log/`
+ `Mathlib/Data/Real/` and a whole-tree `def log2`/`Real.log₂` grep on the upstream face:
zero hits). The scratch's `Real.logb 2` step-budget phrasing (scratch:243–278) is correct
upstream too; only its *comment wording* ("at this Mathlib pin") needs de-workspacing.

**Long tail** (`Filter.Tendsto`/`atTop`/`𝓝`, `Set.Icc/Ioi`, `×ˢ`, `StrictAntiOn`/`StrictAnti`,
`Finset.range`, `div_eq_iff`, `div_eq_div_iff`, `div_ne_zero`, `not_lt`, `lt_irrefl`,
`ne_of_gt`, `lt_of_lt_of_le`, `eq_or_lt` on `le`, `pow_pos`/`pow_nonneg`/`div_nonneg`/
`mul_nonneg`/`sub_nonneg`, `mul_le_mul_of_nonneg_left`, `abs_sub_comm`, `one_pos`):
not individually re-grepped; their build-face validity is carried by the standing
verification that `hw_bootstrap.lean` compiles axiom-clean at exactly the AC face
(`builds/lean/hw_bootstrap-axioms.log`: 41 audited declarations, all
`[propext, Classical.choice, Quot.sound]`; PUBLISHING.md:38–39; QUEUE.md:42 item 13 DONE).
**Binder-shape caveat:** string-presence on the upstream face ≠ identical binder shapes;
`Real.logb_le_logb` (section-variable `b`/`hb` at `Log/Base.lean:186–189`) is the likeliest
drift point — B-pass first checkpoint re-verifies on the PR face (§7.5).

## 2. Private helpers that must ship (upstream style: helpers `private`)

Scratch declares **zero** `private`. House precedent: landed promotions ship helpers
`private` (`HullWhiteCalibration.lean` has 10 `private` decls; `ZCB.lean:79`
`private lemma hasDerivAt_zcb_r_r`; CONTRIBUTING.md:101–102). Candidate split
(S-pass final call), under Option B (35 shipping decls):

- **`private` candidates** (consumed only inside the file): `threshold_affine`,
  `threshold_of_strictMonoOn`, `threshold_of_strictAntiOn` (the three bridges —
  pure proof glue for every `*Threshold`/`*Step` theorem), `boot_succ`
  (definitional unfolding, `rfl`), and `boot_succ_ne_nil` *only if* the public
  statements are restated to discharge head-nonemptiness inline (`by simp [boot]`);
  see §7.6.
- **Keep public**: `fraThreshold` / `swapThreshold` / `swapLastCouponThreshold`
  (instrument-level facts with independent meaning), everything appearing in a public
  statement (`boot`, `boot_length`, `boot_step_err`, `boot_reprices_all`,
  `boot_reprices_range` — `boot_succ_ne_nil` currently appears **in public statements**
  as the `List.head` proof argument, scratch:534, 554, 571), and the whole
  FRA/swap affine + root families.
- Under a fallback Option A (self-contained engine, §3/§7.2), the 11 engine decls ship
  `private` inside `namespace MathFin.Bootstrapping` (shadow-free vs upstream's public
  `MathFin.bisect*`), plus the scratch's `bisect_zero`/`bisect_succ`/`bisect_mem`/
  `bisectStep_snd_sub_fst` which have no upstream-private counterpart.
- **Docstrings on every shipped `def`** — `lake lint` reds a missing `def` docstring
  (PR template; `lakefile.lean:8–21` wires Batteries `runLinter`, scoped `#["MathFin"]`).
  Scratch decls all carry docstrings except `bisect_zero`/`bisect_succ`
  (scratch:101,103) — both vanish under Option B; under Option A add two one-liners.

## 3. Name conflicts against the existing mathfin tree

Ran a declaration grep (`(theorem|lemma|def|abbrev|instance) <name>`) for **all 46** scratch
names over `mathfin/MathFin/**/*.lean`:

- **11 HARD conflicts**: `bisectStep`, `bisect`, `bisectMid`, `bisect_zero`, `bisect_succ`,
  `bisectStep_snd_sub_fst`, `bisect_snd_sub_fst`, `mapsTo_bisectStep`, `bisect_mem`,
  `abs_bisectMid_sub_le`, `tendsto_bisectMid` — all declared **public in
  `namespace MathFin`** at `Foundations/Bisection.lean:56–121` (committed at HEAD).
  Self-containment inside `namespace MathFin` = duplicate-declaration errors. Resolutions:
  - **Option B (recommended)**: drop the engine; `public import
    MathFin.Foundations.Bisection`. Zero conflicts remain. The engine section
    (scratch:81–158) is deleted wholesale; every consumer (`abs_bisectMid_sub_le`,
    `tendsto_bisectMid`, `bisectMid`) resolves to the upstream `MathFin.*` name.
  - **Option A (fallback, per current PUBLISHING.md text)**: keep the engine, but the
    module must then use a two-level `namespace MathFin.Bootstrapping` (the landed
    promotion convention: `HullWhiteCalibration.lean:80` `namespace MathFin.HullWhite`)
    so the private copies shadow rather than clash — at the cost of duplicating public
    upstream code (review risk, §7.2).
- **Zero conflicts for the 35 module-specific names** (`threshold_*`, `affineStep_*`,
  `fraValue_*`, `strictAnti*`, `fra*`, `payerSwapValue_*`, `swap*`, `boot_*`,
  `fraBootstrap_flatCurve`) — grep clean, including the 361 KB uncommitted-era
  `ItoFormulaAdaptedDrift.lean`.
- **Home path free**: `MathFin/FixedIncome/Bootstrapping.lean` exists on neither face
  (directory listings: 24 files each); no `Bootstrapping` string anywhere in
  `mathfin/MathFin/` or `MathFin.lean`. Note the topical neighbor:
  `FixedIncome/YieldCurve.lean` is *also* called "Yield curve bootstrapping" (its :11
  docstring) and owns the closed-form `bootstrap_solve*` names (benchmark ids
  `mf-bootstrap-solve{,-first,-second}`, `mf-bootstrap-consistency` in
  `benchmarks/mathematical_finance.json`) — a **different** result family (closed-form
  coupon-bond recursion vs this file's numerical bisection engine); the PR body should
  draw that boundary explicitly and cross-link.
- **Root import**: add a plain `import MathFin.FixedIncome.Bootstrapping` line to
  `MathFin.lean` (FixedIncome block :377–410; e.g. after `YieldCurve` at :382; the landed
  pattern is a plain `import` + one-line comment, cf. `MathFin.lean:228`).
- Caveat: HEAD may move before the PR opens — re-run the (cheap) grep at branch time.

## 4. House-style deltas (scratch → CONTRIBUTING.md + landed-module practice), per item

1. **Header block** (CONTRIBUTING.md:106–107; YieldCurve.lean:1–8): add copyright
   (`Copyright (c) 2026 Raphael Coelho`, Apache 2.0, Authors) + literal `module` line +
   `public import Mathlib` + `public import MathFin.FixedIncome.{ZCB,InterestRateSwap,FRA}`
   (+ `public import MathFin.Foundations.Bisection` under Option B). Scratch's plain
   `import Mathlib` / `import MathFin.*` (scratch:1–4) → `public import`.
2. **`@[expose] public section`** after the module docstring — CI-enforced:
   `tests/test_router.py:106` `test_mathfin_module_files_expose_public_section` iterates
   **all** `MathFin/**/*.lean`.
3. **Namespace** `Bootstrap` → `MathFin.Bootstrapping` (landed promotion convention,
   HullWhiteCalibration.lean:80). The scratch's per-section `open MathFin`
   (scratch:283,389,584) then disappears — inside `namespace MathFin.*` the MathFin
   names resolve directly.
4. **Module docstring**: compress the 66-line teaching header (scratch:6–73) to a
   HullWhiteCalibration-style docstring ending in the results list; keep a
   "Structural note:" paragraph for the per-prefix threshold hypothesis (scratch:524–528 —
   the honest-curve-level-statement caveat) and the excluded-instruments scope
   (scratch:60–70, forward-starting legs + joint solves). Drop lesson-0030/Exercise
   references and the "No `sorry`" sentence (scratch:72).
5. **Forbidden-text gate**: `tests/test_values.py:58–67` bans `\bsorry\b`, `\badmit\b`,
   `native_decide`, `polyrith`, `exact?`/`apply?`/`rw?`/`simp?` over **comment-stripped**
   MathFin sources (`test_values.py:78–92`, via `strip_comments`). The scratch is clean
   in code; the word `sorry` appears only in the docstring (scratch:72), which stripping
   removes — still delete it (don't rely on the stripper), and note the richer ban list
   vs the workspace's habit.
6. **Audit block stripped**: the trailing `#print axioms` block (scratch:622–662) does not
   ship — axiom auditing rides byte-fresh `AxiomAuditGen.lean`
   (`python3 -m tools.verify.axiom_audit_gen --write`; generator pins every
   benchmark-cited MathFin constant, `axiom_audit_gen.py:1–15` — a benchmark-less module
   adds no rows to it).
7. **`private` helpers**: per §2.
8. **Comment discipline** (CONTRIBUTING.md:102–105): keep the storied def/theorem
   docstrings (house style — every shipped module has them) and only non-obvious
   why-comments (e.g. the pin-workaround note at scratch:243–245, reworded
   upstream-facing: "`Mathlib` states the log ladder over `Real.logb`"); drop
   lesson narration from proof bodies.
9. **Tactic style**: already conforming — `field_simp; ring` close-outs
   (scratch:359–360, 374–379, 604–609), `split_ifs`/`rcases`/`linarith`/`calc` all
   in-house; no `bs_identity` needed (not BS-family). `set_option autoImplicit false`
   (scratch:75): keep — FRA.lean:38/InterestRateSwap.lean:27 carry it (YieldCurve
   doesn't; mixed house practice, the imported modules set it).
10. **Pointer comments** (`-- pointers:`/`-- benchmark-id:` FRA.lean:11–16): omit —
    benchmark-less modules don't carry them (YieldCurve.lean has none either... it is
    benchmark-backed; the *landed* promotions HullWhite/MonteCarlo omit them — current
    convention, matching pr-5-memo §4.5).
11. **`lake lint` sweep** (PR template; `lakefile.lean:8–21`): watch unused-variable lints
    (the scratch's deliberately-unused bracket hypotheses are already `_`-prefixed:
    `swapThreshold`'s `_hx` scratch:410, `swapLastCouponThreshold`'s `_hx` scratch:470).
12. **Naming register** (CONTRIBUTING.md:105 "identifiers carry the what"): in the flat
    upstream namespace the terser names read thin — consider `boot` →
    `bootstrapCurve` (or `bootstrappedCurve`), `affineStep_*` → `bootstrapAffine_*`,
    mirroring YieldCurve's `bootstrap_solve*` register. Cosmetic; S-pass call.

## 5. Local compile-verification feasibility BEFORE the PR (inspection; I ran no lake build, no docker)

Facts established this session:

- mathfin toolchain `leanprover/lean4:v4.33.0-rc1` (`mathfin/lean-toolchain:1`) is
  **installed** (`~/.elan/toolchains/` lists v4.32.0, v4.33.0-rc1, v4.35.0-rc3).
- mathfin's **Mathlib layer is built**: `mathfin/.lake/packages/mathlib/.lake/build` holds
  **8,302 oleans** (find count). **BrownianMotion is NOT built** (0 oleans) — but it is
  **not in this module's import closure** (checked: Bisection.lean:8, ZCB HEAD imports
  Mathlib + `Foundations/DerivOfDeriv`, and DerivOfDeriv.lean:8 imports Mathlib only;
  FRA/IRS import Mathlib + ZCB).
- mathfin's **own oleans are absent**: `mathfin/.lake/` contains only `config` + `packages`
  — no `build/`. So `cd mathfin && lake env lean <any MathFin module>` fails at import
  resolution today. Verifying the promoted module in mathfin's env first requires a
  **targeted build of the five dependency modules**:
  `lake build MathFin.Foundations.Bisection MathFin.Foundations.DerivOfDeriv
  MathFin.FixedIncome.ZCB MathFin.FixedIncome.FRA MathFin.FixedIncome.InterestRateSwap`
  (Mathlib layer cached ⇒ minutes, not the 5–15 min full build), then
  `lake env lean MathFin/FixedIncome/Bootstrapping.lean`. That is a lake build: out of my
  scope; per host-safety doctrine (mathfin/AGENTS.md:14–19) it takes the single
  Lean-loaded-process slot with the daemon down; writes stay in regenerable
  `mathfin/.lake/build` and touch no tracked file (PR-1 content untouched).
- **The AC-face port-test route works only for Option A.** The AC face has both layers
  materialized and built (`AmericanPutConvexity/.lake/packages/MathFin/.lake/build/lib/lean/`
  holds 85 olean-side files incl. `FixedIncome/*.olean`), and `module`/`public import`
  syntax compiles there (the vendored pin itself uses it; toolchain v4.32.0). But the pin
  **lacks** `Foundations/Bisection.lean`, so an Option-B module fails at import on that
  face. Under Option A the port-test is: promoted file copied to
  `builds/lean/pr6-port-test.lean`, then
  `cd AmericanPutConvexity && lake env lean ../builds/lean/pr6-port-test.lean`.
- **Docker route** (authoritative): `docker compose pull verify` + run is pull-only and
  doctrine-legal; the CI trio (`pytest tests/ -q` → `python3 -m tools.verify.ledger status`
  → `lake build`, CONTRIBUTING.md:39–40) plus `lake lint` (PR template) live there. I did
  not run docker (constraint); the orchestrator owns that step.
- **Cheap host-side gates runnable anywhere**: `pytest tests/ -q`,
  `python3 -m tools.verify.ledger status`, `python3 -m tools.verify.axiom_audit_gen --write`
  (Python-only; no Lean slot).

**Bottom line**: Option B is verifiable locally **only** via the targeted mathfin build
(daemon-down slot) or the CI trio; Option A is verifiable by the standing AC-face
port-test workflow today. Either way the CI trio in the pulled container is the
authoritative gate — the AC face runs mathlib 81a5d257/v4.32.0 while mathfin pins
0434c03/v4.33.0-rc1.

## 6. coverage.md rows (CONTRIBUTING.md:70–77 step 5; PR template row item)

Format precedent: dated prose paragraphs under `## Current Audit` (e.g. the FRA entry,
coverage.md:683–691), not a table. **Tension carried from pr-5-memo §6**: the landed
PR-2/3 commit added **no** coverage.md rows (grep `HullWhiteCalibration|MonteCarloPricer`
in coverage.md: zero hits — verified by the sibling pass; my own grep for
`YieldCurve|bootstrap_solve` also finds none, despite `mf-bootstrap-solve*` benchmark ids
existing). Follow the template or the precedent — S-pass decision (recommend: add the
rows; CONTRIBUTING is explicit).

If added, PR-6's list — **35 rows, all `full`** under Option B (46 under Option A);
headline rows:

| Group | Theorems | Faithfulness |
|---|---|---|
| Engine bridges | `threshold_affine`, `threshold_of_strictMonoOn`, `threshold_of_strictAntiOn` (private candidates) | full |
| Affine step | `affineStep_err`, `affineStep_tendsto`, `affineStep_value_err`, `affineStep_stepBudget` | full |
| FRA | `fraValue_affine_of_newUnknown`, `fraValue_newUnknown_eq_quote_iff`, `fraValue_affine_zcb`, `strictAntiOn_fraValue`, `fraThreshold`, `fraStep_err`, `fraStep_tendsto`, `fraRoot_parForward`, `fraRoot_agrees_with_pin` | full |
| Payer swap | `payerSwapValue_affine_of_newUnknown`, `strictAnti_payerSwapValue`, `swapThreshold`, `swapStep_err`, `swapStep_tendsto`, `swapRoot_is_par`, `payerSwapValue_affine_lastCoupon`, `payerSwapValue_affine_lastCoupon_annuity`, `strictAnti_payerSwapValue_lastCoupon`, `swapLastCouponThreshold`, `swapStep_lastCoupon_err` | full |
| Induction | `boot`, `boot_length`, `boot_succ`, `boot_succ_ne_nil`, `boot_step_err`, `boot_reprices_all`, `boot_reprices_range` | full |
| Capstone | `fraBootstrap_flatCurve` | full |

Honesty notes for the row text: the affine-unfolding lemmas
(`fraValue_affine_of_newUnknown`, both `payerSwapValue_affine_*`, `fraValue_affine_zcb`,
`boot_succ`) are small-algebra supports (`rw`+`ring`/`rfl`) in the exact register of the
shipped `fraValue_zcb_eq_discount_difference` (FRA.lean:60–63, a direct instantiation) —
flag in the row that the *deriving* theorems are the step/tendsto/budget/repricing
families. **No `library_wrapper` exception here** — the ask's known exception
(`cox_scratch.lean`'s `cdsFairSpread_TV_balances`, PUBLISHING.md:86–92) belongs to
**PR-4**, not PR-6; consequently no `UPSTREAM_CITATIONS` row is needed. The scratch's
own axiom log (`builds/lean/hw_bootstrap-axioms.log`, 41 audited decls, standard-three)
backs the row's "axioms-clean" sentence; the promotion re-runs it on the PR face.

## 7. Flags for the S-pass

1. **The Bisection decision (headline §0.2)** — Option B (import upstream engine; drop
   scratch:81–158) vs Option A (self-contained private engine in
   `namespace MathFin.Bootstrapping`). Recommendation: **B** (no duplication of public
   upstream code; upstream reviewers will ask "why not import Foundations/Bisection?"),
   with the concrete local-verification recipe of §5. PUBLISHING.md:74–76's PR-6 flag
   must be rewritten either way — its premise describes the build face, not the PR base.
2. **Option A residual risk**: the private engine would *shadow* public
   `MathFin.bisect*` inside the namespace — legal, but a reviewer-visible duplicate of
   committed upstream code; also keeps the module non-portable to any face lacking
   Bisection — the exact inverse of the original motivation.
3. **Verification slot**: any `lake build`/docker run respects host-safety (one
   Lean-loaded process, daemon down; docker pull-only). I ran none — §5 is an inspection
   report, not a run log. The only compile evidence in this E-pass is the standing AC-face
   verification of the *unmodified* scratch (axioms log + QUEUE.md:42).
4. **Mathlib-face drift**: names verified by presence on both mathlib faces; exact binder
   shapes only at the AC face. `Real.logb_le_logb` (section-variable binders) is the
   likeliest churn point; B-pass first checkpoint re-verifies on the PR face per the
   build-face convention (workspace AGENTS.md §Name-verification).
5. **Template-vs-precedent bundle** (as in pr-5-memo): benchmark shim + ledger row +
   coverage rows — PR-2/3 landed with none of them; decide once, apply to PR-6. PR-6 has
   **no benchmark ids**; the caplet/floorlet precedent (coverage.md:675–678: module
   content "carries no benchmark entry of its own … exercised through the parity identity
   and the ledger instead") is the argument if none are added.
6. **`boot_succ_ne_nil` in public statements** (scratch:534,554,571): either keep it
   public or restate the three theorems with an inline `(by simp [boot])` head proof;
   upstream linters/reviewers may prefer the latter (no helper in the public API purely
   as a proof argument).
7. **YieldCurve boundary** (§3): the PR body must delineate closed-form coupon-bond
   bootstrapping (`YieldCurve`) from numerical bisection bootstrapping (this module) and
   cross-link; also consider whether the module wants a `YieldCurve`-flavored name
   (`Bootstrapping.lean` is free and accurate).
8. **Doc drift**: PUBLISHING.md:17/74 says "45 decls / 45 theorems"; the file has
   **46 declarations** (grep count; 41 in the axiom log — the 5 missing are
   `bisect_zero`, `bisect_succ`, `bisectStep_snd_sub_fst`, `bisect_mem`,
   `boot_succ_ne_nil`, i.e. simp/glue lemmas). Update PUBLISHING/QUEUE wording when the
   PR lands.
9. **Re-run the conflict grep at branch time** (§3 caveat) — HEAD moved twice this week.

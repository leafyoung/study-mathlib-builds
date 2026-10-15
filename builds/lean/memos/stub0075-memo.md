# Memo — E-pass for flipping stub lesson 0075 (VaR detail; risk aggregation)

**Date**: 2026-10-14. **Dispatcher**: stub-flip E-pass (post-0068 pipeline: E-flash mapping →
orchestrator scope cut → author+gate → V-pass).
**Subject**: `mdbook/src/lessons/0075-var-detail-aggregation.md` (STUB; SUMMARY Part X,
ch. 24 row; registry `model-coverage-map.md:135`).

**Read this ask**: the stub in full (60 lines); `resources/fixed-income-notes-chapters/scans/ch24-scan.md`
in full (239 lines); `pdftotext resources/fixed-income-notes-chapters/ch24-risk-management.pdf`
→ `/tmp/ch24.txt` (920 lines; printed page = PDF page, offset +0 per AGENTS.md, spot-verified
against running headers 419–434 in the extraction); lesson 0050 in full (the predecessor —
what 0075 must NOT re-teach); declaration greps of all ten `mathfin/MathFin/RiskMeasures/*.lean`
files; `WorstCaseRisk.lean` and `AcceptanceSet.lean:100-140` read in full; absences greps over
all of `mathfin/MathFin/`; `builds/lean/mc_pricer.lean` + `heston_scratch.lean` headers;
`builds/lean/QUEUE.md` tail; `mdbook/src/reference/model-coverage-map.md:79,:135`;
`mdbook/src/NOTES.md:650-670`; `builds/lean/memos/stub0068-memo.md` (format + register model).

---

## 1. Verdict: **needs-build**

**Not flippable today.** Unlike 0054/0058/0068 — where the flip rode substrate that had *just
landed* — nothing relevant to 0075 has landed since the stub was written. All three of the
stub's blocker claims re-verify TRUE (§2). The proved content that exists (§3) is either
already taught by 0050 (axioms, RU, Gaussian closed forms) or is the *wrong measure*
(`worstCase` is the no-density-bound limit, not ES_α).

**But it is NOT research-gated.** The stub's own unblock steps (1)–(2) are finite-space
arithmetic: a Bernoulli-law VaR + the counterexample + the ES ladder. This is the smallest,
easiest build in the queue's history — no SDEs, no measure theory beyond `Finset` sums over
`stdSimplex ℝ ι`, strictly simpler than landed items 12–16. After it lands, 0075 flips
**full-with-scope-cut** on the §8 skeleton: the chapter's mathematical heart (Example 24.1 as
a theorem, the α-window, "eighty against four") becomes proved Lean, exactly the register of
the three recent flips. This matches the course's own classification: NOTES.md:666-668
"Remaining 9 stubs … all gated on NEW builds", and the registry row
(`model-coverage-map.md:135`): unblock path = "jump laws + risk-composition build".

---

## 2. Blocker audit — all three stub blockers still TRUE (re-verified this ask)

Stub status banner (`0075-var-detail-aggregation.md:3-8`) names three gaps:

1. **"Thm 24.4's worst-case representation needs a supremum over measures with densities
   bounded by 1/(1−α)" — TRUE.** `worstCase_isLUB`
   (`mathfin/MathFin/RiskMeasures/WorstCaseRisk.lean:92-95`) is the sup over the **entire**
   probability simplex `stdSimplex ℝ ι` (via `representingSet_worstCase` :78 = full simplex)
   — i.e. the distortion bound pushed to ∞, whose value is `maxᵢ(−Xᵢ)`, not ES_α. The
   density-ball constraint `0 ≤ Z ≤ 1/(1−α)`, `E[Z] = 1` appears nowhere; the RN/ess-sup layer
   the general statement needs is absent (grep: no `Measure-density-ball`, no `rnDeriv`
   usage anywhere in `RiskMeasures/`).
2. **"the stack's VaR is Gaussian-only" — TRUE.** `gaussianVaR`
   (`RiskMeasures/Gaussian.lean:42`, `μ + σ * z`) is the only VaR object in the clone; every
   other VaR/CVaR lemma (CoherentAxioms, RockafellarUryasev, Additivity, Examples.lean:60-70)
   is a Gaussian instance. Grep `Bernoulli|bernoulli` over `mathfin/MathFin/` → **zero hits**
   (Mathlib's Bernoulli never imported); `Binomial/Model.lean` is CRR option pricing, not
   loss laws. No quantile-of-a-general-law definition exists (`quantile` hits are all
   Gaussian-Φ contexts or Spectral.lean's doc comments).
3. **"elicitability scoring plus cross-desk aggregation have no home at all" — TRUE.** Grep
   `elicit|Expectile|expectile` over `mathfin/MathFin/` → zero. Grep
   `CVA|ExpectedExposure|netting|Netting` → zero. No scoring-function/argmin machinery, no
   exposure objects, no composition-of-ρ-over-subportfolios statement.

The stub's "What the stack has" list (`0075:30-39`) is accurate line-by-line (§9); its
path-to-unblock (1)–(4) (`0075:49-54`) is exactly right in ordering and remains the plan —
steps (1)+(2) are the build this memo names; (3) stays gated (general RN form) with a cheap
finite-law stretch; (4) stays gated.

---

## 3. Proved content inventory (what the flipped lesson stands on)

All names grep-verified at **mathfin HEAD** this ask (mathfin is its own compilation face for
`MathFin.*` modules — builds/lean files import MathFin, e.g. `builds/lean/heston_scratch.lean:2`
imports `MathFin.FixedIncome.VasicekBondPrice`; the AC-packaged-mathlib face rule applies to
*mathlib* names, and the mathlib names these files consume — `stdSimplex`, `Finset.sup'`,
`Finset.inf` — are exercised by already-compiling mathfin modules, so they exist at the pin).

### 3a. Def 24.1's four axioms — proved at Gaussian (0050's layer, cited not re-taught)

- `IsCoherentRisk` (structure, four fields) — `AcceptanceSet.lean:36`; consequences
  `rho_zero` :46, `convexOn` :51, `continuous` :58, `acceptance_closed` :63, `cone` :71,
  `convex_acceptance` :79.
- Gaussian instances: `gaussianVaR_translation` (`CoherentAxioms.lean:48`),
  `gaussianCVaR_translation` :53, `gaussianVaR_positiveHomogeneity` :59,
  `gaussianCVaR_positiveHomogeneity` :65, `gaussianVaR_monotone_mean` :71,
  `gaussianCVaR_monotone_mean` :79.

### 3b. §24.5's variance-covariance rung — the closed forms EXIST (this is proved §24.5 content)

- `gaussianVaR` (`Gaussian.lean:42`) + `gaussianVaR_affine` :51 + `gaussianVaR_standard` :64
  — VaR_α = μ + σz_α, the ladder's first-rung closed form (ch. p. 423, lines 296-313 of the
  extraction).
- **`gaussianCVaR_standard` (`Gaussian.lean:68`): CVaR = ϕ(z)/(1−α)** — exactly eq. §24.5's
  `ES_α = n(z_α)/(1−α)·σ` at μ=0, σ=1 (scaled by `gaussianCVaR_affine` :58). This is the
  proved ES-closed-form the flipped lesson's ladder section teaches.
- `gaussianCVaR_sub_VaR` (`Gaussian.lean:73`), `gaussianVaR_volatility_scaling` (:82, iid
  time aggregation), `gaussianVaR_additive_at_rho_one` (`Additivity.lean:35`),
  `gaussianCVaR_additive_at_rho_one` (:48).
- **`gaussianVaR_subadditive` (`CoherentAxioms.lean:102`) + `gaussianCVaR_subadditive` :114**
  (+ `joint_stdev_le` :88; packaged at `Examples.lean:60-70`) — the Gaussian case where VaR
  does *not* fail: the theorem-shaped contrast that sharpens Example 24.1 (chapter p. 419:
  "the standard reassurance — that it only fails for strange distributions — is not true";
  the Gaussian case is the converse contrast).
- RU layer (0050's, cross-linked): `ruObjective` (`RockafellarUryasev.lean:70`),
  `ruObjective_at_gaussianVaR` :166, `gaussianCVaR_le_ruObjective` :183,
  `gaussianCVaR_isLeast_ruObjective` :239, `gaussianCVaR_eq_VaR_plus_tail_term` :253.

### 3c. Thm 24.4's nearest neighbors — proved, but the wrong measure (context, not proof)

- `worstCase` (`WorstCaseRisk.lean:32`) = `Finset.univ.sup' … (fun i ↦ −X i)`;
  `le_worstCase` :36, `worstCase_le` :40, **`worstCase_isCoherent`** :44 (all four ADEH axioms
  by `Finset` case analysis — the finite-state template the new build imitates),
  `representingSet_worstCase` :78, **`worstCase_isLUB`** :92 — sup of `E^Q[−X]` over the full
  simplex. Honest reading for the lesson: this is the stress-test family's *unbounded*
  endpoint ("distort by as much as you like"), ES_α is the *bounded* member; the shape
  (coherent ⟺ sup of expectations) is proved, the bound is not.
- **`coherentRisk_isLUB`** (`AcceptanceSet.lean:108-140`, read in full this ask): the ADEH
  representation theorem at finite state — every coherent ρ is an IsLUB of expected losses
  over its representing set, proved by cone separation
  (`exists_separating_of_not_mem_cone`, `MathFin/Foundations/ConvexDuality.lean`). This is
  the chapter's "a coherent risk measure and a stress test are the same object" (p. 421,
  lines 241-243) at the abstract level — proved substrate for the section's framing.
- `spectralRiskFinite` (`Spectral.lean:56`) with `spectralRisk_translation` :60,
  `spectralRisk_mono` :72, `spectralRisk_convex_combination_normalized` :82,
  `spectralRisk_convex_combination` :92 — ES is the spectral measure with distortion
  φ ≡ 1/(1−α) on the tail; the finite weighted-sum layer exists, ES itself does not (doc
  comments :14-40 honestly scope it to finite quantile grids "at the current pin").
- `IsCoherentRisk.convexOn` (`AcceptanceSet.lean:51`) — Thm 24.5's "a supremum of linear
  functionals is convex" (p. 421, lines 228-239) in its abstract finite-state form:
  coherence packages subadditivity + homogeneity = convexity. Proved; the ES instance is not.

### 3d. Adjacent landed substrate the lesson can cite

- `mc_pricer.lean` (`builds/lean/mc_pricer.lean`, item 12, 488 lines, 8 theorems): SLLN
  consistency + CLT with identified variance — §24.5's full-revaluation-MC rung (nested
  simulation error bars) and §24.12's "one set of paths" requirement get their stack hook
  here (narrative anchor, not a VaR computation).
- `greeks_signs.lean` (item 3) — §24.6's report-as-Taylor-expansion content.
- `herfindahl` (`Concentration.lean:43`) + `herfindahl_nonneg` :47,
  `herfindahl_le_one_of_sum_le_one_of_nonneg` :55, `herfindahl_card_inv_le_of_sum_one` :72 —
  a concentration index with proved bounds; optional cross-link for §24.3's
  "concentration is free" remark (not required).

**Nothing here is new-to-the-course except 3c** (worstCase/ADEH-representation, never taught
by any lesson — 0050 only name-drops the file). The lesson's namesake content — Example
24.1's arithmetic, the α-window, Def 24.3's quantile average, the $4-vs-$80 atom contrast —
has **zero** proved substrate. Hence needs-build, not full-with-scope-cut.

---

## 4. The smallest honest build that unlocks the flip

**Module**: `builds/lean/discrete_var_scratch.lean`, compiled in the mathfin face
(`cd mathfin && lake env lean ../builds/lean/discrete_var_scratch.lean` — the recorded
pattern for MathFin-importing builds; cox_scratch followed exactly this path before
promotion). **Promotion target**: `mathfin/MathFin/RiskMeasures/DiscreteVaR.lean` (PR-ready;
RiskMeasures is already a root-imported folder). No mathfin source edits needed for the
scratch — it consumes `MathFin.RiskMeasures.AcceptanceSet`/`.WorstCaseRisk` for `stdSimplex`
style and `IsCoherentRisk`.

**Theorem list (all finite-space; no measurability, no RN, no integration beyond `Finset`
sums + at most an interval integral of a step function):**

1. `finiteVaR` (def) — `finiteVaR (q : ι → ℝ) (L : ι → ℝ) (α : ℝ) : ℝ :=
   sInf {x | ∑ i in Finset.univ.filter (fun i => L i ≤ x), q i ≥ α}` on `Fintype ι`,
   `q ∈ stdSimplex ℝ ι` as hypothesis or bundled. (Def 24.2 verbatim, ch. p. 419 line 107.)
2. `finiteVaR_eq_value_inf` — the inf over ℝ collapses to a `Finset.inf` over
   `Finset.image L univ` (the stub's "finite-space VaR is a Finset infimum", 0075:52-53).
   This attainment lemma is the workhorse for 3–6.
3. `vaR_one_bond` — the one-bond law (two states: loss 0 w.p. 24/25, loss 100 w.p. 1/25):
   `finiteVaR q L (19/20) = 0`. (Example 24.1 first half, p. 419 lines 115-121.)
4. `vaR_two_halves` — the split law (three lumped states: 0 w.p. 0.9216, 50 w.p. 0.0768,
   100 w.p. 0.0016): `finiteVaR q' L' (19/20) = 50`. (p. 419 lines 122-127; chapter's
   `P(exactly one) = 2×0.04×0.96 = 0.0768` is already lumped.)
5. **`vaR_subadditivity_fails`** — the headline: `¬ (finiteVaR q' (L'+L') (19/20) ≤
   finiteVaR q L (19/20) + finiteVaR q L (19/20))`, i.e. 50 > 0 + 0 as a *theorem*.
   (Example 24.1's "ρ(A) = ρ(B) = 0 but ρ(A+B) = 50", p. 419 line 129.)
6. `vaR_counterexample_window` — the chapter's exercise (p. 421, lines 244-248), **sharpened**:
   failure ⟺ `6912/10000 < α ≤ 24/25`. Note the right endpoint is *included* under Def
   24.2's `P(L ≤ x) ≥ α` convention (at α = 0.96: `P(L≤0) = 0.96 ≥ 0.96` keeps VaR_one = 0
   while VaR_two = 50 still); the chapter states the open interval — the Lean statement pins
   the endpoint and the flipped lesson should teach the discrepancy as an exercise. (Also
   excludes α = 0.9216: `P(L≤0) = 0.9216 ≥ 0.9216` collapses VaR_two to 0.)
7. `es_one_bond_eq_80` — Def 24.3 at the one-bond law: the quantile average
   `(1/(1−α))·∫_α^1 VaR_u du` (step function: 0 on [0.95, 0.96], 100 on (0.96, 1]) = 80.
   Encoding choice left to S-pass: interval integral of the step quantile function, or the
   equivalent finite tail sum; either way the *value theorem* is the deliverable.
   (Def 24.3 / eq. 24.1, p. 420 lines 153-179.)
8. `condExp_tail_eq_mean_one_bond` — `E[L | L ≥ VaR_α] = E[L] = 4` (the event is the whole
   space at an atom) — the "$4 against $80" contrast as proved Lean. (p. 420 lines 167-183.)

**Stretch (optional, only if cheap — not required for the flip):**
`es_sup_representation_finite` — Thm 24.4 at the two-state law: `sup over Z` with
`0 ≤ Z ≤ 20`, `E[Z] = 1` of `E[Z·L]` equals 80, by 2-state LP case analysis (Z* puts weight
20 on the default state, 0.2 on the survival state). Would upgrade the representation
section from fully-gated to proved-at-the-example. If it drags, gate it.

**Size estimate**: ≤ ~500 lines (compare: mc_pricer 488, hw_scratch 767). Every numeric
coefficient (`6912/10000`, `24/25`, `19/20`, `24/25` weights) is `norm_num` territory.

**What the build must NOT attempt** (scope fences to state in its header, mirroring
cox_scratch's fence block): the general bounded-density sup Thm 24.4 (needs RN/ess-sup —
absent at the pin); elicitability scoring (no argmin machinery); any CVA/exposure object
(grep-verified absent); cross-desk aggregation composition.

---

## 5. What stays gated after the build (the flipped lesson's honest boundary)

1. **Thm 24.4 in general** (p. 421 lines 184-227): sup over the density ball needs an
   essential-sup/RN layer not in `RiskMeasures/` at this pin. Nearest proved neighbors to
   cite honestly: `worstCase_isLUB` (no-bound endpoint), `coherentRisk_isLUB` (abstract
   ADEH at finite state), `spectralRiskFinite` (distortion layer). The chapter's pointwise
   `Z*` argument (lines 197-227) is teachable as chapter-sourced mathematics.
2. **Thm 24.5 as an ES theorem** (p. 421 lines 228-239): only the abstract convexity fact
   (`IsCoherentRisk.convexOn`) and the spectral convex-combination lemmas exist; "ES is
   coherent" itself is not instanceable. One-line shape, teachable chapter-sourced.
3. **Elicitability** (Def 24.9, eq. 24.5, p. 429-430 lines 669-738): no scoring-function
   machinery in any clone (grep-verified); the asymmetric-quantile score's minimization
   claim, the mixture-consistency obstruction, and Fissler–Ziegel joint elicitability are
   chapter-sourced. (References verified in the chapter's own list, lines 907-919:
   Gneiting 2011, Fissler–Ziegel 2016, Bellini et al. 2014.)
4. **Backtesting statistics** (§24.9 p. 428-429, lines 651-665): Binomial(n, 1−α) exception
   counts, traffic-light — no stats substrate; chapter-sourced.
5. **Calc 24.7 / Calc 24.8** (p. 425 lines 431-483; p. 426-427 lines 513-616): empirical
   numerics (184/69/38 bp, 93% unexplained, 0.98→0.22 vs flat 0.55, crossing ≈160). Desk
   content in the 0067 house pattern (chapter-sourced, cross-link 0049/0021/0062).
6. **§24.11 counterparty risk** (p. 431 lines 774-798): `CVA = LGD·∫EE(t)dP(τ≤t)` — no
   exposure/CVA object exists (grep-verified); cross-link the landed hazard layer
   (`hazardSurvival`, Cox density pricing from lesson 0068's substrate) for the `dP(τ≤t)`
   half only.
7. **§24.12 one-model-or-many** (p. 432-434 lines 813-905): architecture narrative —
   sensitivities-add-across-models, `EE(t)` max-doesn't-distribute, "a netted exposure is
   not a sum of exposures". No aggregation object to prove anything about; teach
   chapter-sourced (the scan's own verdict, ch24-scan.md:236-238).

---

## 6. Chapter anchors (ch24-risk-management.pdf; printed = PDF page, offset +0; extraction /tmp/ch24.txt)

- p. 419: **Def 24.2** VaR `inf{x : P(L ≤ x) ≥ α}` (lines 106-108); **Example 24.1**
  diversification punished — one bond `VaR₀.₉₅ = $0` (115-121), two halves
  `0.9216 < 0.95 ⟹ VaR = $50` (122-130); "the failure is not a curiosity" + jumps remark
  (136-146).
- p. 420: §24.4; **Def 24.3** + **eq. (24.1)** quantile average (153-166); **$4-vs-$80
  remark** — conditional form useless at atoms (167-183); **Thm 24.4** statement + **eq.
  (24.2)** density bound `0 ≤ Z ≤ 1/(1−α)` (184-191).
- p. 421: Thm 24.4 proof via `Z*` + the pointwise product argument (197-227); **Thm 24.5**
  + "a supremum of linear functionals is convex" (228-239); "a coherent risk measure and a
  stress test are the same object" (241-243); **α-window exercise** (244-248).
- p. 422: **Fig 24.1** split experiment — VaR jumps at the first split, ES falls to expected
  loss (285-290).
- p. 423: **§24.5 ladder** — variance-covariance closed forms `VaR = z_α·σ_L`,
  `ES = n(z_α)/(1−α)·σ_L` + delta-hedged blindness (296-321); historical simulation
  (323-331); full-revaluation MC (333-340).
- p. 424: **Def 24.6** first-order report; report-is-a-measurement-of-a-model (355-401);
  §24.7 + **eq. (24.3)** P&L explain (409-430).
- p. 425: **Calc 24.7** + **eq. (24.4)** unexplained-variance share, 1.2%/93%/100% table,
  "hedging is what breaks the explain" (431-483); explain-is-for-the-residual remark
  (494-502).
- p. 426-427: **Calc 24.8** three-sources table 0.98→0.22 vs flat 0.55, ratio 1.15→2.64,
  crossing ≈160 (513-546); Fig 24.2 (583+); "expected shortfall computed from a wrong delta
  is a coherent measure of the wrong thing" (per scan, §24.8).
- p. 428-429: §24.9 backtesting — Binomial(n, 1−α), 2.5 expected vs nine = 1-in-1000,
  traffic light (651-665); **Def 24.9** elicitable (669-674); **eq. (24.5)** asymmetric
  quantile score (677-685).
- p. 430: ES not elicitable — mixture consistency (695-702); (VaR, ES) jointly elicitable,
  Fissler–Ziegel (708-712); coherence-vs-elicitability trade (713-725); τ-expectile remark
  (726-738).
- p. 430-431: §24.10 PVA recipe, book-level reserve, "incoherent in exactly the way Value at
  Risk is" (761-772).
- p. 431: §24.11 `CVA = LGD·∫₀ᵀ EE(t) dP(τ≤t)`, vega-bearing, collateral (774-798).
- p. 432-434: §24.12 — internal arbitrage, marginals-vs-joint, sensitivities add ("the
  common language is the market, not the model"), `EE(t)` max doesn't distribute, the
  per-product + one-global-model architecture, consistency-is-not-correctness (813-905).

---

## 7. Section skeleton for the flipped lesson (each section names what it teaches)

**H1**: Lesson 0075 — VaR detail; risk aggregation · **Goal**: ch. 24 §24.3–24.12 beyond
0050 — Example 24.1 as a theorem, ES at atoms, what coherence needs, the computation ladder,
the one-model-or-many architecture; proved: discrete-law VaR/ES build + Gaussian closed
forms + the ADEH representation; gated: general Thm 24.4, elicitability, aggregation.

1. **Motivate** — risk puts back the measure pricing spent twelve chapters eliminating
   (§24.1, scan ch24-scan.md:4-7); 0050 owns the axioms/RU layer; this lesson owns the
   detail 0050 deferred ("two Bernoulli losses … an exercise-sized build", 0050:44-46 — now
   actually built).
2. **Establish A — Example 24.1 as a theorem.** Teaches **`finiteVaR`/`finiteVaR_eq_value_inf`**
   (mechanism) + **`vaR_one_bond`**, **`vaR_two_halves`**, **`vaR_subadditivity_fails`**
   (50 > 0 + 0). Contrast: **`gaussianVaR_subadditive`** (`CoherentAxioms.lean:102`) — the
   law where VaR does not fail; the failure is about jumps, not strangeness (p. 419).
   Optional hook: `herfindahl` (Concentration.lean:43) for "concentration is free".
3. **Establish B — the window (moving the quantile moves the verdict).** Teaches
   **`vaR_counterexample_window`** (failure ⟺ 0.9216 < α ≤ 0.96, endpoint sharpened vs the
   chapter's open interval — exercise material). Fig 24.1's jump (p. 422) as the picture.
4. **Establish C — eighty against four (Def 24.3 at atoms).** Teaches
   **`es_one_bond_eq_80`** + **`condExp_tail_eq_mean_one_bond`**; the conditional form is
   not imprecise but useless at atoms (p. 420).
5. **Establish D — the worst-case representation, honestly.** Thm 24.4 stated
   chapter-sourced with the Z* argument; proved neighbors: **`coherentRisk_isLUB`**
   (`AcceptanceSet.lean:108`, abstract ADEH = "same object, two ways"), **`worstCase_isLUB`**
   (`WorstCaseRisk.lean:92` = the unbounded-distortion endpoint), **`spectralRiskFinite`**
   (`Spectral.lean:56`, the distortion layer); Thm 24.5's convexity shape via
   **`IsCoherentRisk.convexOn`** (`AcceptanceSet.lean:51`). Gate: the bounded-density sup
   (general form) — plus the finite-law stretch if landed.
6. **Establish E — the computation ladder (§24.5).** Variance-covariance rung PROVED:
   **`gaussianVaR_affine`** + **`gaussianCVaR_standard`** (= ϕ(z)/(1−α), the chapter's
   closed form) + `gaussianCVaR_sub_VaR` + `gaussianVaR_volatility_scaling`; the
   delta-hedged-book blindness chapter-sourced (greeks_signs cross-link). Historical + MC
   rungs narrative; MC error bars anchored on mc_pricer's SLLN/CLT.
7. **Establish F — explain, attribution, architecture (§24.6-24.8, 24.12; chapter-sourced,
   0067 pattern).** Eq. (24.3)/(24.4); Calc 24.7's 93%; Calc 24.8's flat column;
   sensitivities-add-across-models vs EE(t)'s max-doesn't-distribute; "a netted exposure is
   not a sum of exposures"; the per-product + one-coarse-model architecture.
8. **Establish G — backtesting and elicitability (§24.9; chapter-sourced).** Def 24.9 +
   eq. (24.5); VaR elicitable / ES not / pair jointly (Fissler–Ziegel); coherence vs
   elicitability as properties of different roles; the expectile aside. Gate: no scoring
   machinery in the stack.
9. **Connect** — §24.10 PVA ↔ 0062's underdetermined parameters; §24.11 CVA ↔ 0068's
   hazard/`hazardSurvival` layer (the dP(τ≤t) half); §24.12 marginals-vs-joint ↔ 0070;
   ladder ↔ 0049; explain ↔ 0021; 0050 as the axiom layer this lesson completes.
10. **ask-your-tutor admonish** — e.g. "Ask why the two-bond VaR can be 50 while each half
    is 0 and what single number in Def 24.2 (the one quantile) is doing all the damage —
    then ask which α-values make the failure vanish and check against the proved window."
11. **Primary source** — ch. 24 PDF (pp. 417-434); `mathfin/MathFin/RiskMeasures/*`
    (esp. `WorstCaseRisk.lean`, `AcceptanceSet.lean`, `Gaussian.lean`, `CoherentAxioms.lean`,
    `Spectral.lean`); the new `RiskMeasures/DiscreteVaR.lean`;
    `builds/lean/discrete_var_scratch.lean`; Artzner et al. 1999, Acerbi–Tasche 2002,
    Fissler–Ziegel 2016 (chapter's reference list, PDF lines 907-919).
12. **Exercises + Answers** — (1) verify the α-window arithmetic from the proved theorem
    (retrieval of `vaR_counterexample_window`, incl. the endpoint convention); (2) compute
    ES and the conditional mean at the two-bond law and compare; (3) verbatim-name the
    Gaussian subadditivity lemma (`gaussianVaR_subadditive`); (4) why the variance-covariance
    method reports zero for a delta-hedged book, and which proved closed form the method
    rests on; (5) scope fence: state one §24.9 claim the stack cannot yet grade and name the
    missing theory (scoring functions/argmin).

Registry/SUMMARY in the flip's same edit: `model-coverage-map.md:135` blocker cell →
"jump-law VaR + ES ladder LANDED (DiscreteVaR); gated: bounded-density sup, elicitability,
aggregation"; ch24 row :79 similarly.

---

## 8. Stale references in the current stub text

**None.** Every stack claim in the stub re-verified TRUE at mathfin HEAD this ask:

| Stub location | Claim | Status |
|---|---|---|
| 0075:30-31 | `gaussianCVaR_isLeast_ruObjective`, `gaussianCVaR_eq_VaR_plus_tail_term` in `RockafellarUryasev.lean` | TRUE (:239, :253) |
| 0075:32-33 | `IsCoherentRisk`, `acceptance_closed`, `coherentRisk_isLUB` in `AcceptanceSet.lean` | TRUE (:36, :63, :108) |
| 0075:33-34 | `gaussianVaR_affine`, `gaussianCVaR_sub_VaR` in `Gaussian.lean` | TRUE (:51, :73) |
| 0075:34-35 | `gaussianVaR_subadditive` in `CoherentAxioms.lean` | TRUE (:102) |
| 0075:36-38 | `worstCase_isCoherent`, `worstCase_isLUB`, "sup representation at finite state, without density bounds" | TRUE (:44, :92; accurate characterization) |
| 0075:38-39 | "None of: Bernoulli/jump VaR, the ES quantile average, the bounded-density supremum, scoring functions, aggregation" | TRUE (greps §2) |
| 0075:49-54 | path-to-unblock (1)–(4) | still open; (1)+(2) = the build of §4 |

The stub is an accurate stub — it stays until the build lands, then the flip replaces it.

---

## 9. Verification record

Commands run this ask:

- `pdftotext resources/fixed-income-notes-chapters/ch24-risk-management.pdf /tmp/ch24.txt`
  (920 lines) + page-header spot checks (419 at line 89 … 434 at line 892).
- Declaration greps: all ten `mathfin/MathFin/RiskMeasures/*.lean`
  (`grep -n "^theorem\|^lemma\|^def\|…"` per file — outputs quoted in §3).
- Absence greps over `mathfin/MathFin/`: `elicit|Expectile|expectile|Bernoulli|bernoulli`
  → zero; `CVA|ExpectedExposure|expectedExposure|netting|Netting` → zero; `stdSimplex`
  → AcceptanceSet/WorstCaseRisk/ConvexDuality/AxiomAudit only.
- Read in full: `WorstCaseRisk.lean` (97 lines), `AcceptanceSet.lean:100-140`,
  lesson 0050, the stub, ch24-scan.md, QUEUE.md tail, NOTES.md:650-670,
  model-coverage-map rows :79/:135, stub0068-memo.md.
- Headers read: `mc_pricer.lean`, `heston_scratch.lean` (MathFin-import evidence),
  `Binomial/Model.lean` (CRR, not loss laws), `Examples.lean:60-70` (Gaussian VaR
  subadditivity packaging).

**Not run this ask** (reported as such): any `lake env lean` compile (E-pass is read-only;
the builder re-verifies on the compilation face as backstop per AGENTS.md
§Name-verification); `mdbook build` + `check_links.py` (no lesson edits made — the flip is
a later dispatch); the numeric LP check of the §4 stretch theorem (S-pass decision).
The arithmetic claims in §4 items 3–8 were verified by hand against the chapter's own
numbers (p. 419 lines 115-127, p. 420 lines 170-179, p. 421 lines 244-248), not by Lean.

**Verdict restated**: **needs-build**. Land `RiskMeasures/DiscreteVaR.lean` per §4
(eight theorems, ≤ ~500 lines, mathfin face), then flip 0075 full-with-scope-cut on the
§7 skeleton with the §5 gates quoted in the honest-boundary section.

# Memo — E-pass for flipping stub lesson 0069 (inflation is FX: YoY swaps)

**Date**: 2026-10-14. **Dispatcher**: build-queue stub-flip pass (post-0068; stub registry
12→9 per `edf5def`).
**Subject**: `mdbook/src/lessons/0069-inflation-yoy.md` (STUB; registered
`SUMMARY.md` Part X; registry row `model-coverage-map.md:133`).

**Read this ask**: the stub in full; `resources/fixed-income-notes-chapters/scans/ch17-scan.md`
in full; `pdftotext resources/fixed-income-notes-chapters/ch17-fx-quantos-inflation.pdf`
(extraction to `/tmp/ch17.txt` succeeded, 551 lines; printed page = PDF page, offset +0 —
p. 289 printed on PDF page 1, verified); lesson 0047 (`0047-quanto-adjustment.md`) in full;
memo `stub0068-memo.md` in full (register precedent); declaration greps and file reads
quoted below, all with explicit face.

---

## 1. Verdict: **needs-build**

Not `full-with-scope-cut`, and the reason is program-consistent: every flipped sibling
(0054: ForwardEqScratch stages 1–3; 0058: same + GyongyScratch; 0068: cox_scratch promoted
to `FixedIncome/Cox.lean`) flipped only **after the chapter's own core equations existed as
landed theorems**. For 0069 nothing chapter-level is landed: eq. (17.6), eq. (17.7), and
eq. (17.10) exist in no Lean file on any face (greps below). A flip today would have a
proved section made entirely of *generic* engines (`changeOfNumeraire`, MGF lemmas) with
every chapter equation on the gated side — a stub wearing a FULL hat.

But this is **not research-gated**: the blocker is one small mechanical build. The stub's
status banner ("no inflation substrate … the YoY convexity additionally needs a
two-Hull-White Gaussian bond-ratio expectation, absent from every clone") is true as an
absence statement and stale as an unblock assessment:

1. **The ZC half (eqs. 17.6/17.7) needs no new substrate at all.** The deterministic
   `changeOfNumeraire` (`MathFin/Foundations/Numeraire.lean:124`, AC build face) takes
   arbitrary positive real slots `NT BT B0 N0` and has **no** normalization or
   integrability hypothesis ("no integrability hypothesis is needed", docstring :119–121).
   Instantiating `NT := Pⁿ(0,T)` (an observable constant), `X := I_T`, and stating the
   Jarrow–Yildirim identification as an explicit hypothesis
   (`∫ I_T / B_T ∂Qⁿ = I_0 · Pʳ(0,T)`) gives eq. (17.6) in one line; eq. (17.7) is a
   rearrangement. The modeling content — "I_t Pʳ(t,T) is a nominal tradable" — is the
   hypothesis, honestly stated, not smuggled.
2. **The YoY Gaussian core (eq. 17.10) is `quantoForward_of_gaussian` one dimension up.**
   Every engine exists on the AC build face: the ρ-decomposition of a correlated driver
   into independent normals (`QuantoGrounding.lean:65–117`, a ~55-line proof of exactly
   this factorization for one asset + FX), the 1D Gaussian MGF
   `integral_exp_mul_gaussianReal_zero` (`MathFin/Foundations/BrownianMartingale.lean:49`,
   AC face: `∫ x, exp(α·x) ∂(gaussianReal 0 v) = exp(α²·v/2)`), the independence
   factorization `IndepFun.integral_mul_eq_mul_integral` (used at
   `QuantoGrounding.lean:101–104`), and the joint-Gaussian law API
   (`BivariateGaussianHyp` + `conditional_expectation_formula`,
   `MathFin/Foundations/BivariateGaussian.lean:34/:61`, AC face — including
   `indepFun_of_covariance_eq_zero`, used in its own proof at :97). The two-rate cross
   term `−BʳBⁿ·Cov` is the `a²/2` algebra of the quanto proof, doubled.
3. **What is genuinely absent and stays absent**: two-correlated-Hull-White *dynamics*
   (hw_scratch/hw_bootstrap/jamshidian are single-rate throughout — one κ, one σ, no
   correlation hypothesis anywhere; grep this ask, §8), the SDE-level derivation of
   eq. (17.9)'s δ-shift, and the three-parent decomposition of the forward-measure means.
   These are the gated boundary — they do not block the flip.

---

## 2. The smallest honest build that unlocks the flip

**`builds/lean/inflation_scratch.lean`** — est. 250–350 lines, one B-pass; compiled via
`cd AmericanPutConvexity && lake env lean ../builds/lean/inflation_scratch.lean`.

**B1 — `forwardIndex_eq` + `breakeven_eq` (eqs. 17.6/17.7).** Hypotheses: probability
measure `Qⁿ`; positive reals `Pⁿ₀T Pʳ₀T B_T I₀`; `I_T : Ω → ℝ`; the identification
hypothesis `∫ ω, I_T ω / B_T ∂Qⁿ = I₀ * Pʳ₀T` (index-linked bond priced on the real
curve — the postulate, explicit). Conclusion:
`∫ I_T ∂(numeraireMeasure Qⁿ BT (fun _ ↦ Pⁿ₀T) 1 Pⁿ₀T) = I₀ * Pʳ₀T / Pⁿ₀T`, i.e.
`𝔼^{Q^{n,T}}[I_T] = I_0 P^r(0,T)/P^n(0,T)`. Proof: `changeOfNumeraire`
(`Numeraire.lean:124`) + field algebra (~25–40 lines). Corollary `breakeven_eq`:
`(1+b)^T = Pʳ₀T/Pⁿ₀T` with `b` defined by the swap's fixed leg. Engine consumed from the
**transitively-proven** set (see face note below).

**B2 — `yoyRatioExp_gaussian` (eq. 17.10's Gaussian core).** Hypotheses mirroring
`quantoForward_of_gaussian` (`QuantoGrounding.lean:65`): independent standard normals
`Z₁ Z₂` (`HasLaw` + `Measurable` + `IndepFun`), reals `mⁿ mʳ Vⁿ Vʳ ρ Bⁿ Bʳ` with
`0 ≤ Vⁿ`, `0 ≤ Vʳ`, `ρ² ≤ 1`; define `yⁿ := mⁿ + √Vⁿ·Z₁`,
`yʳ := mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)`. Conclusion:
`∫ exp(Bⁿ·yⁿ − Bʳ·yʳ) ∂μ = exp(Bⁿ·mⁿ − Bʳ·mʳ + ½(Bⁿ²·Vⁿ + Bʳ²·Vʳ − 2·Bⁿ·Bʳ·ρ·√(Vⁿ·Vʳ)))`.
Proof: pointwise factorization into `exp(const)·exp(a·Z₁)·exp(b·Z₂)` with
`a = Bⁿ√Vⁿ − Bʳρ√Vʳ`, `b = −Bʳ√(1−ρ²)√Vʳ`; independence factorization; two MGF
applications (`integral_exp_mul_gaussianReal_zero`, `BrownianMartingale.lean:49`);
`a²`-algebra produces the cross term (the `QuantoGrounding.lean:75–117` pattern, messier
ring. ~120–180 lines). State the covariance form `C := ρ√(VⁿVʳ)` in a corollary.

**B3 — `yoyConvexity_eq` (eq. 17.10's exact chapter shape).** Compose B2 with the bond
reconstitution deterministics `Dⁱ = −½Bⁱ²Vⁱ` (chapter p. 295: reconstitution factor
`e^{Dʳ−Dⁿ−Bʳyʳ+Bⁿyⁿ}` over the naive ratio of forwards). Total exponent:
`(Dʳ−Dⁿ) + B2's exponent = Bⁿ·mⁿ − Bʳ·mʳ + Bⁿ²·Vⁿ − Bʳ·Bⁿ·C` — the real-variance halves
cancel, the nominal halves double. Carry the naive ratio
`Pʳ(0,T)Pⁿ(0,S)/(Pʳ(0,S)Pⁿ(0,T))` as an explicit multiplicative constant. Pure algebra on
B2 (~40 lines). Verified against the chapter: extraction lines 411–436 (the `Dᵢ`-cancel
sentence at :429–430 and eq. (17.10) at :433) — the algebra above reproduces the chapter's
exponent exactly.

**Optional B4 — `quanto_deleted`**: with `mʳ = mʳ_pure + Δ` (Δ the ρ_{rI}-piece as an
input), `Δ = 0` deletes exactly that piece of the exponent. One-line corollary of B3; if
skipped, the deletion statement stays prose-plus-algebra in the lesson (acceptable — the
means' provenance is gated anyway).

**Not in the build** (gated, §4): the conditional identity eq. (17.8) as a named lemma;
eq. (17.9)'s derivation; two-HW dynamics; the MC cross-check.

**Face note for the B-pass** (first-checkpoint duty): B1's engine chain
(`ForwardMeasure` → `Numeraire` → `ChangeOfMeasure`) is **transitively consumed by landed
builds** (`mc_pricer.lean`, `cms_scratch.lean` etc. import
`MathFin.FixedIncome.ForwardMeasure`; import greps this ask) — zero import risk. B2's MGF
engine `BrownianMartingale.lean` (imports `BrownianMotion.Gaussian.BrownianMotion`, the
BrownianMotion package — present in the AC package list) is source-verified on the AC face
but **not yet imported by any landed `builds/lean` file** (`grep -l
"QuantoGrounding\|BivariateGaussian\|BrownianMartingale\|GaussianGirsanov" builds/lean/*.lean`
→ empty), and `QuantoGrounding.olean`/`BivariateGaussian.olean` are not pre-cached in the
packaged copy's build dir (only `GarmanNormalForm` among the quanto-adjacent modules).
Their source is on the face and the package's own `AxiomAuditGen.lean:869` records
`MathFin.quantoForward_of_gaussian` as standard-three — but per the build-face rule the
builder re-verifies the import chain compiles before building on it. Fallback if the
`BrownianMartingale` chain is heavy: restate the 1D MGF locally from
`Mathlib.ProbabilityTheory` primitives, mirroring `QuantoGrounding.lean:50–57`'s private
`integral_exp_mul_stdNormal`. Do **not** route B2 through `heston_scratch.lean`'s
`expAffine2` (that is derivative/PDE calculus, not law/moments — wrong tool) or through
`BivariateGaussianHyp` (viable but a newer API than the QuantoGrounding precedent).

---

## 3. Proved content available today (lemma ↔ chapter equation)

All names grepped on the **AC build face**
(`AmericanPutConvexity/.lake/packages/`) first; line numbers are build-face lines.

**Numeraire/forward-measure layer (transitively proven on face via landed builds):**
- `changeOfNumeraire` (`MathFin/Foundations/Numeraire.lean:124`) — `N₀·𝔼^{Q^N}[X/N_T] =
  B₀·𝔼^Q[X/B_T]`, arbitrary positive real slots, no integrability hypothesis. **The engine
  of eq. (17.6)** (B1 instantiates it; today it grounds the lesson's §A prose).
- `numeraireMeasure` (`Numeraire.lean:86`) + `numeraireMeasure_isProbabilityMeasure`
  (:97, needs the normalization `∫ NT/BT = N0/B0` — the martingale-pricing property of the
  bond, a hypothesis at this layer).
- `forwardMeasure` (`MathFin/FixedIncome/ForwardMeasure.lean:65`),
  `forwardMeasure_price` (:83), `forwardMeasure_expected_spot` (:99) — the **constant-rate**
  T-forward instance (bond hardcoded `e^{−rT}`). The pattern behind eq. (17.6); the
  two-curve instance goes through `changeOfNumeraire` directly (see §7, stale item 3).
- `changeOfMeasure_setIntegral_eq` (`MathFin/Foundations/ChangeOfMeasure.lean:101`) — the
  Bayes engine.

**Dynamic numeraire layer (landed; grounds eq. (17.8)'s legitimacy statement):**
- `changeOfNumeraire_setIntegral_eq` (`Numeraire.lean:171`) — hypotheses: adapted positive
  numeraire processes `N B`, the normalization `t ↦ (B₀/N₀)(N_t/B_t)` a Q-martingale, and
  the discounted claim `t ↦ (B₀/N₀)(X_t/B_t)` a Q-martingale; conclusion: for `s ≤ t ≤ T`
  and `A ∈ 𝓕_s`, the `Q^N`-integrals of `X_t/N_t` and `X_s/N_s` over `A` agree. Read with
  `X_t := I_t·Pʳ(t,T)` (the index-linked bond) and `N := Pⁿ(·,T)`, this **is** the
  chapter's legitimacy for eq. (17.8)'s second line: "legitimate because
  `I_t Pʳ(t,T)/Pⁿ(t,T)` is a T-forward martingale" (p. 294, extraction :352–353). The
  conditional instance as a named lemma stays gated (§4.1) — but the lesson can teach the
  move on this landed anchor without overclaiming.

**Gaussian layer (source-verified on face; consumption note in §2):**
- `quantoForward` (`MathFin/BlackScholes/Dividends.lean:112`),
  `quanto_correction_factor` (:117) — Thm 17.4's `e^{−ρσ_Sσ_X T}` (lesson 0047's core).
- `quantoForward_of_gaussian` (`MathFin/BlackScholes/QuantoGrounding.lean:65`) — the
  ρ-decomposition density-weighted expectation; **the direct proof template for B2**; also
  the forward-level shadow of eq. (17.9)'s δ-shift (§4.2).
- `integral_exp_mul_gaussianReal_zero` (`MathFin/Foundations/BrownianMartingale.lean:49`)
  — the Gaussian MGF base stone (B2's engine).
- `BivariateGaussianHyp` (`MathFin/Foundations/BivariateGaussian.lean:34`) +
  `conditional_expectation_formula` (:61) — joint-Gaussian law API, alternative B2
  hypothesis shape.
- Esscher tilt: `gaussianReal_withDensity_esscher` (`MathFin/Foundations/
  GaussianGirsanov.lean:72`), `hasLaw_esscher_tilt` (:104) — "under
  `Q = P.withDensity(exp(c·W − c²/2))`, the same W has law N(c,1)": the **law-level
  shadow of eq. (17.9)**'s drift-shift-by-δ (a single driver; the correlation enters B2-style
  through which driver appears in the density).

**HW layer (single-rate; workspace builds, compiled on the AC face per the landing record):**
- `hwBondPrice_eq` (`builds/lean/hw_scratch.lean:533`) — `P(0,T) = 𝔼[e^{−∫r}] =
  exp(−mean + σ²V/2)`: the single-rate exponential-Gaussian moment whose two-rate
  generalization B2 performs at the ratio level.
- `hwBondPrice_affine` (`hw_scratch.lean:575`) — `P(0,T) = A(T)·e^{−B(T)r₀}`; the
  reconstitution-form anchor (the chapter's `Dⁱ, Bⁱ` live here in one-rate form).
- Calibration/fits: `hwCalibMean` (`hw_scratch.lean:681`), `hw_reprices_curve`
  (:788) — the "each model's own Hull–White fit term" parent, one-rate.
- `hwIntegratedRate_hasLaw_gaussian` (`hw_scratch.lean:319`) — the rate's Gaussian law.

**Convexity-phenomenon cross-links:**
- `cms_adjustment_nonneg` (`builds/lean/cms_scratch.lean:362`) — the CMS convexity (the
  "wrong date" sibling; eq. (17.8)'s remark lists futures and CMS as the same phenomenon).
- `mc_put_consistency` (`builds/lean/mc_pricer.lean:210`), `mc_put_clt` (:275) — the
  MC-consistency *pattern* (BS-payoff-shaped; the YoY MC stays gated, §4.5).

**Verified absences (greps this ask):** no `jarrow|inflation` object in `mathfin/` or
`builds/lean/` (only false hits: category-theory `inflationary`, a Jarrow–Turnbull
docstring at `MathFin/Bridges/SurvivalUnification.lean:18`); no two-rate/correlation
substrate in the HW files (all single κ, single σ); no price index, no real curve, no YoY
object anywhere.

---

## 4. What stays gated (the honest boundary, quoted anchors)

1. **Eq. (17.8)'s conditional identity as a named lemma.**
   `changeOfNumeraire_setIntegral_eq` (`Numeraire.lean:171`) lands the martingale
   legitimacy in set-integral form under explicit hypotheses (index-linked-bond
   discounted-price martingale = the identification; bond-numeraire normalization); the
   `E^{Q^T}[I_T | F_S] = I_S·Pʳ(S,T)/Pⁿ(S,T)` instance is not assembled. Teach eq. (17.8)
   as chapter math on the landed anchor; name the gap.
2. **Eq. (17.9)'s SDE-level δ-derivation.** The Itô product-rule drift-matching on
   `I·Pʳ` (chapter pp. 294–295) has no SDE-level home in the stack. Landed shadows:
   `hasLaw_esscher_tilt` (`GaussianGirsanov.lean:104`, single driver, law level) and
   `quantoForward_of_gaussian` (forward level). The full two-driver drift-shift theorem —
   and the "maturity drops out via Bʳ" attribution to the short rate — is gated.
3. **Two-Hull-White dynamics and the three-parent mean decomposition.** The means
   `mⁿ, mʳ` and covariance `C` in eq. (17.10) are *inputs* in B2/B3. Where they come from
   (each model's HW fit term; the quanto parent `−ρ_{rI}σ_rσ_I`; the forward-measure
   parent `−ρ_{nr}σ_nσ_r Bⁿ`; chapter p. 296) needs two correlated integrated rates —
   absent (`hw_scratch.lean:533/:575` are one-rate; the "each model carries its own κ, σ"
   structure has no shared-Brownian generalization). Teach the parents as
   chapter-sourced interpretation of the inputs.
4. **Ex 17.3's numbers** (−0.3/−1.8/−4.2/−8.8/−12.4 bp total, quanto part −0.3→−3.9 bp;
   pp. 296–297) — chapter data, no Lean (the program does not do floating-point
   numerics in Lean; consistent with every sibling).
5. **The independent-Monte-Carlo cross-check** (chapter p. 297 "Trusting this";
   `crosscurrency.rs`): the *culture* is teachable (and the chapter's own sign-error
   warning is a desk remark), but a YoY-stepping MC under (17.9) is not built —
   `mc_pricer.lean:210/:275` are BS-payoff-shaped. Gate with the pattern named.
6. **The breakeven-vs-expectation covariance identity** (`𝔼^T[I_T] = 𝔼^P[I_T] +
   Cov^P(M_T,I_T)/𝔼^P[M_T]`, p. 293) — a Bayes rearrangement on the numeraire density;
   teachable as chapter math on `numeraireMeasure`'s definition (:86), not a landed
   lemma. No fixed sign — the chapter's own point; do not "prove" a direction.
7. **Fig. 17.2 / the quanto-share-of-correction curve** — chapter figure; prose only.

---

## 5. Chapter anchors (ch17 PDF; printed page = PDF page, offset +0; /tmp/ch17.txt line refs)

- p. 293: §17.3 opens; FX↔inflation dictionary table (:234–249); Jarrow–Yildirim
  identification (:253–255); **Calc 17.5**, eq. (17.6) (:256–265), eq. (17.7) (:267–273);
  no-model remark + breakeven-not-expectation + kernel covariance, no fixed sign
  (:277–302).
- p. 294: **Ex 17.2** breakeven `b = e^{0.025}−1 = 2.53%`, 3 bp compounding-convention gap
  (:303–310); §17.4 opens; **Calc 17.6**, eq. (17.8) index cancels (:312–356); futures/CMS
  same-phenomenon remark (:357–364).
- p. 295: two-HW + lognormal index model setup (:370–372); **Calc 17.7** drift matching,
  `δ = −ρ_{rI}σ_rσ_I`, maturity drops out (:373–404); **eq. (17.9)** (:405–410).
- pp. 295–296: **Calc 17.8** reconstitution formula, `Dᵢ = −½Bᵢ²Vᵢ` cancels half of each
  variance, **eq. (17.10)** (:411–436); reading remark — three drifts, two parents,
  `ρ_{rI}=0` deletes the quanto term (:442–453).
- pp. 296–297: Fig. 17.2 (:455–490); **Ex 17.3** worth table (:492–516); "Trusting this"
  MC remark (:520–525).
- p. 297: §17.5 "a change of numeraire is a change of country" (:527–541).

Also verified: the stub's formulas match the chapter exactly — eq. (17.6)/(17.7)
(stub :12–14), eq. (17.8) (:16–18), `δ = −ρσσ` (:20), eq. (17.10)'s exponent
(:21–22), the bp table (:23), the ρ=0-deletion/MC remark (:24–26), Ex 17.2 (:55–57).

---

## 6. Section-by-section skeleton for the flipped lesson (after B1–B3 land)

**H1**: Lesson 0069 — Inflation is FX: year-on-year swaps · **Goal**: own ch. 17.3–17.4 —
the dictionary as postulate, the model-free ZC swap (eqs. 17.6/17.7) and the YoY
convexity closed form (eq. 17.10) as proved theorems; honestly gated: the conditional
step's named lemma, eq. (17.9)'s SDE derivation, two-HW dynamics, the numbers.

1. **Motivate.** Three markets, one adjustment `−ρσ₁σ₂`; a dozen bp at the long end,
   invisible without the identification; the breakeven routinely misdescribed as an
   expectation. Links: 0047 (the quanto half of this chapter), 0042 (two-curve objects).
2. **Establish A — the dictionary is a postulate; the ZC swap is bookkeeping (eqs.
   17.6/17.7).** Teaches **`forwardIndex_eq`/`breakeven_eq`** (B1) from
   **`changeOfNumeraire`** (`Numeraire.lean:124`); the identification stated as the
   hypothesis it is; Fisher equation; the static trade. The not-an-expectation discussion
   as chapter math on `numeraireMeasure`'s density (:86) — covariance with the pricing
   kernel, no fixed sign (gate item 6).
3. **Establish B — where the model comes back (eq. 17.8).** Conditioning kills the index:
   `𝔼^T[I_T/I_S] = 𝔼^T[Pʳ(S,T)/Pⁿ(S,T) · 1/I_S]`. Teaches the legitimacy on
   **`changeOfNumeraire_setIntegral_eq`** (`Numeraire.lean:171`) — the landed
   set-integral martingale statement with the index-linked bond in the claim slot; the
   named conditional instance gated (§4.1). Same-phenomenon cross-links: futures (0044),
   CMS (**`cms_adjustment_nonneg`**, `cms_scratch.lean:362`; 0058).
4. **Establish C — the Gaussian core (eq. 17.10).** Teaches
   **`yoyRatioExp_gaussian` + `yoyConvexity_eq`** (B2/B3), with
   **`quantoForward_of_gaussian`** (`QuantoGrounding.lean:65`) named as the one-dimension-down
   precedent and **`integral_exp_mul_gaussianReal_zero`**
   (`BrownianMartingale.lean:49`) as the MGF engine. The `Dᵢ`-cancellation read off the
   proof; the two parents; `ρ_{rI} = 0` deletes exactly the quanto input (algebra).
5. **Establish D — honest boundary.** (a) eq. (17.9)'s δ: anchors
   **`hasLaw_esscher_tilt`** (`GaussianGirsanov.lean:104`) + the quanto forward; SDE
   derivation gated. (b) where the means come from: three parents chapter-sourced;
   single-rate substrate named (**`hwBondPrice_eq`** `hw_scratch.lean:533`,
   **`hwBondPrice_affine`** :575, `hwCalibMean` :681); two-rate dynamics gated. (c) the
   numbers and the MC culture: chapter-sourced, MC pattern named
   (`mc_put_consistency`, `mc_pricer.lean:210`), YoY MC gated.
6. **Connect.** 0047 (Thm 17.4 — same `−ρσσ`, different seats), 0042 (breakeven as a
   two-curve object), 0044 (futures basis), 0058/`cms_adjustment_nonneg` (wrong-date
   convexity), 0063 (numeraire changes in the LMM drift); "a change of numeraire is a
   change of country" (§17.5) as the chapter's carry-away.
7. **ask-your-tutor admonish** (include; sibling register): e.g. "Ask what exactly goes
   wrong if you quote the YoY leg off the zero-curve breakevens: not an error message —
   a few bp of silent drift, negative at every tenor if `ρ_{rI} < 0`. Seeing why no
   static portfolio can pin eq. (17.8) is the lesson."
8. **Primary source**: ch. 17 PDF §17.3–17.5 (pp. 293–297);
   `MathFin/Foundations/Numeraire.lean`, `MathFin/Foundations/ChangeOfMeasure.lean`,
   `MathFin/FixedIncome/ForwardMeasure.lean`, `MathFin/BlackScholes/QuantoGrounding.lean`,
   `MathFin/Foundations/BrownianMartingale.lean`, `MathFin/Foundations/GaussianGirsanov.lean`;
   `builds/lean/inflation_scratch.lean` (B1–B3), `builds/lean/hw_scratch.lean`,
   `builds/lean/cms_scratch.lean`, `builds/lean/mc_pricer.lean`.
9. **Exercises + Answers** (carry the stub's Ex 17.2 attempt as Ex 1): sign/algebra drill
   on eq. (17.10) (which term dies when `σ_I → 0`?); which-lemma drills (eq. 17.6 →
   `forwardIndex_eq`/`changeOfNumeraire`; the martingale legitimacy →
   `changeOfNumeraire_setIntegral_eq`); the two-parents decomposition drill; a
   compounding-convention drill extending Ex 17.2 to 5y/30y; a scope-fence drill (name
   one thing the closed form takes as input that the stack cannot yet produce — the
   means under the two-HW model).

Same-edit discipline: flip edits the lesson file + the registry row
(`model-coverage-map.md:133`) + `NOTES.md` stub count, per AGENTS.md.

---

## 7. Stale references in the current stub text

| Stub location | Text | Status |
|---|---|---|
| :3–5 (status banner) | "BLOCKED — no inflation substrate in the stack … the YoY convexity additionally needs a two-Hull-White Gaussian bond-ratio expectation, absent from every clone" | Absence clauses re-verified TRUE; blocker framing **stale in strength** — the ZC half needs no new substrate (`changeOfNumeraire` `Numeraire.lean:124`, no normalization hypothesis needed), and the YoY core is a mechanical one-dimension-up extension of landed `quantoForward_of_gaussian` with every engine on the face (§1–2). Replace with needs-build + build spec. |
| :30–31 | "`BlackScholes/Quanto.lean` (re-export of `Dividends.lean`) — `quantoForward`, `quanto_correction_factor`" | **TRUE** (AC face: `Dividends.lean:112/:117`; re-export note `Quanto.lean:19`). Not stale. |
| :33–35 | "`QuantoGrounding.lean` — `quantoForward_of_gaussian` … exactly the expectation-of-a-lognormal computation eq. (17.10) needs, done once" | **TRUE and confirmed as the build path** — it is literally B2's proof template (`QuantoGrounding.lean:65–117`, AC face). |
| :36–37 | "`ForwardMeasure.lean` — `forwardMeasure_expected_spot`, the pattern behind eq. (17.6)" | Name TRUE (`ForwardMeasure.lean:99`, AC face). **Trap for the flip**: it is the *constant-rate* instance (bond hardcoded `e^{−rT}`, def :65); the two-curve eq. (17.6) instantiates the general `changeOfNumeraire` with `NT := Pⁿ(0,T)`, not this lemma as-is. Cite both; never present `forwardMeasure_expected_spot` as eq. (17.6)'s proof. |
| :38 | "Inflation itself, real curves, and the two-curve Gaussian machinery: none found" | First two TRUE (grep this ask). Third clause **misleading as written**: the general Gaussian/numeraire machinery exists on the face (§3); what is missing is the chapter-level instances + two-rate dynamics. Rewrite in the flip. |
| :44–46 | "a two-Hull-White bond-reconstitution and Gaussian-expectation layer that no clone contains — eq. (17.10)'s cross term … has no proved home" | TRUE for the theorem (re-verified), stale as unblock assessment — the layer is a ~300-line build, not a research gap (§2). |
| :50–53 | "Path to unblock (1)–(4)" | Shape correct (step 2 = B1, step 3 = B2/B3 — matching this memo's build); step 1 is a postulate-statement not a build item; step 4's numeric check is outside Lean scope (gated, chapter-sourced). Tighten to the §2 spec. |
| `model-coverage-map.md:133` | "no inflation substrate · generalize lesson 0047's quanto" | Update in the flip's same edit to: build-landed (`inflation_scratch` B1–B3), remaining gates = two-HW dynamics + eq. (17.9) SDE derivation. |

**Not stale**: everything else re-verified this ask — the chapter equation transcriptions
(§5), lesson 0047's existence and content (read in full; its build-plan item 3,
`0047:62–65`, already promises this lesson — cross-link it), `BlackScholes/Quanto.lean`
re-export, `GarmanNormalForm.lean` (not needed by 0069; it is 0047's eq. 17.4 layer).

---

## 8. Verification record

Commands run this ask (outputs quoted or summarized above):

- `pdftotext resources/fixed-income-notes-chapters/ch17-fx-quantos-inflation.pdf
  /tmp/ch17.txt` (551 lines) — chapter read in full; page-offset check (p. 289 on PDF
  page 1).
- Full reads: stub `0069-inflation-yoy.md`; `scans/ch17-scan.md`; lesson
  `0047-quanto-adjustment.md`; `memos/stub0068-memo.md` (register);
  `QuantoGrounding.lean` (mathfin working copy, in full).
- Build-face reads (`AmericanPutConvexity/.lake/packages/MathFin/MathFin/…`):
  `BlackScholes/QuantoGrounding.lean` (in full), `Foundations/Numeraire.lean` :95–175,
  `FixedIncome/ForwardMeasure.lean` :55–135, `Foundations/BivariateGaussian.lean` :1–120,
  `Foundations/GaussianGirsanov.lean` :100–133, `Foundations/BrownianMartingale.lean`
  :42–56.
- Declaration greps: `mathfin/MathFin/BlackScholes/` + `FixedIncome/` listings and
  `Dividends.lean`/`ForwardMeasure.lean` declarations (working copy), then **line-number
  re-greps on the AC face** for every cited name (`Dividends.lean:112/:117`,
  `ForwardMeasure.lean:65/:71/:83/:99`, `Numeraire.lean:86/:97/:124/:171`,
  `QuantoGrounding.lean:50/:65`, `BivariateGaussian.lean:34/:61`,
  `GaussianGirsanov.lean:72/:104`, `BrownianMartingale.lean:49`).
- Workspace-build reads: `hw_scratch.lean` declaration list + :496–592,
  `hw_bootstrap`/`jamshidian_scratch`/`cms_scratch`/`mc_pricer` declaration lists,
  `cms_scratch.lean:362–370`, `mc_pricer.lean:210–216`.
- Absence greps: `jarrow|inflation` over `mathfin/` + `builds/lean/` (false hits only);
  correlation-substrate negative over the HW files; `builds/lean/*.lean` landing
  inventory (38 files listed).
- Import-chain analysis: import lines of the six key build-face modules + landed-build
  import greps (`grep -l "MathFin" builds/lean/*.lean`, import lists, and
  `grep -l "QuantoGrounding\|BivariateGaussian\|BrownianMartingale\|GaussianGirsanov"
  builds/lean/*.lean` → empty) — establishing the transitive-consumption split in §2/§3.
- Olean checks: packaged MathFin build dir has `Numeraire.olean`,
  `ForwardMeasure.olean`, `GarmanNormalForm.olean`; **no** `QuantoGrounding.olean`,
  `BivariateGaussian.olean`; `integral_exp_mul_gaussianReal_zero` located in MathFin (not
  Mathlib) via olean+source grep — with the standing caveat (inherited from
  stub0068-memo §8) that the AC face materializes a partial mathlib source tree, so
  source-grep negatives there are not conclusive.

**Not run this ask** (reported as such): any `lake env lean` compilation (read-only
E-pass; the builder re-verifies on the compilation face as the backstop — first
checkpoint, per AGENTS.md's name-verification convention), `mdbook build` +
`check_links.py` (no book edit in this pass), and any Monte-Carlo/numeric run.

**Verdict restated**: **needs-build** — land `builds/lean/inflation_scratch.lean`
(B1 `forwardIndex_eq`/`breakeven_eq` from `changeOfNumeraire`; B2
`yoyRatioExp_gaussian` via the `quantoForward_of_gaussian` ρ-decomposition +
`integral_exp_mul_gaussianReal_zero`; B3 `yoyConvexity_eq` = eq. (17.10) exact shape;
B4 optional deletion corollary; ~250–350 lines, one B-pass), then flip 0069 to FULL on
the §6 skeleton with the §4 gates quoted in the honest-boundary section; apply the §7
registry corrections in the same edit.

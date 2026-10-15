# Stub 0072 E-pass memo — regimes; estimating vol/correlation (ch. 21)

**Date:** 2026-10-14 · **E-pass by:** flash-explorer (read-only) · **Verdict: NEEDS-BUILD**

One small, concrete Lean build (four Gaussian-sampling theorems, ~500–700 lines, one B-pass)
unlocks a **full-with-scope-cut** flip. This is cheaper than the unblock path recorded in
the stub and in `mdbook/src/reference/model-coverage-map.md:134` ("lesson 0040's Kalman
beachhead"): the stub's blocker list treated the whole statistical layer as absent, but the
**build face** (not the clones) already carries the log-likelihood-ratio definition, the
Gaussian pdf, the Gaussian mean/variance/moments, Jensen, and the static-Girsanov slice.
What is missing is the *computation*, not the substrate.

## 1. What was read / run (evidence base)

- Stub in full: `mdbook/src/lessons/0072-regimes-estimating-vol-corr.md` (68 lines).
- Scan ledger: `resources/fixed-income-notes-chapters/scans/ch21-scan.md` (277 lines).
- Chapter text: `pdftotext resources/fixed-income-notes-chapters/ch21-estimation-in-practice.pdf /tmp/ch21.txt` (1,366 lines; PDF page = printed page, offset +0). Read §21.3–§21.7 in full (lines 455–1340).
- Landed substrate: declaration greps of `builds/lean/{mc_pricer,heston_scratch,cox_scratch}.lean`; mathfin module greps in the workspace clone **and** the packaged build-face copy.
- Name verification per the build-face rule — every MathFin name below was checked in
  `AmericanPutConvexity/.lake/packages/MathFin/MathFin/` and every Mathlib name in
  `AmericanPutConvexity/.lake/packages/mathlib/` (packaged faces, this session).
- Negative greps (all this session): `kalman|marchenko|pastur|kullback|chi.?sq|inaccessible|particle` over `builds/lean/*.lean` → **no hits**; `entropy|kullback|relativeEntropy|rentropy` over build-face `MeasureTheory`+`Probability` → no Gaussian-KL theorem (the `llr` *definition* exists, the computation does not); `-i inaccessible` over build face → only false positives (FreeAlgebra, Name.lean, etc.); no realised-variance estimator anywhere.

## 2. Chapter content verified from the PDF (the five load-bearing formulas)

| Item | PDF anchor | Content |
|---|---|---|
| eq. 21.2, Calculation 21.3 | p. 360 (txt 518–536) | delay ≈ ln(1/α)/D observations, D = ½(r − 1 − ln r), r = σ²_high/σ²_low; table 15→30%: 9.4 vs 8.5, 15→25%: 16.3 vs 17.3, 15→18%: 97.9 vs 152.2; small-shift D ≈ (r−1)²/4 (txt 586) |
| §21.3 remarks | pp. 359–362 | regime = state not parameter; neither hidden under continuous observation; switch at a *totally inaccessible* stopping time; three sampling obstructions (noise, dependence, scale) txt 594–624 |
| §21.4 remark + Calculation 21.4 | pp. 362–363 (txt 670–735) | change of measure moves drift, never the diffusion coefficient; ⟨S⟩ pathwise so measure-invariant; drift error flat at σ/√T (0.158/0.155/0.159), volatility error "falls like √(2/n)" (3.64/1.12/0.36 %) |
| eq. 21.3, Calculation 21.5 | p. 365 (txt 821–848) | E[σ̂] = σ√(2/n)·Γ((n+1)/2)/Γ(n/2) ≈ σ(1 − 1/(4n)); 1.24 % low at n = 20 |
| eq. 21.4 | p. 365 (txt 851–865) | E[RV over n samples] = σ²T + 2nη²; bias linear in frequency; Calc 21.6 signature plot (txt 866–918); two-scale/kernel (Calc 21.7, txt 919–983) |
| eq. 21.5 | p. 368 (txt 1027–1043) | Marchenko–Pastur bulk [(1−√q)², (1+√q)²], q = p/n; two eigenvalues clear the edge on Treasuries |
| eq. 21.6, Calculation 21.10 | p. 371 (txt 1162–1210) | κ^Q = κ + λη, θ^Q = κθ/κ^Q, η unchanged; premium cannot sit in vol-of-vol |

## 3. Proved content inventory (all names verified in the packaged faces this session)

### (a) Landed anchors usable in the flipped lesson today

- `MeasureTheory.llr` — build face `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean:29` (`llr μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal`, with `llr_self`, `neg_llr`). The exact object eq. 21.2's D integrates.
- `gaussianPDFReal μ v x` (mean μ, **variance** v — definition read) — build face `Mathlib/Probability/Distributions/Gaussian/Real.lean:49`; `integral_id_gaussianReal` (`∫x = μ`, Real.lean:539), `variance_fun_id_gaussianReal` / `variance_id_gaussianReal` (`Var = v`, Real.lean:549/574).
- `ConvexOn.map_condExp_le` (Jensen) — build face `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:168` — the one-sided sqrt bias of eq. 21.3.
- `withDensity_rnDeriv` family — build face `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:203–247` — rnDeriv of density-vs-base, the step that makes the KL computation accessible.
- `MathFin.gaussian_esscher_pdf` — packaged `Foundations/GaussianGirsanov.lean:59`; `gaussianReal_withDensity_esscher` (:72, tilt shifts the mean, variance unchanged — the static "drift moves, σ doesn't"); `hasLaw_esscher_tilt` (:104); `hasLaw_sub_const` (:118). **This is the proved core of §21.4's division-of-labour remark, in the static one-observation slice.**
- `MathFin.GaussianMoments.integral_sq_gaussianReal` / `integral_pow4_gaussianReal` / `integral_pow6_gaussianReal` — packaged `Foundations/GaussianMoments.lean:33/44/64` — the sampling-theorem moments.
- `MathFin.BrownianQuadraticVariation.qv_equals_t` (packaged `Foundations/BrownianQuadraticVariation.lean:175`, L¹/equipartition form of [B,B]_t = t), `integral_sq_increment` (:67, E[(B_t−B_s)²] = t−s), `brownianQuadraticVariation_of_isPreBrownianReal` (:196) — the bracket ingredient behind "neither is hidden" and the σ²Δt in eq. 21.4.
- `MathFin.hasLaw_increment` — packaged `Foundations/WienerIntegral.lean` (⚠ workspace clone has it in `Foundations/GaussianMoments.lean` — face churn; the build imports the packaged location).
- `MathFin.vasicekIntegratedRate_hasLaw_gaussian` — packaged `FixedIncome/VasicekBondPrice.lean:206`; `meanReversionHalfLife` — packaged `FixedIncome/Vasicek.lean` (the bad-column's slow coefficient).
- `MathFin.conditional_expectation_formula` — packaged `Foundations/BivariateGaussian.lean:61` (Kalman seed, per lesson 0040).
- `MathFin.bs_discounted_isQMartingale` — packaged `Foundations/Girsanov.lean:61` (the measure-change mechanism).
- `builds/lean/mc_pricer.lean:210` `mc_put_consistency`, `:275` `mc_put_clt`, `:470` `mc_put_variance` — the landed estimator→consistency→CLT-error-bar pattern, the house template for a sampling theorem.
- `builds/lean/heston_scratch.lean:258` `hestonGenerator_expAffine2`, `:744` `hestonTransform_expectation_gated` — the single-measure affine layer under eq. 21.6 (its transform half; the measure change is NOT landed).

### (b) Missing computations — the build (see §4)

No landed Lean counterpart exists for **any** of eqs. 21.2–21.6 (grep of builds/lean + both faces, this session). The stub is right about that. But each of 21.2/21.3/21.4 is now a short computation on substrate (a) — that is what changed.

### (c) Absent substrate (stays gated, research-grade in Mathlib terms)

Marchenko–Pastur / random-matrix eigenvalue laws (no chi-squared distribution even — grep empty), Kalman/particle filters, sequential-detection (SPRT) optimality, totally inaccessible stopping times, 2D/pathwise Girsanov for the Heston premium, pathwise-QV measure-invariance.

## 4. The smallest honest build (what unlocks the flip)

**One new scratch file, `builds/lean/EstimationScratch.lean`, compiled against the
AmericanPutConvexity face** (`cd AmericanPutConvexity && lake env lean ../builds/lean/EstimationScratch.lean`),
~500–700 lines, no new Mathlib/MathFin dependencies beyond §3(a). Five theorems:

1. `kl_gaussianReal_var_ratio` — eq. 21.2's D: for `0 < v`, `0 < r`,
   `∫ x, llr (gaussianReal 0 (r•v)) (gaussianReal 0 v) x ∂(gaussianReal 0 (r•v)) = (r − 1 − log r)/2`.
   Route: `gaussianReal_of_var_ne_zero` (withDensity form) + `withDensity_rnDeriv` family →
   llr = log of the `gaussianPDFReal` ratio (a quadratic in x) → integrate termwise with
   `integral_id_gaussianReal` + `variance_id_gaussianReal`. MathFin pattern to imitate:
   `gaussian_esscher_pdf` (completing the square). Closest existing substrate: `llr` + `GaussianMoments`.
2. `kl_gaussianReal_small_shift` (optional, cheap) — D = (r−1)²/4 + o(1) as r → 1, via the
   second-order Taylor of `log` at 1 — the chapter's "halving the gap quadruples the delay".
3. `rvExpectation_withNoise` — eq. 21.4: for Gaussian increments with E[(ΔX_i)²] = σ²Δt and
   iid mean-zero noise ε_i of scale η, `E[Σᵢ (ΔX_i + ε_i − ε_{i−1})²] = σ²T + 2nη²`.
   Route: expectation linearity + expansion; E[(ΔX)²] via `integral_sq_increment`/
   `integral_sq_gaussianReal`; cross-terms vanish by independence/mean-zero.
4. `sqrtBias_oneSided` — eq. 21.3's sign: for the RV-based estimator σ̂ (of a nondegenerate
   Gaussian sample), `E[σ̂] < σ` via strict concavity of sqrt through
   `ConvexOn.map_condExp_le`. The exact Γ((n+1)/2)/Γ(n/2) constant stays gated (it is
   *buildable later*: build face has the Gamma half-integer apparatus, e.g.
   `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:39` — a medium follow-up, not research).
5. `drift_se_endpoint` — Calc 21.4's bad column: for X_t = μt + σB_t,
   `(X_T − X_0)/T` has law `gaussianReal μ (σ²·T)` (affine pushforward of `hasLaw_eval`),
   hence `Var[(X_T − X_0)/T] = σ²/T` and the se is independent of n — "the estimator sees
   only the endpoints".

B-pass per ROUTING.md; WIP-checkpoint rule applies (each theorem lands as it verifies).
This scale matches `cms_scratch`/`cox_scratch`, i.e. one dispatch.

## 5. Gated boundary after the build (what the flipped lesson must NOT claim)

1. **The delay law itself** (ln(1/α)/D as the *expected delay* of a sequential test) — SPRT asymptotics; only the D-ingredient (theorem 1) is proved. Taught as chapter arithmetic on proved D.
2. **The Bayesian regime-filter recursion** (predict/renormalise, posterior band) — needs lesson 0040's linear-Gaussian filter build; `conditional_expectation_formula` is the seed, nothing built.
3. **Totally inaccessible stopping times** — absent from the build face (the §21.3 remark is taught as chapter citation, ch. 2 reference).
4. **Marchenko–Pastur bulk (eq. 21.5), eigenvalue cleaning, Calc 21.8/21.9 numbers** — no RMT anywhere in the faces; taught chapter-only. (Also §21.6's correlation-form discussion links forward to 0063/0073 but proves nothing Lean-side.)
5. **Exact Γ-ratio constant in eq. 21.3** and the two-scale/realised-kernel theorems (Calc 21.7) — later builds on top of theorems 3–4.
6. **κ^Q = κ + λη as a measure change (eq. 21.6)** — `heston_scratch` is single-measure generator algebra; a 2D Girsanov does not exist. Teachable: the algebra κθ = κ^Qθ^Q, and η-invariance by the *static-slice analogy* (`gaussianReal_withDensity_esscher`); the Heston measure change is gated.
7. **Pathwise-QV measure-invariance (the deep §21.4 argument)** — `qv_equals_t` is an L¹ statement under a *fixed* measure; the pathwise a.s.-limit object and its absoluteness under equivalent measures are not built. The `brownian-motion` `QuadraticVariation.lean` anchor the stub cites is the Doob–Meyer `predQuadVariation` — measure-*dependent*, weaker than the stub implies (see §7).
8. **"n dependent observations ≠ n× information"** — no information-theoretic layer.

## 6. Chapter anchors for the flipped lesson

- §21.3 pp. 359–362: eq. 21.2 (p. 360), screening criterion, three obstructions, subtle-regime hedging cost.
- §21.4 pp. 362–364: Girsanov remark (p. 362–363), Calculation 21.4 table (p. 363), division of labour exact (p. 364).
- §21.5 pp. 364–368: four decisions; eq. 21.3 (p. 365); eq. 21.4 (p. 365); Calc 21.6 signature plot (p. 366); Calc 21.7 (p. 367).
- §21.6 pp. 368–370: Calc 21.8 (p. 368), eq. 21.5 (p. 368–369), three routes + Calc 21.9 (pp. 369–370).
- §21.7 p. 370–372 (fold-in per scan verdict): Calculation 21.10 / eq. 21.6 (p. 371) — cross-link 0022 (affine engine) and forward-link 0073.

## 7. Stale references in the current stub text (fix at flip)

1. **Wrong anchor characterization**: "the pathwise bracket ⟨S⟩ … `QuadraticVariation.lean`" (`brownian-motion/BrownianMotion/StochasticIntegral/QuadraticVariation.lean`) — that file defines `predQuadVariation`, the **Doob–Meyer predictable bracket** (defined *via a measure*; :32). The closer anchor is mathfin's `BrownianQuadraticVariation.qv_equals_t` — and even that is L¹-under-fixed-measure, not the pathwise object §21.4's invariance argument needs.
2. **Mis-quoted rate**: stub says volatility error "falls like $2/\sqrt n$"; the chapter says √(2/n) for the error (PDF p. 363) — as a standard error of σ̂ the honest form is 1/√(2n) (equivalently √(2/n) for the *variance* error). The scan-ledger shorthand "(∝ 2/√n)" propagated into the stub.
3. **"KL-rate detection … absent"** — absent as a *theorem*, but the `llr` definition + Gaussian pdf/moments have been sitting in the build face; the stub's grep covered the clones, not `AmericanPutConvexity/.lake/packages/` (the exact face-churn trap the AGENTS.md rule exists for). This staleness is what the verdict turns on.
4. **Single unblock path** ("Kalman beachhead first", stub lines 56–62 and registry row `model-coverage-map.md:134`) — correct as the *filter* unblock, but not the smallest unlock for this lesson: theorems 1–5 above carry §21.3's D-term and all of §21.5 + §21.4's drift column without any filter.

## 8. Section skeleton for the flipped lesson (each section names its lemma)

1. H1 + **Goal** + Motivate — a regime is a state, not a changing parameter.
2. **Establish: regimes and whether they can be caught (§21.3)** — teaches `kl_gaussianReal_var_ratio` (D = ½(r−1−ln r), eq. 21.2's denominator) + optional `kl_gaussianReal_small_shift` ((r−1)²/4); the bracket ingredient `qv_equals_t`/`integral_sq_increment` for "neither is hidden"; delay law and screening criterion as chapter arithmetic on proved D; filter recursion + inaccessibility gated.
3. **Establish: calibrating to prices and history at once (§21.4)** — teaches `gaussianReal_withDensity_esscher` + `hasLaw_esscher_tilt` + `bs_call_formula_of_physical`/`bs_discounted_isQMartingale` (static slice: drift moves, variance doesn't) + `drift_se_endpoint` (Calc 21.4's flat column); vol column's √(2/n) law stated at the rate, exact sampling theorem gated; pathwise invariance gated.
4. **Establish: estimating a volatility (§21.5)** — teaches `rvExpectation_withNoise` (eq. 21.4, bias linear in n) + `sqrtBias_oneSided` (eq. 21.3's sign; Γ constant gated); window/resolution decisions + signature plot as chapter numbers.
5. **Establish: estimating a correlation (§21.6)** — eq. 21.5 + Calc 21.8/21.9 chapter-cited (all Lean-side gated; no RMT); the ρ form as imposed structure (cross-link 0063's correlations, 0073).
6. **Fold-in: implied exceeds realised (§21.7)** — eq. 21.6's algebra + η-invariance by static-slice analogy (`heston_scratch` affine layer cited); 2D measure change gated; forward-link 0073.
7. **The gated boundary — stated plainly** (§5 above, 0068-style section).
8. **Connect** (0040 backward, 0022/0073 sideways, 0075 risk aggregation) → ask-your-tutor admonish → Primary source (ch. 21 PDF + the EstimationScratch file) → Exercises/Answers.

## 9. Verification log (commands actually run this session)

- `pdftotext resources/fixed-income-notes-chapters/ch21-estimation-in-practice.pdf /tmp/ch21.txt && wc -l` → 1,366 lines; §21.3–§21.7 read in full.
- Declaration greps: `mc_pricer.lean`, `heston_scratch.lean`, `cox_scratch.lean`; `grep -rn -l "kalman|marchenko|pastur|kullback|chi.?sq|inaccessible|particle" builds/lean --include=*.lean` → **exit 1, no files**.
- Build-face greps: entropy/KL (none), ChiSquared (none), inaccessible (false positives only), `gaussianPDFReal`/`llr`/`ConvexOn.map_condExp_le`/`withDensity_rnDeriv` family (found, paths in §3).
- 13 MathFin names + `meanReversionHalfLife` + `integral_pow6_gaussianReal` verified in the **packaged** face `AmericanPutConvexity/.lake/packages/MathFin/MathFin/`; `hazardSurvival_eq_exp` **not found** in the packaged face (Cox promotion not yet in the pinned MathFin rev — builds for 0072 must not import Cox).
- Not run: `lake env lean` on any new file (E-pass is read-only; the B-pass runs the compilation check per ROUTING.md), and `mdbook build` (no lesson edits made).

# E-pass memo — stub 0061 (LSV calibration circularity)

**Date:** 2026-10-14 · **E-pass:** flash-explorer (read-only) · **Lesson:**
`mdbook/src/lessons/0061-lsv-calibration-circularity.md` (STUB)
**Chapter:** Bagaria ch. 11, pp. 196–205
(`resources/fixed-income-notes-chapters/ch11-local-stochastic-volatility.pdf`,
pdftotext'd this session to /tmp/ch11.txt; split-file page = printed page, offset +0).

## VERDICT: needs-build — one small build (`lsv_scratch.lean`, est. 250–450 lines)
unlocks a **full-with-scope-cut** flip.

The proved core for *this chapter* does not exist yet: what is landed is generic
substrate (1-D Gyöngy coefficient functions, lognormal density, Mathlib condExp API)
from which the chapter's teachable core — the leverage-function form, the "L² comes
out" factoring, the pinned product, and Ex. 11.2's conditioning computation — is a
small, fully-specified build away. Without that build a flip would be an enhanced
survey (every Establish section either re-teaching 0058's Gyöngy content or
chapter-sourced prose), below the 0054/0058/0068 register, where each flip taught a
build-backed proved core for its own chapter. The chapter's theorem *content* (Thm
11.2's "reprices iff"), the McKean–Vlasov existence question, and all of §11.3's
calibration machinery stay gated regardless (research-grade cores + one buildable-but-
unbuilt substrate) — so the flip after the build is full-with-scope-cut, not full-now.

Why not still-stub: nothing here is research-blocked at the statement/algebra level.
The stub's own "path to unblock" item (3) already nominated an interim FULL
candidate ("Ex. 11.2 computable today") — it only picked the wrong engine (see
Stale references, item 3).

---

## 1. Proved content inventory (all grep-verified THIS session; face noted per item)

### 1a. Landed substrate the flipped lesson cites (taught elsewhere — cross-ref, don't re-teach)
| Landed name | Where | Chapter match |
|---|---|---|
| `Gyongy.exists_diffCoeffSq_fn` — `∃ b̂² : ℝ → ℝ` Borel with `diffCoeffSq 𝔜 X δ t ω = b̂²(X_t ω)` pointwise, i.e. `b²(t,x) = 𝔼[δ²|X=x]` as a genuine (t,x)-function | `builds/lean/GyongyScratch.lean:1242` | the `(t,K)`-section *shape* of eq. 11.1's `E[v_t|S_t=K]` (§11.2), read at `δ_t = L(t,S_t)√v_t` under the constructed-process hypotheses |
| `Gyongy.exists_driftCoeff_fn` | `GyongyScratch.lean:1210` | drift twin (context) |
| `Gyongy.marginal_flow_weak_equation_fn_constructed` — weak forward equation with `(t,x)`-form Borel coefficients | `GyongyScratch.lean:1281` | §11.2's proof step 1 (Gyöngy half) |
| `Gyongy.gyongy_mimicry_gated` — one-time-marginal mimicry **modulo named gate `hgate`** (flow uniqueness; Y carried as data) | `GyongyScratch.lean:1516` (docstring :1498–1500) | §11.2's proof step 1, with the gate list = this lesson's boundary; already quoted in 0058 (`0058-…:155–173`) and 0038 |
| `covariation_itoIntegralCLM_T` | AC face `AmericanPutConvexity/.lake/packages/MathFin/MathFin/Foundations/ItoIntegralCovariation.lean:72` (MathFin pin 784a831) | Def 11.1's `dW dZ = ρ dt` machinery |
| `hestonBracket_affine` (ρ appears in the 2-factor generator bracket) | `builds/lean/heston_scratch.lean:276` (item 19, zero sorry — the one `grep sorry` hit is the doc line "No `sorry`", :96) | Def 11.1 context: the landed correlated-2-factor generator algebra instance |
| `forward_eq_timeDependent_flux`, `forward_eq_convolution_timeDependent_flux` | `builds/lean/ForwardEqScratch.lean:1269,1310` | §11.3's grid discussion — shows what exists (1-d, t-only coefficients) and hence what does not (2-d, `(t,x)`) |

### 1b. AC-face anchors the build consumes (each grepped on `AmericanPutConvexity/.lake/packages/`)
| Anchor | Where | Role |
|---|---|---|
| `condExp_mul_of_stronglyMeasurable_right`: `μ[f*g | m] =ᵐ[μ] μ[f | m] * g` (g `[m]`-strongly-measurable, integrability on f, f*g) | AC-face mathlib `Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean:251` | **the "L² comes out" step** (§11.2's factoring sentence: "L²(t,S_t) comes out of the conditional expectation because … it is a deterministic function of the thing being conditioned on", PDF p. 197) |
| `StronglyMeasurable.exists_eq_measurable_comp` (Doob–Dynkin, `[Nonempty Z] [TopologicalSpace Z]`, Z := ℝ) | AC-face mathlib `Mathlib/MeasureTheory/Function/FactorsThrough.lean:57` | factorization of `E[v|σ(S)]` through S — the leverage function is a *function of K* (eq. 11.2). Pattern already executed privately at `GyongyScratch.lean:1186` (`exists_coeffFn_comp`, private — re-derive the 4-line public wrapper in the build) |
| `stronglyMeasurable_condExp` | AC-face mathlib `Mathlib/Probability/CondVar.lean:85` (usage site) | input to the Doob–Dynkin step |
| `lognormalTerminalPDF (S_0 r σ T K) = gaussianPDFReal 0 1 (bsd2 …) / (K·σ·√T)` | AC-face MathFin `MathFin/BlackScholes/BreedenLitzenberger.lean:66` | the coin-toss densities `φ_lo, φ_hi` (Ex. 11.2, p. 198) |
| `bsd2_eq`: `bsd2 = (log(S_0/K) + (r − σ²/2)T)/(σ√T)` | AC-face MathFin `MathFin/BlackScholes/Call.lean:110` | pins the density shape: at K = F, r = 0, T = 1, `φ_c(F) = exp(−σ_c²/8)/(F·σ_c·√(2π))` — the exact ATM inequality reduces to `ln(σ_lo/σ_hi) < 0 < (σ_hi²−σ_lo²)/8` |
| `Real.tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)` (+ `tendsto_comp_exp_atBot` :387) | AC-face mathlib `Mathlib/Analysis/SpecialFunctions/Exp.lean:230` | the wing-limit route: `log(φ_lo/φ_hi)` is a quadratic in `ln(K/F)` with negative leading coefficient → atBot → ratio → 0 → posterior on hi → 1 in BOTH wings (matches the PDF table's 0.98 at K=60 and 0.96 at K=160) |
| `conditional_expectation_formula` (bivariate Gaussian: `E[X|σ(Y)] = μ_X + (ρσ_X/σ_Y)(Y−μ_Y)` a.e.) | AC-face MathFin `MathFin/Foundations/BivariateGaussian.lean:61` | **teaching contrast only** (see Stale references item 3): the LINEAR conditional expectation a jointly-Gaussian (S,v) would give, vs. the true density-ratio posterior |

### 1c. What the build itself will prove (the flip's proved core — see §5)
The leverage-function form and everything algebraic downstream of the form (pinned
product eq. 11.6, extremes Ex. 11.1, λ-family mean-variance invariance, λ=0 endpoint
`L⁰² = 25/29` — exact rationals: 0.0725 = 29/400, 0.05 = 1/20), and Ex. 11.2's
conditioning content as exact inequalities (ATM posterior < 1/2; ATM leverage <
unconditional; wing limits; nonconstancy). Numbers: `√0.0725 ≈ 26.9%`, ATM posterior
≈ 0.297 ("0.30"), `L⁰ = (1/4)/√(29/400) ≈ 0.93` — I re-derived all three arithmetically
this session against the PDF's table (p. 198) and Calc 11.3 (p. 203); they agree. These
decimal figures stay chapter-sourced (not machine-checked reals).

## 2. Chapter anchors (PDF = printed page, split file)
- **Def 11.1** (p. 196): LSV SDE; division of labour (random `√v_t` carries dynamics, deterministic `L(t,S_t)` carries the fit).
- **Thm 11.2** (p. 197): reprices every European iff `L²(t,K)E[v_t|S_t=K] = σ_loc²(t,K)` (11.1); equivalently (11.2); proof = "Gyöngi's theorem ∩ Dupire's formula"; the factoring sentence quoted above.
- **Ex. 11.1** (pp. 197–198): `v ≡ 1 ⇒ L = σ_loc`; stochastic part already fits ⇒ `E[v|S=K] = σ_loc²`, `L ≡ 1` ("switches itself off").
- **Ex. 11.2** (p. 198): coin toss 15%/35%; `E[v] = ½(0.15²+0.35²) = 0.0725`, `√ = 26.9%`; posterior formula `E[v|S_T=K] = (v_lo φ_lo + v_hi φ_hi)/(φ_lo+φ_hi)`; table K = 60/80/100/125/160 → P(hi) = 0.98/0.51/0.30/0.51/0.96, `√E[v|K]` = 34.7/27.1/22.9/27.1/34.4%; "wrong by four volatility points at the money and eight in the wing, in opposite directions … a hundred times any bid-offer spread"; hump shape.
- **§11.3** (pp. 200–202): circularity ("L appears on both sides"); McKean–Vlasov remark ("not settled in general. Models are calibrated and traded anyway", p. 200); grid: `ψ(t,S,v)` 2-d Fokker–Planck, `E[v|S=K] = ∫vψ dv/∫ψ dv`, time-marching; particle method (Guyon–Henry-Labordère): Nadaraya–Watson (11.3), Gaussian kernel, `h_t ∝ σS_0√t N^{−1/5}`; grid-vs-cloud Structure; interacting particles (mean-field in the scheme); denominator cap/floor in sparse regions.
- **§11.4** (pp. 202–203): dial (11.4) `dv^λ = α dt + λβ dZ`; `L_λ` (11.5); pinned product (11.6) for every λ; endpoints λ=0 (pure local vol) / λ=1; **Calc 11.3** (p. 203): flat 25% surface, λ=0 → L flat 0.93 (= (1/4)/√(29/400), exact rational 25/29 squared), λ=1 → 1.09 ATM down to 0.71 wings ("measured"); "λ changes the answer, does not change the calibration, and therefore cannot be determined by it"; third-time pattern (β ch10 / stochastic part / λ); reserve doctrine.
- **Remark** (p. 204): forward smile as the λ-calibrator — cross-link to 0060 per the scan ledger.

## 3. Gated boundary (stays gated after the build; each gate named + located)
1. **Thm 11.2's iff-content** (that the leverage-defined model reprices the market). Needs four things, none landed:
   (a) `gyongy_mimicry_gated`'s `hgate` — flow uniqueness for merely-Borel coefficients (research-grade; item-11 verdict in QUEUE.md: "strong existence for merely-Borel coefficients false in general; Skorokhod/martingale-problem core absent from every clone");
   (b) Y-existence / weak solution for the local-vol side (research-grade, same item-11 verdict);
   (c) the **Dupire surface formula** on a non-Gaussian density carrier — buildable, per-family engine landed (`hasDerivAt_integral_mul_kernelFamily`; coverage-map row 9), genuine `(t,x)` forward equation rejected as hypothesis-echo in item 10 (`memos/item10-memo.md`);
   (d) existence of the LSV joint solution for a given `(σ_loc, v-part)` — the McKean–Vlasov/mean-field question, "not settled in general" (PDF p. 200); carried as data hypotheses at best.
   Note the sharpening: the *mimicry machinery* for S is the landed **1-D** layer (S alone is a real-valued Itô process with `δ_t = L(t,S_t)√v_t` w.r.t. W; the 2-factor origin of v enters only through the joint law inside the conditional expectation and through hypothesis (d)) — the stub's "multidimensional Gyöngy" framing overstates the machinery gap (see Stale references item 2).
2. **McKean–Vlasov / mean-field SDE theory**: absent from every clone — fresh grep this session (`grep -rli "McKean|meanField|mean_field"` over mathfin/MathFin, brownian-motion/src, AmericanPutConvexity: zero hits).
3. **§11.3 grid machinery** (2-d Fokker–Planck with `(t,S,v)`-coefficients): absent; even 1-d `(t,x)` coefficients are the item-10 gate (`ForwardEqScratch.lean` is t-only-coefficient; no `sorry`).
4. **§11.3 particle machinery** (Nadaraya–Watson estimator, kernel rates, empirical-measure convergence): absent — fresh grep (`Nadaraya|kernelRegression|particleMethod|empiricalMeasure`: zero hits). Waits for lesson 0040's statistics territory, as the stub says.
5. **Ex. 11.2's decimal table** (22.9%/26.9%/0.30/0.98/…): chapter-sourced, hand-verified arithmetically this session, not machine-checked; the build proves the exact inequalities, not the decimals.
6. **Calc 11.3's λ=1 figures** (1.09 → 0.71, "measured", p. 203): would need posterior evaluations at those strikes — out of the small build's scope; chapter-sourced.

## 4. Stale references in the current stub text (fix at flip)
1. **"the Dupire chain (lesson 0021, unbuilt)"** — lesson 0021 is BUILT/FULL (its H1 carries no `· STUB`; proved half = `breedenLitzenberger`, landed AC-face MathFin `BreedenLitzenberger.lean:74`). What is unbuilt is 0021's *build half* — the Dupire surface formula (coverage-map row 9). Also "Land lesson 0021's Dupire chain" in Path-to-unblock (1).
2. **"a *multidimensional* Gyöngy argument (lesson 0038's is one-dimensional)"** — overstated (see §3.1 note): the needed conditioning object `E[v_t|σ(S_t)]` is a condition-on-one-real-r.v. factorization — dimension-free via Doob–Dynkin — and the S-side mimicry is the landed 1-D layer with `δ = L√v`. The real gates are `hgate`, Y-existence, Dupire-surface, mean-field existence. (0039's triage table repeats the "multidimensional Gyöngy" phrasing — cross-check note for that lesson, not a blocker.)
3. **"`conditional_expectation_formula`, `linearShift` (BivariateGaussian.lean — the mixture machinery behind Ex. 11.2's coin-toss Bayes computation)"** — wrong engine. That theorem (AC-face `BivariateGaussian.lean:61`) is the LINEAR conditional expectation of a jointly-GAUSSIAN pair; Ex. 11.2's posterior is a ratio of lognormal densities — non-Gaussian, genuinely nonlinear. The scan ledger (ch11-scan.md line 113) repeats the claim. The right anchors: `lognormalTerminalPDF` + `bsd2_eq` + Mathlib condExp API (§1b). Keep `conditional_expectation_formula` only as the Gaussian contrast case.
4. **"Gyöngy 1-D via lesson 0038"** — understated since the stub was written: item 11 landed the constructed-process layer with `(t,x)`-form coefficients (§1a; 1,702 lines, zero sorry, V-passed per QUEUE.md item 11). 0061 should cite it (already taught in 0058/0038), not re-derive.
5. **Path-to-unblock item (3)** — "Ex. 11.2 by hand from `conditional_expectation_formula`": the candidate is real, the engine is wrong (item 3 above); corrected engine in §5.
6. Keep as-is: `covariation_itoIntegralCLM_T` (verified AC-face :72); "particle theory waits for lesson 0040" (matches §3.4); "McKean–Vlasov … none found" (re-confirmed fresh this session).

## 5. buildRequirement — the smallest honest build
**Module:** `builds/lean/lsv_scratch.lean`, compiled on the build face:
`cd AmericanPutConvexity && lake env lean ../builds/lean/lsv_scratch.lean`.
Imports: `Mathlib` + `MathFin.BlackScholes.BreedenLitzenberger` (brings `lognormalTerminalPDF`; `MathFin.BlackScholes.Call` for `bsd2_eq` is in that import tree — verify at first checkpoint). Zero `sorry`; `#print axioms` standard-three on every public theorem; WIP-checkpoint per lemma. Est. 250–450 lines, one B-pass (glm max).

Contract (names indicative; S-pass freezes them):
- **B1** `lsv_condExp_factors_through_state` — `{S v : Ω → ℝ}` (S measurable, v integrable): `∃ m : ℝ → ℝ, Measurable m ∧ ∀ ω, μ[v | comap S] ω = m (S ω)`. Engine: `stronglyMeasurable_condExp` + `exists_eq_measurable_comp` (FactorsThrough.lean:57); re-derive the wrapper — GyongyScratch's is private (:1186).
- **B2** `lsv_condExp_pullout` — `μ[L²(S)·v | comap S] =ᵐ[μ] μ[v | comap S] * L²(S)` via `condExp_mul_of_stronglyMeasurable_right` (PullOut.lean:251), L Borel, integrability hypotheses explicit.
- **B3** pinned product + extremes — for `m, σ_loc : ℝ → ℝ` positive: `(σ_loc/√m)² · m = σ_loc²`; `m ≡ 1 ⇒ L = σ_loc`; `m = σ_loc² ⇒ L = 1` (Ex. 11.1; eq. 11.6's per-λ form: family version with `m_λ`).
- **B4** coin-toss λ-family — `v_lo(λ) = 29/400 − λ/20`, `v_hi(λ) = 29/400 + λ/20`: `E[v^λ] = 29/400` for all λ; endpoint `L⁰² = σ_loc²/(29/400)`, instance `σ_loc = 1/4 ⇒ L⁰² = 25/29` (Calc 11.3's 0.93, exact).
- **B5** coin-toss leverage function — `φ_c = lognormalTerminalPDF F 0 σ_c 1`, `m(K) = (v_lo φ_lo K + v_hi φ_hi K)/(φ_lo K + φ_hi K)`:
  `cointoss_posterior_atm_lt_half` (`φ_hi F < φ_lo F` for `0 < σ_lo < σ_hi`, via `bsd2_eq` at K=F then `ln(σ_lo/σ_hi) < 0 < (σ_hi²−σ_lo²)/8` — exact, two lines);
  `cointoss_leverage_atm_lt_uncond` (`m F < (v_lo+v_hi)/2`, algebra);
  `cointoss_posterior_wing_limit_atTop` and `…_atZero` (posterior on hi → 1; `log(φ_lo/φ_hi)` = quadratic in `ln(K/F)` with negative leading coeff → atBot, then `Real.tendsto_exp_atBot`/`tendsto_comp_exp_atBot`, Exp.lean:230/:387);
  `cointoss_leverage_nonconstant` (wing limit vs ATM value).
- **STRETCH (gate it if it overruns):** `cointoss_condExp_characterization` — the posterior function composed with `S_T` **is** `E[v | σ(S_T)]` on the two-branch mixture measure (condExp characterization; branch-split integrals via a lognormal change of variables). Warning: `lognormalTerminalPDF_change_of_variables` exists in the mathfin WORKING clone but was NOT found on the AC face (784a831) this session — the density-pushforward engine must be re-verified (or grown as a house lemma) before this stretch is contracted; otherwise the interpretation stays chapter-sourced and only the analytic properties are proved. Do not let the stretch block B1–B5.

Closest existing substrate: `GyongyScratch.lean` (hypothesis shape + the private Doob–Dynkin wrapper to re-derive), `heston_scratch.lean` (correlated-generator precedent), `ForwardEqScratch.lean` (shows the density-side boundary), AC-face MathFin `BreedenLitzenberger.lean`/`Call.lean`/`BivariateGaussian.lean`/`ItoIntegralCovariation.lean`.

After landing: flip 0061 per the recorded pipeline (NOTES.md stub session: memo → scope cut → glm-max author + mdbook gate → orchestrator V-pass); update the model-coverage-map row 11 and the NOTES.md stub count (9 → 8); register nothing new in SUMMARY.md (0061 already at `SUMMARY.md:137`).

## 6. Checks run this session (and not run)
- pdftotext ch11 + read §11.1–11.4 in full (anchors §2). ✔
- Read the stub, ch11-scan.md, lessons 0021/0038/0039/0058/0068 (structure + gated boundaries), QUEUE.md, ROUTING.md (grep), NOTES.md stub-session section, coverage-map rows 9–11. ✔
- Grepped every name in §1a/§1b at its stated face; AC-face MathFin rev confirmed 784a831; mathfin working clone 4d82234 (QUEUE.md env map, matches). ✔
- Fresh absence greps: McKean–Vlasov/mean-field, Nadaraya/kernel-regression, particle/empirical-measure, 2-d Fokker–Planck — zero hits (ForwardEqScratch is the only Fokker hit, 1-d). ✔
- `grep -c sorry`: GyongyScratch 0, ForwardEqScratch 0, heston_scratch 1 (the doc line "No `sorry`" at :96 — no actual sorry; consistent with QUEUE item 19). ✔
- Arithmetic hand-checks of the PDF figures (26.9%, 0.297≈0.30, 22.9%, L⁰≈0.93 = 5/√29) — mine, by hand, not machine-checked. ✔
- **Not run:** `lake env lean` compilation of GyongyScratch/ForwardEqScratch this session (axiom-clean status taken from the recorded item-10/11 V-passes in QUEUE.md; the B-pass re-verifies at its first checkpoint per the standing rule). **Not run:** `mdbook build` (authoring-time gate, not an E-pass check).

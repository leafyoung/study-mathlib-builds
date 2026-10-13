# Item 10 memo — E-pass substrate sweep: Forward-eq stage 3 ((t, x)-dependent coefficients, full Dupire form)

E-pass (flash-explorer, read-only), 2026-10-13. Scope per ROUTING.md item-10 row:
sweep `builds/lean/ForwardEqScratch.lean` + lesson 0021 + chapter targets; hand the
coefficient-structure judgment to E'(glm). All names below are grep-verified in the
local clones on 2026-10-13; line numbers are current file states.

**Headline finding (dispatch correction, resolved):** the dispatch names Bagaria
ch21 as the formula source. Ch21 is "Estimation in Practice"
(`resources/fixed-income-notes-chapters/ch21-estimation-in-practice.pdf`; scan
`resources/fixed-income-notes-chapters/scans/ch21-scan.md` — filtering, regimes,
estimators; zero Fokker–Planck/Dupire theorems). The (t, x)-dependent forward
equation lives in **ch9** (`ch09-implied-and-local-volatility.pdf`, §9.4 eq. 9.2/9.3,
Thm 9.5/9.6/9.7), which lesson 0021 already cites. Not an ESCALATE trigger: the math
target is fully recovered from ch9's scan ledger + PDF text. Ch21 retains one
relevant anchor (see §2).

---

## 1. Name inventory (verified, file:line)

### 1a. `builds/lean/ForwardEqScratch.lean` (1,273 lines; items 7–8 landed)

Namespace `ForwardEqScratch`. Imports: `Mathlib`,
`MathFin.Foundations.FeynmanKacHeatEquation` (line 1–2). Public stage-1 names:

- `pden (μ σ x₀ t x : ℝ) : ℝ := heatKernel (σ ^ 2 * t) (x - (x₀ + μ * t))` — :162
- `pdenx (μ σ x₀ t x : ℝ) : ℝ := -(x - (x₀ + μ * t)) / (σ ^ 2 * t) * pden μ σ x₀ t x` — :166
- `pdenxx (μ σ x₀ t x : ℝ) : ℝ := pden μ σ x₀ t x * ((x - (x₀ + μ * t)) ^ 2 - σ ^ 2 * t) / (σ ^ 2 * t) ^ 2` — :171
- `hasDerivAt_pden_t {μ σ x₀ t x : ℝ} (ht : 0 < t) (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ pden μ σ x₀ s x)
      (-μ * pdenx μ σ x₀ t x + (σ ^ 2 / 2) * pdenxx μ σ x₀ t x) t` — :177
- `hasDerivAt_pden_x {μ σ x₀ t : ℝ} (x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    HasDerivAt (fun x' ↦ pden μ σ x₀ t x') (pdenx μ σ x₀ t x) x` — :195
- `hasDerivAt_pdenx_x {μ σ x₀ t : ℝ} (x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    HasDerivAt (fun x' ↦ pdenx μ σ x₀ t x') (pdenxx μ σ x₀ t x) x` — :203
- `forward_eq_constant_drift (μ σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    deriv (fun s ↦ pden μ σ x₀ s x) t
      = -μ * deriv (fun x' ↦ pden μ σ x₀ t x') x
        + (σ ^ 2 / 2) * deriv (deriv (fun x' ↦ pden μ σ x₀ t x')) x` — :229
- `forward_eq_driftless (σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) : …` (μ = 0 corollary) — :247
- `pden_zero_drift_eq_gaussianPDFReal … : pden 0 σ x₀ t x = gaussianPDFReal x₀ (σ ^ 2 * t).toNNReal x` — :256
- `convDen (μ σ x₀ : ℝ) (g : ℝ → ℝ) (a b t x : ℝ) : ℝ :=
    ∫ y in Set.Icc a b, g y * pden μ σ x₀ t (x - y) ∂volume` — :269
- `forward_eq_convolution (μ σ x₀ : ℝ) (g : ℝ → ℝ) (a b t x : ℝ) (ht : 0 < t)
    (hσ : 0 < σ) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    deriv (fun s ↦ convDen μ σ x₀ g a b s x) t
      = -μ * deriv (fun x' ↦ convDen μ σ x₀ g a b t x') x
        + (σ ^ 2 / 2) * deriv (deriv (fun x' ↦ convDen μ σ x₀ g a b t x')) x` — :661
  (the migration lemma; its proof consumes the private DCT chain below)

Public stage-2 names (time-dependent coefficients — the direct stage-3 predecessors):

- `pdenGen (m v : ℝ → ℝ) (t x : ℝ) : ℝ := heatKernel (v t) (x - m t)` — :705
- `pdenGenx (m v : ℝ → ℝ) (t x : ℝ) : ℝ := -(x - m t) / v t * pdenGen m v t x` — :709
- `pdenGenxx (m v : ℝ → ℝ) (t x : ℝ) : ℝ := pdenGen m v t x * ((x - m t) ^ 2 - v t) / (v t) ^ 2` — :714
- `hasDerivAt_pdenGen_x {m v : ℝ → ℝ} {t : ℝ} (x : ℝ) (hvt : 0 < v t) :
    HasDerivAt (fun x' ↦ pdenGen m v t x') (pdenGenx m v t x) x` — :720
- `hasDerivAt_pdenGenx_x {m v : ℝ → ℝ} {t : ℝ} (x : ℝ) (hvt : 0 < v t) :
    HasDerivAt (fun x' ↦ pdenGenx m v t x') (pdenGenxx m v t x) x` — :726
- `hasDerivAt_pdenGen_t {m v : ℝ → ℝ} {t x μ' σsq : ℝ}
    (hm : HasDerivAt m μ' t) (hv : HasDerivAt v σsq t) (hvt : 0 < v t) :
    HasDerivAt (fun s ↦ pdenGen m v s x)
      (-μ' * pdenGenx m v t x + (σsq / 2) * pdenGenxx m v t x) t` — :735
- `forward_eq_timeDependent (m v μ σ : ℝ → ℝ) (t x : ℝ)
    (hm : HasDerivAt m (μ t) t) (hv : HasDerivAt v (σ t ^ 2) t) (hvt : 0 < v t) :
    deriv (fun s ↦ pdenGen m v s x) t
      = -μ t * deriv (fun x' ↦ pdenGen m v t x') x
        + (σ t ^ 2 / 2) * deriv (deriv (fun x' ↦ pdenGen m v t x')) x` — :754
- `forward_eq_timeDependent_constant (μ σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) : …`
  (definitional stage-1 match; proof = `forward_eq_constant_drift`) — :773
- `convDenGen (m v : ℝ → ℝ) (g : ℝ → ℝ) (a b t x : ℝ) : ℝ :=
    ∫ y in Set.Icc a b, g y * pdenGen m v t (x - y) ∂volume` — :790
- `forward_eq_convolution_timeDependent (m v μ σ : ℝ → ℝ) (g : ℝ → ℝ) (a b t x : ℝ)
    (ht : 0 < t)
    (hm : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt m (μ s) s)
    (hv : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt v (σ s ^ 2) s)
    (hmc hμc hσc hvc : ContinuousOn _ (Icc (t / 2) (3 * t / 2)))
    (hvs : ∀ s ∈ Icc (t / 2) (3 * t / 2), 0 < v s)
    (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    deriv (fun s ↦ convDenGen m v g a b s x) t
      = -μ t * deriv (fun x' ↦ convDenGen m v g a b t x') x
        + (σ t ^ 2 / 2) * deriv (deriv (fun x' ↦ convDenGen m v g a b t x')) x` — :1210

Private machinery (NOT importable — see Conflict 4) — the migration/DCT engine a
stage-3 section would reuse by growing this file in place:

- `hasDerivAt_heatKernel_shift` / `_shift2` / `_shift0` / `_shift2_0` (kernel-shift
  argument derivatives) — :49, :73, :99, :109
- `heatKernel_heat` (∂_t K = ½ ∂²_y K, from the private FeynmanKacHeatEquation
  calculus re-derived through the public curve lemma) — :132
- stage 1: `continuous_pden_y/x/xx` (:274–286), `exists_pden_bound` (explicit
  constant domination on the rectangle s ∈ [t/2, 3t/2], z ∈ [x−1−b, x+1−a]) — :302,
  `integrable_base` — :424, `hasDerivAt_convDen_t/_x/_xx_core/_xx` — :445, :530,
  :588, :644
- stage 2: `continuous_pdenGen_z/x/xx` + `_y` variants — :795–819,
  `exists_cont_bound {f : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u) (hc : ContinuousOn f (Icc l u)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, l ≤ z → z ≤ u → |f z| ≤ C` — :824,
  `exists_pdenGen_bound (m v : ℝ → ℝ) (a b t x : ℝ) (ht : 0 < t)
    (hmc hvc : ContinuousOn _ (Icc (t/2) (3t/2))) (hvs : ∀ s ∈ …, 0 < v s) :
    ∃ C, 0 ≤ C ∧ ∀ s z, … |pdenGen|, |pdenGenx|, |pdenGenxx| ≤ C` — :838,
  `hasDerivAt_convDenGen_t` — :970, `hasDerivAt_convDenGen_x` — :1082,
  `hasDerivAt_convDenGen_xx_core` — :1136, `hasDerivAt_convDenGen_xx` — :1189

**Hypothesis pattern the existing machinery imposes** (what stage 3 must generalize):

1. Coefficients enter only through their **primitives** `m, v : ℝ → ℝ` (mean and
   variance curves); `μ t`/`σ t` are recovered as `m'`/`v'` via `HasDerivAt`
   hypotheses. There is no coefficient function of two variables anywhere.
2. Regularity actually used: `HasDerivAt m (μ t) t`, `HasDerivAt v (σ t²) t` at the
   point (pointwise form) or on the band `Icc (t/2) (3t/2)` (migration form);
   `ContinuousOn m/v/μ/σ` on the band; `0 < v s` on the band (uniform ellipticity).
   No measurability hypotheses at all — coefficients are deterministic.
3. Test function: `Continuous g` + global bound `|g y| ≤ Cg`; integration over
   `Set.Icc a b` with `a ≤ b`.
4. The domination constants (`exists_pden_bound` :302, `exists_pdenGen_bound` :838)
   exploit **Gaussian decay** of a known closed-form density (`exp ≤ 1`,
   `1/√v` monotone in `v ≥ v_min`). This is the step with no analogue once the
   density is not Gaussian.
5. Proof skeleton = chain rule on the Gaussian kernel
   (`hasDerivAt_heatKernel_comp`) + dominated convergence
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + `ring`-closing the
   coefficient algebra. For x-dependent coefficients the chain-rule half collapses:
   `K(v(t), x − m(t))` cannot represent a non-Gaussian density (see Conflict 3).

### 1b. MathFin substrate (`mathfin/` clone; working HEAD = b46e9b4, branch
`ito-drift-expectation` — NOT the pin 784a831; pin status per item 1c)

`MathFin/Foundations/FeynmanKacHeatEquation.lean` (in ForwardEqScratch's import set):

- `noncomputable def heatKernel (t y : ℝ) : ℝ :=
    (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (2 * t))` — :61 (public)
- `lemma hasFDerivAt_heatKernel {t₀ : ℝ} (ht₀ : 0 < t₀) (y₀ : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ ↦ heatKernel p.1 p.2)
      ((heatKernel t₀ y₀ * (y₀ ^ 2 - t₀) / (2 * t₀ ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (-(y₀ / t₀) * heatKernel t₀ y₀) • ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, y₀)` — :203
  (**the one genuinely-2D ingredient**; the precedent for any x-partial work — see
  Conflict 5)
- `lemma hasDerivAt_heatKernel_comp {v w : ℝ → ℝ} {τ₀ vd wd : ℝ}
    (hv : HasDerivAt v vd τ₀) (hw : HasDerivAt w wd τ₀) (hvpos : 0 < v τ₀) (z : ℝ) :
    HasDerivAt (fun s ↦ heatKernel (v s) (z - w s)) …` — :238 (the stage-1/2 engine)
- `heatKernel_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) : 0 ≤ heatKernel t y` — :268
- `integrable_heatKernel` — :273; `integrable_id_mul_heatKernel` — :299;
  `integrable_sq_mul_heatKernel` — :305; `continuous_heatKernel (s : ℝ)` — :367;
  `integrable_payoff_mul_heatKernel` — :429
- **x-domination toolkit (directly reusable for x-parameter differentiation):**
  `heatKernel_shift_le {t : ℝ} (ht : 0 < t) {x x₀ δ : ℝ} (hx : |x - x₀| < δ) (z : ℝ) :
    heatKernel t (z - x) ≤ Real.sqrt 2 * Real.exp (δ ^ 2 / (2 * t)) * heatKernel (2 * t) (z - x₀)`
  — :451 (docstring: "makes the `x`-derivatives' dominating function independent of
  `x` over `Metric.ball x₀ δ`"); `heatKernel_temporal_le` — :493;
  `heatKernel_loc_le {v₀ v x x₀ δ : ℝ} … : heatKernel v (z - x) ≤ … * heatKernel (3 * v₀) (z - x₀)`
  — :537
- **General kernel-family differentiation under the integral** (the machinery a
  stage-3 x-parameter derivative would consume):
  `theorem hasDerivAt_integral_mul_kernelFamily {h : ℝ → ℝ} (hhc : Continuous h)
    {φ φ' : ℝ → ℝ → ℝ} {p₀ r : ℝ} (hr : 0 < r) (hφc : ∀ p, Continuous (fun z ↦ φ p z))
    (hφ'c : Continuous (fun z ↦ φ' p₀ z)) (hpt : Integrable (fun z ↦ h z * φ p₀ z) volume)
    {bound : ℝ → ℝ} (hbi : Integrable bound volume)
    (hb : ∀ᵐ z ∂volume, ∀ p ∈ Metric.ball p₀ r, ‖h z * φ' p z‖ ≤ bound z)
    (hderiv : ∀ z, ∀ p ∈ Metric.ball p₀ r, HasDerivAt (fun p ↦ φ p z) (φ' p z) p) :
    HasDerivAt (fun p ↦ ∫ z, h z * φ p z ∂volume) (∫ z, h z * φ' p₀ z ∂volume) p₀` — :595
  (`p` is an abstract real parameter — it may be the *spatial* variable; this is the
  pin's closest thing to "differentiate an x-dependent integral family")
- `heatConvolution_eq_add_integral_deriv` (driftless FK identity,
  `∫ f·K = f 0 + ∫₀ᵗ ½∫ f″·K`) — :768; `feynmanU (g : ℝ → ℝ) (t x : ℝ)` — :828;
  `feynmanU_eq_integral_of_map` — :852; `feynmanU_eq_expectation` — :888
- Private in that file (re-derived, not importable): `hasDerivAt_heatKernel_y/_t/_y_y/_x/_x_x`
  — :73/:92/:156/:177/:187, `heatKernel_eq_gaussianPDFReal` — :65,
  `heatKernel_t_eq_half_y_y` — :259

`builds/lean/GyongyScratch.lean` (1,146 lines, item-5/6 landed; imports `Mathlib` +
`ItoContribution` — the AmericanPutConvexity clone build, :7–10). This is where the
**(t, x)-dependent coefficients already exist in proved form** — as conditional
expectations given σ(X_t), exactly the Thm 9.6 shape:

- `driftCoeff (μ : Measure Ω) (X β : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ := μ[β t | sigmaGen X t]` — :317
- `diffCoeffSq (μ : Measure Ω) (X δ : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
    μ[(fun ω => δ t ω * δ t ω) | sigmaGen X t]` — :321
- `tower_identity` — :358; `expectation_beta_eq_a` — :406;
  `expectation_deltaSq_eq_b2` — :416; `generatorIntegrand` — :437;
  `continuous_marginal_integrand` (proved DCT interchange) — :451;
  `time_derivative_marginals` — :620; `marginal_flow_weak_equation` — :645;
  `timeMeasure_Ioc_eq_interval` — :680
- Constructed instance (hitoid discharged, dispatches 10–12):
  `constructedBoundedItoProcess` — :781, `constructedGenIntegrandExp` — :835,
  `hitoid_constructed_terminal` — :924, `hitoid_constructed_band` — :972,
  **`marginal_flow_weak_equation_constructed`** — :1078 (the weak forward equation
  for the constructed process with the Gyöngy `(a, b²)` generator; consumes
  `hasDerivAt_marginal_flow_core` :539). All `#print axioms`-audited at :1129–1146.
  Caveat: this file lives under `builds/lean/`, not in the mathfin tree, and its
  import root `ItoContribution` is an AmericanPutConvexity-clone olean (Conflict 6).

`MathFin/Foundations/SDEExistence.lean`: Picard machinery exists but the coefficients
are **autonomous, state-only, Lipschitz**: `picardMap (hB) (T) (hBmeas) (hBcont)
{b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ) …`
— :82, contraction :95. No `(t, x)`-dependent coefficient SDE anywhere (grep for
dupire/localVol/fokker over all of `mathfin/MathFin/`: zero hits). Y-existence for
merely-measurable coefficients stays gated (GyongyScratch :203–205).

Lesson-0021 anchors (verified present): `MathFin/BlackScholes/BreedenLitzenberger.lean`
— `breedenLitzenberger` :78, `lognormalTerminalPDF_nonneg` :87,
`lognormalTerminalPDF_change_of_variables` :144. `MathFin/BlackScholes/PDEFromFeynmanKac.lean`
exists (`bsV_satisfies_bs_pde_via_feynmanKac` referenced at
`mathfin/MathFin/Blueprint.lean:257`).

### 1c. Pin-vs-HEAD status

- QUEUE.md "Pinned-rev environment map" (:13–23, grep-verified 2026-10-05): pin
  784a831 has the CLM/martingale family + driftPrim chain; **missing at pin**
  (workspace-HEAD only): `Foundations/Bisection.lean`, `Foundations/DerivOfDeriv.lean`,
  `Foundations/ProductMeasure.lean`, the `Probability/` dir.
- `FeynmanKacHeatEquation.lean` is **not** on the missing list, and items 7–8
  (DONE) already import it — treated pin-available (low-risk caveat: the local
  clone has since moved to b46e9b4; no git run per protocol).
- The mathlib4/ reference clone (`master`) carries every Mathlib name cited below.

### 1d. Mathlib names (mathlib4/ local clone)

- `theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀) …` —
  `Mathlib/Analysis/Calculus/ParametricIntegral.lean:286` (the measure-form
  ForwardEqScratch uses ~10×); interval version
  `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean:96`.
- `theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
  [l.IsCountablyGenerated] …` — `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:67`
  (the GyongyScratch DCT engine).
- `theorem IntervalIntegrable.ae_hasDerivAt_integral {f : ℝ → E} {a b : ℝ} …` —
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean:66`
  (endpoint differentiation only — exactly the trap lesson 0021:103–105 warns of);
  global form `LocallyIntegrable.ae_hasDerivAt_integral` — :38.
- `theorem contDiff_succ_iff_deriv …` — `Mathlib/Analysis/Calculus/ContDiff/Deriv.lean:92`
  (GyongyScratch's C²-route to a continuous f″).
- **`HasPartialDeriv` does NOT exist at this rev** (zero file hits) — any x-partial
  statement must route through `HasFDerivAt` on `ℝ × ℝ` (precedent:
  `hasFDerivAt_heatKernel`, FeynmanKacHeatEquation.lean:203) or nested
  `HasDerivAt`/`deriv ∘ deriv` chains (the ForwardEqScratch convention).
- **`integral_deriv_mul_derivWithin` does NOT exist at this rev** (zero hits in
  mathlib4/Mathlib) — lesson 0021's shopping-list name (:68) is stale. Conflict 2.

## 2. Lesson / chapter targets

**Lesson 0021** (`mdbook/src/lessons/0021-local-volatility-dupire.md`) — the
statements the build feeds:

- The formula: `σ²_loc(K,T) = (∂_T C + (r−q)K ∂_K C + qC) / (½ K² ∂²_K C)` — :45–49.
- The derivation step stage 3 underwrites: "Differentiate under the integral twice
  in K … and once in T (substituting the forward equation
  `∂_T φ = ½ ∂²_S[σ²_loc(S,T) S² φ]`); integrate by parts; solve" — :54–58.
- Shopping list + honest obstacles: smoothness/interiority hypotheses, forward
  Kolmogorov as prerequisite, Gyöngy Tier-3 — :62–78; research addendum (Thm 9.5 =
  eq. 9.4, Def 9.4, proof structure "differentiate in T, substitute the forward
  equation, integrate by parts twice"; coordinate-choice design note) — :86–119.
- Stale name in the shopping list: `integral_deriv_mul_derivWithin` :68 (Conflict 2).

**Lesson 0054** (`mdbook/src/lessons/0054-the-semigroup-and-the-adjoint.md`) — the
other fed lesson; records the stage-3 requirement verbatim: "Still open for the full
unblock: the (t, x)-dependent coefficients (full Dupire — flux-form PDE with
coefficients inside the derivatives, needing the Gyöngy
conditional-expectation coefficients)" — :70–73; path-to-unblock sequencing — :75–84.

**Bagaria ch9** (`resources/fixed-income-notes-chapters/ch09-implied-and-local-volatility.pdf`;
scan `resources/fixed-income-notes-chapters/scans/ch09-scan.md`) — the correct source:

- **eq. 9.2 (the stage-3 target statement)**: `∂p/∂T = −∂_S[(r−q)S p] +
  ½ ∂²_S[σ²_loc(T,S) S² p]` — "with the coefficients inside the derivatives rather
  than outside" (scan :23–25; PDF §9.4, pdftotext lines 339–362).
- eq. 9.3 (flux form): `∂_T p = −∂_S J`, `J = (r−q)S p − ½ ∂_S[σ²_loc S² p]`
  (scan :26–28; PDF pdftotext lines 364–382).
- Def 9.4 (local-vol model `dS = (r−q)S dt + σ_loc(t,S_t) S dW`) — scan :29–30.
- Thm 9.5 (Dupire, eq. 9.4; proof = differentiate C in T, substitute 9.2, IBP
  twice) — scan :31–33; PDF proof text pdftotext lines 424–439+.
- Thm 9.6 (Gyöngy: `a(t,x) = E[β_t | X_t=x]`, `b²(t,x) = E[δ_t² | X_t=x]`) —
  scan :42–45; Thm 9.7 (`σ²_loc(T,K) = E[σ_T² | S_T=K]`, eq. 9.7/9.8) — scan :46–48.
- Clone status: "Dupire's formula (9.4)/(9.5), Gyöngy mimicry, forward/flux
  equation … none found in mathfin/, brownian-motion/, mathlib4/,
  AmericanPutConvexity/" — scan :123–126 (consistent with my zero-hit grep).

**Bagaria ch21** (dispatch-named; actually "Estimation in Practice"):
no Fokker–Planck/Dupire theorem exists in the chapter (scan
`resources/fixed-income-notes-chapters/scans/ch21-scan.md` has no FP anchor in its
formula inventory :3–183). The single relevant anchor is the §21.2 "Two projections"
remark (PDF p. 358; pdftotext lines 404–410): `σ²_loc(t,x) = E[v_t | S_t = x]`
("conditioning on the current level and nothing else") — the Thm 9.7 restatement,
recorded in ch21-scan.md :57–62. Useful for the E'(glm) coefficient-judgment only as
a second citation of the same conditional-expectation coefficient object.

**NOTES.md stage-3 guidance** (`mdbook/src/NOTES.md:275–284`, stage-2 landing
report): "Remaining for full Dupire: (t, x)-dependent coefficients in flux form
(−∂_x(a_t p) + ½∂²_x(b_t² p)) with Gyöngy's condExp coefficients — stage-3 guidance
in the build report."

## 3. Candidate routes (through verified substrate only)

**Route A — weak-form full Dupire via the landed Gyöngy chain (recommended; the
only route where (t, x)-dependence is genuine and proved).**
Deliverable shape: the forward equation for the Gyöngy coefficients in
test-function form — d/dt E[f(X_t)] = E[f'(X_t)·a_t] + ½ E[f''(X_t)·b²_t] with
`a = driftCoeff`, `b² = diffCoeffSq` — is **already landed** as
`Gyongy.marginal_flow_weak_equation_constructed` (GyongyScratch.lean:1078, driven by
`hitoid_constructed_band` :972 and `hasDerivAt_marginal_flow_core` :539). Stage 3's
new content on this route: bridge the weak form to the density-side machinery of
ForwardEqScratch — i.e. for a test function g and the migrated object
u(t,x) = E[g(y)·p-form], prove d/dt ∫ g p = ∫ (a ∂g + ½ b² ∂²g) p
(integration-by-parts transfer of the generator, the flux-form reading of Thm 9.6's
engine; the pairing `tower_identity` :358 + `expectation_beta_eq_a` :406 +
`expectation_deltaSq_eq_b2` :416 is the IBP-free core that already exists).
Consumes: GyongyScratch :317, :321, :358, :406, :416, :451, :539, :972, :1078;
ForwardEqScratch public theorems :229, :661, :754, :1210. Blocker to flag for
E'(glm)/S: the *pointwise-in-x density* p(t, x) does not exist in the substrate for
non-Gaussian laws — Route A stays at expectation/test-function level unless a
density-existence hypothesis is carried (Route C's shape).

**Route B — flux-form migration lemma (divergence-form statement shape,
t-only coefficients).** Deliverable shape: extend `forward_eq_convolution_timeDependent`
(:1210) to divergence form: for u = convDenGen,
∂_t u = −∂_x(m'(t)·u) + ½ ∂²_x(v'(t)·u) — the *statement form* of eq. 9.2 with the
coefficients inside the derivatives. With t-only coefficients this is
algebraically equivalent to stage 2 (∂_x of a t-only coefficient is 0), so the proof
reuses the verified chain verbatim: `hasDerivAt_convDenGen_t` (:970, its conclusion
integral is exactly −μ(t)·∫g·pdenGenx + (σ²/2)·∫g·pdenGenxx), then product rule
with constant coefficients against `hasDerivAt_convDenGen_x` (:1082) /
`hasDerivAt_convDenGen_xx_core` (:1136) to identify ∂_x(μ(t)·u) = μ(t)·∂_x u.
This lands the "flux form" theorem class lesson 0054:70–73 names and gives the
S-pass the exact statement skeleton that a later genuine-(t,x) build would
generalize. Small build; zero new analytic inputs.

**Route C — hypothesis-carried classical forward equation with genuinely
(t, x)-dependent coefficients.** Deliverable shape: given u : ℝ → ℝ → ℝ with
declared `HasDerivAt`-in-t and `deriv ∘ deriv`-in-x data (the ForwardEqScratch
convention; no `HasPartialDeriv` exists — Conflict 5), and smooth bounded
coefficients `μ σ : ℝ → ℝ → ℝ` with `0 < σ` bounded below, state the divergence-form
equation ∂_t u = −∂_x(μ·u) + ½ ∂²_x(σ²·u) *as a hypothesis-carried equivalence*
and prove the migration lemma for it: u_conv(t,x) = ∫ g(y) u(t, x−y) dy satisfies
the same equation, by `hasDerivAt_integral_mul_kernelFamily`
(FeynmanKacHeatEquation.lean:595, parameter = x) + `heatKernel_shift_le` (:451) /
`heatKernel_loc_le` (:537) for the x-uniform domination. **Warning for E'(glm)/S:
without a construction of u the statement is in danger of being vacuous
(hypothesis-echo) — the tier2 name-binding lesson. The honest carriers of u are:
(i) the stage-2 Gaussian pdenGen (then σ collapses to t-only — Route B), or (ii) an
X_t-density that does not exist in the substrate (Conflict 3). This route is
statement-judgment territory and must not be name-bound at B without the E'(glm)
verdict on which generalization survives.**

## 4. Conflicts

1. **Dispatch chapter error (resolved):** ch21 has no (t,x)-forward-equation
   inventory; the target formulas are ch9 §9.4 eq. 9.2/9.3 + Thm 9.5/9.6/9.7
   (scan ledger `ch09-scan.md`:23–48). Ch21's only contribution is the Thm 9.7
   restatement at `ch21-scan.md`:57–62.
2. **Stale Mathlib name in lesson 0021:** `integral_deriv_mul_derivWithin`
   (lesson 0021:68) does not exist in mathlib4 at this rev (repo-wide grep, zero
   hits). The real parameter-differentiation lemmas are
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   (ParametricIntegral.lean:286) — which items 7–8 already use — and the
   endpoint-only `IntervalIntegrable.ae_hasDerivAt_integral`
   (LebesgueDifferentiationThm.lean:66), exactly the trap the lesson's own
   addendum (:103–105) flags.
3. **The full pointwise Dupire statement has no carrier in the substrate:** the
   only density objects in the program are Gaussian (`pden` :162, `pdenGen` :705 =
   shifted heat kernels); a (t,x)-dependent diffusion's density is not Gaussian,
   so stage 3's chain-rule proof skeleton cannot carry genuine x-dependence, and
   no density-existence machinery for non-Gaussian laws exists in any clone
   (ch9-scan :123–126; GyongyScratch gating note :203–205;
   `SDEExistence.picardMap` :82 takes autonomous `b σ : ℝ → ℝ` only). This is the
   known E'(glm) coefficient-judgment wall, pre-planned in ROUTING.md's item-10
   row — not a new blocker.
4. **Privacy of the migration engine:** every reusable stage-1/2 analytic piece
   (`exists_pden_bound` :302, `integrable_base` :424, `hasDerivAt_convDenGen_*`
   :970/:1082/:1136/:1189, `exists_cont_bound` :824) is `private` in
   ForwardEqScratch.lean. A stage-3 build importing the file gets only the public
   theorems (:229 … :1210). House pattern so far is to grow
   `ForwardEqScratch.lean` in place (stage 2 did exactly that); a new file would
   have to re-declare the private layer or the file must be grown.
5. **No partial-derivative operator at this rev:** `HasPartialDeriv` absent from
   mathlib4 (zero hits); x-derivatives must be stated as `deriv (fun x' ↦ …) x`
   chains (ForwardEqScratch convention) or `HasFDerivAt` on `ℝ × ℝ`
   (precedent `hasFDerivAt_heatKernel`, FeynmanKacHeatEquation.lean:203). Mixed
   (t,x) smoothness hypotheses for Route C must be built from these.
6. **Import-root split for Route A:** GyongyScratch.lean imports `ItoContribution`,
   whose olean is built inside the AmericanPutConvexity clone
   (GyongyScratch.lean:7–10); ForwardEqScratch.lean imports only Mathlib +
   FeynmanKacHeatEquation (:1–2). A stage-3 file consuming BOTH chains needs both
   roots in its lake environment — a build-env decision for the S-pass (the two
   scratch files do not import each other today).
7. **Pin caveat:** local mathfin/ is at b46e9b4 (branch ito-drift-expectation),
   not the pin 784a831; FeynmanKacHeatEquation.lean is not on the pin's missing
   list (QUEUE.md:19–23) and items 7–8 import it, so it is treated
   pin-available — but the S-pass should keep the import set identical to items
   7–8's (`Mathlib` + `MathFin.Foundations.FeynmanKacHeatEquation`) for Route B/C,
   and treat Route A as a builds/lean-scratch (AmericanPutConvexity-rooted) build
   if it consumes GyongyScratch.

## 5. Unknowns (escalation fodder, not failures)

- Whether ForwardEqScratch.lean still compiles at the *current* mathfin clone state
  (b46e9b4) — never run in this pass; last verified at the stage-2 landing
  (NOTES.md:275–280, 2026-10-04).
- AmericanPutConvexity/ItoContribution.lean internals not swept (6,700 lines —
  ROUTING.md context-ceiling clause). Route A's upstream names
  (`itoDrift_expectation_identity_adapted`, `mMeq_frozen`, `driftPrim`) are
  verified only at their GyongyScratch usage sites (:950, :1008, :767), not in the
  source file.
- Whether any non-Gaussian density-existence lemma exists in the brownian-motion/
  clone (not swept; ch21-scan :252–259 and ch9-scan :123–126 both record "none
  found" for adjacent machinery, which is strong but not a fresh sweep of this
  exact question).
- The stage-3 "build report" NOTES.md:283 points at was not located
  (no forward-eq section in builds/lean/README.md); the guidance content is fully
  recovered from NOTES.md:282–284 + lesson 0054:70–73.
- Ch21 remark page anchor: PDF p. 358 (pdftotext lines 404–410); the scan ledger
  records it without a page number.

**ESCALATE status: not triggered.** No unresolved name/signature conflicts were
found (Conflict 1 is a dispatch mis-reference resolved here; Conflict 2 is a stale
name with verified replacements). The stage-3 statement-selection wall (Conflict 3)
is the pre-planned E'(glm) coefficient-judgment handoff per ROUTING.md's item-10
route, and Route C's vacuity warning is the specific judgment call that pass must
make before the S-pass binds names.

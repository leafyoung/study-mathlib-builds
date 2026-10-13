import Mathlib
import MathFin.Foundations.StandardNormal
import MathFin.BlackScholes.Put
import MathFin.BlackScholes.LognormalMoments

/-!
# Tier-1 build I: the Monte Carlo pricer theorem (lesson 0023)

The estimator theorem every desk prices by: for an i.i.d. standard-normal ensemble
`Z : ℕ → Ω → ℝ` and the discounted European put payoff

  `H(z) = e^{-rT} · max(K − S_T(z), 0)`,   `S_T(z) = bsTerminal S₀ r σ T z` (MathFin),

this file proves the two statements of lesson 0023 end-to-end, zero `sorry`:

1. **Consistency (strong law).** `mcMean n := (1/n) · ∑_{i<n} H(Z i)` converges
   almost surely to `𝔼[H]` — and `𝔼[H]` is, by MathFin's `bs_put_formula`, exactly
   the Black–Scholes put price `K·e^{-rT}·Φ(−d₂) − S₀·Φ(−d₁)`. The law used is
   Mathlib's Etemadi strong law `strong_law_ae_real`: it needs only **pairwise**
   independence (so antithetic-pair samplers keep consistency).
2. **Error bars (CLT).** `√n · (mcMean n − P) ⇒ 𝓝(0, σ_H²)` in distribution via
   Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`, with the limit variance
   **identified in closed form**: `σ_H² = e^{-2rT}·M₂ − P²` where

     `M₂ = K²·Φ(−d₂) − 2·K·S₀·e^{μ+ν²/2}·Φ(−d₁) + S₀²·e^{2μ+2ν²}·Φ(−d₁−ν)`,

   `μ = (r − σ²/2)T`, `ν = σ√T` — the truncated (squared) second moment of the
   lognormal, computed from MathFin's completing-the-square primitive
   `integral_exp_mul_gaussianPDFReal_Iic` (the same atom `Put.lean` prices with).

Substrate consumed (grep-verified at the pin):
* Mathlib `Probability/StrongLaw.lean`: `strong_law_ae_real` (Etemadi pairwise).
* Mathlib `Probability/CentralLimitTheorem.lean`: `tendstoInDistribution_inv_sqrt_mul_sum_sub`.
* Mathlib `LpSeminorm/Basic.lean`: `MemLp.of_bound`; `Moments/Variance.lean`: `variance_eq_sub`;
  `L2Space.lean`: `memLp_two_iff_integrable_sq_norm` (the unbounded-payoff L² bridge).
* Mathlib `Probability/Distributions/Gaussian/Real.lean`: `integrable_exp_mul_gaussianReal`
  (the Gaussian L¹ fact that replaces boundedness for the call);
  `integral_gaussianReal_eq_integral_smul`; `integrable_map_measure`; `integrable_congr`.
* Mathlib `Probability/HasLaw.lean`: `HasLaw.comp`, `HasLaw.identDistrib`, `iIndepFun.hasLaw_pi`
  (the joint-vector bridge powering the multi-D seed); `Measure.pi`
  (`Mathlib/MeasureTheory/Constructions/Pi.lean`) for `multiGauss`.
* MathFin `Foundations/StandardNormal.lean`: `Phi`, `setIntegral_gaussianPDFReal_eq_toReal`,
  `integral_exp_mul_gaussianPDFReal_Ioi`, `integral_exp_mul_gaussianPDFReal_univ`,
  `gaussianReal_Ioi_toReal`.
* MathFin `BlackScholes/Call.lean`: `BSCallHyp`, `bsTerminal`, `bsTerminal_gt_K_iff`,
  `bs_call_formula` (the expectation-form call bridge).
* MathFin `BlackScholes/Put.lean`: `bs_put_formula` (the expectation-form put bridge),
  `integral_exp_mul_gaussianPDFReal_Iic`.
* MathFin `BlackScholes/LognormalMoments.lean`: `secondMoment_terminal`,
  `variance_terminal` (the terminal-price moment layer, composed as cross-checks).

The **call-variant layer** (second half of this file): the call payoff
`C(z) = e^{-rT}·max(S_T(z) − K, 0)` is UNBOUNDED, so the put's constant-bound routes
are replaced by (i) integrability via domination `0 ≤ C ≤ e^{-rT}·S_T` with the
discounted-forward identity `E[e^{-rT}·S_T] = S_0` (`integral_discountedTerminal_eq`),
(ii) L² membership via `memLp_two_iff_integrable_sq_norm` + domination of the square,
(iii) the closed-form second moment from the `Ioi` completing-the-square atom
`integral_exp_mul_gaussianPDFReal_Ioi` (the call's exercise region `{z > −d₂}` is a
right tail). A **multi-D seed** closes the file: `multiGauss d` (Mathlib `Measure.pi`
product of standard normals), the joint bridge `multiGauss_hasLaw_joint`
(`iIndepFun.hasLaw_pi` — d independent scalars ARE one Gaussian vector), and
`multiD_consistency` — the Etemadi strong law for i.i.d. vector draws and any
measurable integrable payoff of the whole vector.

Honest scoping (per lesson 0023 "what the build deliberately excludes"): the i.i.d.
ensemble is taken as the hypothesis bundle `iIndepFun Z μ` + `∀ i, HasLaw (Z i)
(gaussianReal 0 1) μ` — the countable-product *construction* lives in
MathFin's (broken-at-this-pin) `Probability.ProductMeasure` and is out of scope
(the multi-D seed uses Mathlib's `Measure.pi`, which is alive at the pin).
Variance reduction and multi-D closed forms are future layers.
-/

open MeasureTheory ProbabilityTheory Real MathFin Filter Function
open scoped NNReal ENNReal Topology

/-! ### The payoff: definition, pointwise bound, measurability -/

/-- The discounted European put payoff as a function of the standard-normal draw:
`H(z) = e^{-rT} · max(K − S_T(z), 0)` with the MathFin terminal map
`S_T(z) = S₀ · exp((r − σ²/2)T + σ√T·z)`. -/
noncomputable def mcPayoff (S_0 K r σ T z : ℝ) : ℝ :=
  Real.exp (-r * T) * max (K - bsTerminal S_0 r σ T z) 0

/-- The terminal map is nonnegative (it is `S₀ · exp(·)`). -/
lemma bsTerminal_nonneg (hS_0 : 0 ≤ S_0) (r σ T z : ℝ) :
    0 ≤ bsTerminal S_0 r σ T z := by
  unfold bsTerminal
  exact mul_nonneg hS_0 (Real.exp_pos _).le

/-- The discounted put payoff is nonnegative. -/
lemma mcPayoff_nonneg (S_0 K r σ T z : ℝ) : 0 ≤ mcPayoff S_0 K r σ T z := by
  unfold mcPayoff
  exact mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

/-- **The put payoff is bounded above** by the discounted strike: `H ≤ e^{-rT}·K`.
This boundedness (a put is the easy case of integrability, per lesson 0023's
boundedness audit) is what licenses the strong law and the CLT. -/
lemma mcPayoff_le (hS_0 : 0 < S_0) (hK : 0 ≤ K) (r σ T z : ℝ) :
    mcPayoff S_0 K r σ T z ≤ Real.exp (-r * T) * K := by
  unfold mcPayoff
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine max_le ?_ hK
  exact (sub_le_self_iff K).2 (bsTerminal_nonneg hS_0.le r σ T z)

/-- The payoff is a measurable (indeed continuous) function of the draw. -/
lemma measurable_mcPayoff (S_0 K r σ T : ℝ) : Measurable (mcPayoff S_0 K r σ T) := by
  unfold mcPayoff bsTerminal
  fun_prop

section Ensemble
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ}

/-! ### Single-draw integrability and L² membership -/

/-- Single draw: the sampled payoff is a.e. strongly measurable. Its law is the
pushforward of the standard normal through `mcPayoff`. -/
theorem aestronglyMeasurable_mcPayoff {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    AEStronglyMeasurable (fun ω => mcPayoff S_0 K r σ T (Z ω)) μ :=
  ((HasLaw.comp (Y := mcPayoff S_0 K r σ T)
      (⟨(measurable_mcPayoff S_0 K r σ T).aemeasurable, rfl⟩ :
        HasLaw (mcPayoff S_0 K r σ T) ((gaussianReal 0 1).map (mcPayoff S_0 K r σ T))
          (gaussianReal 0 1))
      h.Z_law).aemeasurable.aestronglyMeasurable)

/-- **Integrability** (deliverable 1): the sampled put payoff is integrable, by the
pointwise bound `0 ≤ H ≤ e^{-rT}·K` on a probability space. -/
theorem integrable_mcPayoff {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    Integrable (fun ω => mcPayoff S_0 K r σ T (Z ω)) μ := by
  refine memLp_one_iff_integrable.1 ?_
  refine MemLp.of_bound (C := Real.exp (-r * T) * K)
    (aestronglyMeasurable_mcPayoff h) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mcPayoff_nonneg S_0 K r σ T _)]
  exact mcPayoff_le h.S_0_pos h.K_pos.le r σ T _

/-- The sampled payoff is in L² — the CLT hypothesis. -/
theorem memLp2_mcPayoff {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    MemLp (fun ω => mcPayoff S_0 K r σ T (Z ω)) 2 μ := by
  refine MemLp.of_bound (C := Real.exp (-r * T) * K)
    (aestronglyMeasurable_mcPayoff h) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mcPayoff_nonneg S_0 K r σ T _)]
  exact mcPayoff_le h.S_0_pos h.K_pos.le r σ T _

/-- The mean of one sampled payoff is the Black–Scholes put price: this is MathFin's
`bs_put_formula` — the discounted expectation IS the closed form (deliverable 4's
bridge). -/
theorem mean_mcPayoff_eq_bsPut {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, mcPayoff S_0 K r σ T (Z ω) ∂μ
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
        - S_0 * Phi (-(bsd1 S_0 K r σ T)) := by
  simpa only [mcPayoff] using bs_put_formula h

/-! ### The ensemble: independence and identical distribution transfer -/

variable {Z : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- All sampled payoffs have the same pushforward law. -/
theorem hasLaw_mcPayoff (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ) (i : ℕ) :
    HasLaw (fun ω => mcPayoff S_0 K r σ T (Z i ω))
      ((gaussianReal 0 1).map (mcPayoff S_0 K r σ T)) μ :=
  HasLaw.comp (Y := mcPayoff S_0 K r σ T)
    (⟨(measurable_mcPayoff S_0 K r σ T).aemeasurable, rfl⟩ :
      HasLaw (mcPayoff S_0 K r σ T) ((gaussianReal 0 1).map (mcPayoff S_0 K r σ T))
        (gaussianReal 0 1))
    (hlaw i)

omit [IsProbabilityMeasure μ] in
/-- The sampled payoffs are identically distributed. -/
theorem identDistrib_mcPayoff (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ) (i : ℕ) :
    IdentDistrib (fun ω => mcPayoff S_0 K r σ T (Z i ω))
      (fun ω => mcPayoff S_0 K r σ T (Z 0 ω)) μ μ :=
  HasLaw.identDistrib (hasLaw_mcPayoff hlaw i) (hasLaw_mcPayoff hlaw 0)

omit [IsProbabilityMeasure μ] in
/-- Full independence of the ensemble transfers through the payoff map. -/
theorem iIndepFun_mcPayoff (hindep : iIndepFun Z μ) :
    iIndepFun (fun i => fun ω => mcPayoff S_0 K r σ T (Z i ω)) μ :=
  hindep.comp (fun _ => mcPayoff S_0 K r σ T)
    (fun _ => measurable_mcPayoff S_0 K r σ T)

omit [IsProbabilityMeasure μ] in
/-- Pairwise independence of the ensemble transfers through the payoff map — the
Etemadi hypothesis the strong law consumes. (Stated in unfolded `∀` form: `open
Filter` shadows the root `Pairwise`.) -/
theorem pairwise_mcPayoff (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on Z)) :
    ∀ i j : ℕ, i ≠ j →
      (fun ω => mcPayoff S_0 K r σ T (Z i ω)) ⟂ᵢ[μ] (fun ω => mcPayoff S_0 K r σ T (Z j ω)) := by
  intro i j hij
  exact (hindep hij).comp (measurable_mcPayoff S_0 K r σ T)
    (measurable_mcPayoff S_0 K r σ T)

/-! ### The estimator -/

/-- The Monte Carlo estimator: the sample mean of `n` discounted put payoffs. -/
noncomputable def mcMean (S_0 K r σ T : ℝ) {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, mcPayoff S_0 K r σ T (Z i ω)) / (n : ℝ)

/-! ### Deliverable 2: consistency (strong law, Etemadi pairwise form) -/

/-- **Monte Carlo consistency for the put** (lesson 0023, statement (1)).

Under only **pairwise** independence of the standard-normal ensemble (Etemadi's
strong law — the honest hypothesis, so negatively-correlated antithetic pairs
keep consistency) and the risk-neutral lognormal model, the sample-mean estimator
converges almost surely to the Black–Scholes put price
`K·e^{-rT}·Φ(−d₂) − S₀·Φ(−d₁)`. -/
theorem mc_put_consistency (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on Z)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => mcMean S_0 K r σ T Z n ω) atTop
      (𝓝 (K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
        - S_0 * Phi (-(bsd1 S_0 K r σ T)))) := by
  have hint : Integrable (fun ω => mcPayoff S_0 K r σ T (Z 0 ω)) μ :=
    integrable_mcPayoff h
  have hslln := strong_law_ae_real
    (X := fun i => fun ω => mcPayoff S_0 K r σ T (Z i ω))
    hint (pairwise_mcPayoff hindep) (fun i => identDistrib_mcPayoff hlaw i)
  filter_upwards [hslln] with ω hω
  rw [← mean_mcPayoff_eq_bsPut (Z := Z 0) h]
  exact hω.congr fun _ => rfl

/-- The i.i.d. specialization: full independence gives the pairwise hypothesis. -/
theorem mc_put_consistency_iid (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => mcMean S_0 K r σ T Z n ω) atTop
      (𝓝 (K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
        - S_0 * Phi (-(bsd1 S_0 K r σ T)))) := by
  refine mc_put_consistency h hlaw ?_
  intro i j hij
  exact hindep.indepFun hij

/-! ### Deliverable 3: error bars (CLT) -/

/-- **Monte Carlo error bars** (lesson 0023, statement (2)) — the library-form CLT:
`(√n)⁻¹ · (∑_{i<n} H(Z i) − n·P) ⇒ 𝓝(0, σ_H²)` in distribution, where the limit
variance `σ_H² = Var(H)` is identified by the theorem itself (the closed form is
`mc_put_variance` below). Full independence is genuinely needed here — this is the
statement that variance-reduction schemes must re-prove for their dependent
sequences (lesson 0023's research addendum). -/
theorem mc_put_clt_library (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y
      (gaussianReal 0 (Var[fun ω => mcPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) μ') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ *
        (∑ i ∈ Finset.range n, mcPayoff S_0 K r σ T (Z i ω)
          - (n : ℝ) * ∫ ω', mcPayoff S_0 K r σ T (Z 0 ω') ∂μ))
      atTop Y (fun _ => μ) μ' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY (memLp2_mcPayoff h)
    (iIndepFun_mcPayoff hindep) (fun i => identDistrib_mcPayoff hlaw i)

/-- The algebraic identity equating the library CLT integrand with the desk
estimator: `(√n)⁻¹·(s − n·m) = √n·(s/n − m)`. -/
lemma inv_sqrt_mul_sub_eq (s m n : ℝ) (hn : 0 ≤ n) :
    (Real.sqrt n)⁻¹ * (s - n * m) = Real.sqrt n * (s / n - m) := by
  rcases eq_or_lt_of_le hn with h0 | hpos
  · subst h0
    simp
  have hn0 : n ≠ 0 := ne_of_gt hpos
  have hnz : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  field_simp [Real.mul_self_sqrt hn]
  rw [Real.sq_sqrt hn]

/-- **Monte Carlo error bars, desk form**: `√n · (mcMean n − P) ⇒ 𝓝(0, σ_H²)` in
distribution, against the 𝓝(0, σ_H²) limit — the law is
`gaussianReal 0 (Var[fun ω => mcPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal`, not the
standard normal. -/
theorem mc_put_clt (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        (mcMean S_0 K r σ T Z n ω - ∫ ω', mcPayoff S_0 K r σ T (Z 0 ω') ∂μ))
      atTop (id : ℝ → ℝ) (fun _ => μ)
      (gaussianReal 0 (Var[fun ω => mcPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) := by
  have hlib := mc_put_clt_library (μ' := gaussianReal 0
      (Var[fun ω => mcPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) (Y := (id : ℝ → ℝ))
    h hlaw hindep ⟨by fun_prop, Measure.map_id⟩
  refine TendstoInDistribution.congr (fun n => ?_) Filter.EventuallyEq.rfl hlib
  filter_upwards with ω
  simp only [mcMean]
  exact inv_sqrt_mul_sub_eq (∑ i ∈ Finset.range n, mcPayoff S_0 K r σ T (Z i ω))
    (∫ ω', mcPayoff S_0 K r σ T (Z 0 ω') ∂μ) (n : ℝ) (by positivity)

end Ensemble

/-! ### Deliverable 3 continued: the variance, in closed form

The single-draw section: `Z : Ω → ℝ` is one standard-normal sample. -/

section Moments
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ} {Z : Ω → ℝ}

/-- A general three-term linearity lemma for integrals over a measurable set —
the workhorse of the truncated-second-moment computation. -/
lemma integral_lin_comb3 {s : Set ℝ} (_hs : MeasurableSet s)
    {f₁ f₂ f₃ : ℝ → ℝ}
    (h₁ : IntegrableOn f₁ s volume) (h₂ : IntegrableOn f₂ s volume)
    (h₃ : IntegrableOn f₃ s volume) (b₁ b₂ b₃ : ℝ) :
    ∫ z in s, (b₁ * f₁ z - b₂ * f₂ z + b₃ * f₃ z)
      = b₁ * (∫ i in s, f₁ i) - b₂ * (∫ i in s, f₂ i) + b₃ * (∫ i in s, f₃ i) := by
  have hI1 : IntegrableOn (fun z => b₁ * f₁ z) s volume := h₁.const_mul b₁
  have hI2 : IntegrableOn (fun z => b₂ * f₂ z) s volume := h₂.const_mul b₂
  have hI3 : IntegrableOn (fun z => b₃ * f₃ z) s volume := h₃.const_mul b₃
  have hI12 : IntegrableOn (fun z => b₁ * f₁ z - b₂ * f₂ z) s volume := hI1.sub hI2
  have step1 := integral_add hI12 hI3
  have step2 := integral_sub hI1 hI2
  have step4 := integral_const_mul (μ := volume.restrict s) b₁ f₁
  have step5 := integral_const_mul (μ := volume.restrict s) b₂ f₂
  have step6 := integral_const_mul (μ := volume.restrict s) b₃ f₃
  rw [step1, step2, step4, step5, step6]

/-- **Truncated second moment of the lognormal** (the put's second moment):

  `𝔼[(K − S_T)⁺²] = K²·Φ(−d₂) − 2·K·S₀·e^{μ + ν²/2}·Φ(−d₁)
                    + S₀²·e^{2μ + 2ν²}·Φ(−d₁ − ν)`,

with `μ = (r − σ²/2)T`, `ν = σ√T`, computed from MathFin's completing-the-square
primitive `integral_exp_mul_gaussianPDFReal_Iic` — the same atom `Put.lean` prices
with. -/
theorem secondMoment_putPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (max (K - bsTerminal S_0 r σ T (Z ω)) 0) ^ 2 ∂μ
      = K ^ 2 * Phi (-(bsd2 S_0 K r σ T))
        - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
            * Phi (-(bsd1 S_0 K r σ T))
        + S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
            * Phi (-(bsd1 S_0 K r σ T) - σ * Real.sqrt T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_2 := bsd2 S_0 K r σ T with d_2_def
  set μ_log := (r - σ^2 / 2) * T with μ_log_def
  set ν_log := σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_sq : ν_log ^ 2 = σ ^ 2 * T := by
    rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  have h_shift1 : (-d_2) - ν_log = -(bsd1 S_0 K r σ T) := by
    rw [d_2_def, bsd2, bsd1]
    field_simp
    ring
  have h_shift2 : (-d_2) - 2 * ν_log = -(bsd1 S_0 K r σ T) - ν_log := by
    rw [d_2_def, bsd2, bsd1]
    field_simp
    ring
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => (max (K - bsTerminal S_0 r σ T z) 0) ^ 2) (gaussianReal 0 1) := by
    unfold bsTerminal
    fun_prop
  -- Step 1-2: transfer to the standard normal, convert to the density
  rw [show (fun ω => (max (K - bsTerminal S_0 r σ T (Z ω)) 0) ^ 2)
        = (fun z => (max (K - bsTerminal S_0 r σ T z) 0) ^ 2) ∘ Z from rfl,
      hZ.integral_comp hmeas,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Step 3: the square lives on the exercise region `{z ≤ −d₂}`
  rw [show (fun z : ℝ => gaussianPDFReal 0 1 z • (max (K - bsTerminal S_0 r σ T z) 0) ^ 2)
        = (Set.Iic (-d_2)).indicator
            (fun z => gaussianPDFReal 0 1 z * (K - bsTerminal S_0 r σ T z) ^ 2) from
      funext fun z => by
        rw [smul_eq_mul]
        by_cases hz : z ≤ -d_2
        · have h1 : K < bsTerminal S_0 r σ T z ↔ -d_2 < z :=
            bsTerminal_gt_K_iff hS_0 hK hσ hT z
          have hST : ¬ (K < bsTerminal S_0 r σ T z) :=
            fun hc => not_lt.mpr hz (h1.mp hc)
          rw [Set.indicator_of_mem (by simpa using hz : z ∈ Set.Iic (-d_2)),
            max_eq_left (sub_nonneg.mpr (le_of_not_gt hST))]
        · have h1 : K < bsTerminal S_0 r σ T z ↔ -d_2 < z :=
            bsTerminal_gt_K_iff hS_0 hK hσ hT z
          have hlt : -d_2 < z := not_le.mp hz
          rw [Set.indicator_of_notMem (by simpa using hz : z ∉ Set.Iic (-d_2)),
            max_eq_right (sub_nonpos.mpr (le_of_lt (h1.mpr hlt))),
            zero_pow (by norm_num), mul_zero]]
  rw [integral_indicator measurableSet_Iic]
  -- Step 4: expand the square inside the exercise region
  have h_expand : ∀ z ∈ Set.Iic (-d_2),
      gaussianPDFReal 0 1 z * (K - bsTerminal S_0 r σ T z) ^ 2
        = K ^ 2 * gaussianPDFReal 0 1 z
          - (2 * K * (S_0 * Real.exp μ_log)) * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)
          + (S_0 ^ 2 * Real.exp (2 * μ_log)) *
              (Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z _
    have hexp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
        = Real.exp μ_log * Real.exp (ν_log * z) := by
      rw [μ_log_def, ν_log_def, Real.exp_add]
    have hexp2 : Real.exp (2 * ν_log * z)
        = Real.exp (ν_log * z) * Real.exp (ν_log * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp3 : Real.exp (2 * μ_log)
        = Real.exp μ_log * Real.exp μ_log := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold bsTerminal
    rw [hexp, hexp2, hexp3]
    ring
  rw [setIntegral_congr_fun measurableSet_Iic h_expand]
  -- Step 5: the three integrability pieces (Put.lean's route)
  have hint_pdf : IntegrableOn (gaussianPDFReal 0 1) (Set.Iic (-d_2)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hint_eν : IntegrableOn
      (fun z : ℝ => Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) (Set.Iic (-d_2)) volume := by
    refine (((integrable_gaussianPDFReal ν_log 1).const_mul
      (Real.exp (ν_log ^ 2 / 2))).integrableOn).congr_fun ?_ measurableSet_Iic
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one ν_log z).symm
  have hint_e2ν : IntegrableOn
      (fun z : ℝ => Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z)
      (Set.Iic (-d_2)) volume := by
    refine (((integrable_gaussianPDFReal (2 * ν_log) 1).const_mul
      (Real.exp ((2 * ν_log) ^ 2 / 2))).integrableOn).congr_fun ?_ measurableSet_Iic
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one (2 * ν_log) z).symm
  -- Step 6: linearity of the integral
  rw [integral_lin_comb3 measurableSet_Iic hint_pdf hint_eν hint_e2ν
      (K ^ 2) (2 * K * (S_0 * Real.exp μ_log)) (S_0 ^ 2 * Real.exp (2 * μ_log))]
  -- Step 7: the three Gaussian primitives
  rw [show ∫ z in Set.Iic (-d_2), gaussianPDFReal 0 1 z = Phi (-d_2) from by
    rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Iic (0 : ℝ)]; rfl,
    integral_exp_mul_gaussianPDFReal_Iic,
    integral_exp_mul_gaussianPDFReal_Iic]
  rw [h_shift1, h_shift2, μ_log_def]
  -- Step 8: final algebra — merge the exponentials (`(2ν)²/2 = 2ν²` is pure ring)
  have h2ν : (2 * ν_log) ^ 2 / 2 = 2 * ν_log ^ 2 := by
    have h4 : (2 * ν_log) ^ 2 = 4 * ν_log ^ 2 := by ring
    rw [h4]
    ring
  have hm : Real.exp ((r - σ^2 / 2) * T) * Real.exp (ν_log ^ 2 / 2)
      = Real.exp ((r - σ^2 / 2) * T + ν_log ^ 2 / 2) := (Real.exp_add _ _).symm
  have hn : Real.exp (2 * (r - σ^2 / 2) * T) * Real.exp ((2 * ν_log) ^ 2 / 2)
      = Real.exp (2 * (r - σ^2 / 2) * T + 2 * ν_log ^ 2) := by
    rw [h2ν, Real.exp_add]
  linear_combination (norm := ring_nf)
    -(2 * K * S_0 * Phi (-(bsd1 S_0 K r σ T))) * hm
    + (S_0 ^ 2 * Phi (-(bsd1 S_0 K r σ T) - ν_log)) * hn

/-- **Discounted second moment** of the sampled put payoff: `𝔼[H²] = e^{-2rT}·M₂`
with `M₂` the truncated second moment above. -/
theorem secondMoment_mcPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (mcPayoff S_0 K r σ T (Z ω)) ^ 2 ∂μ
      = Real.exp (-2 * r * T) *
          (K ^ 2 * Phi (-(bsd2 S_0 K r σ T))
            - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
                * Phi (-(bsd1 S_0 K r σ T))
            + S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
                * Phi (-(bsd1 S_0 K r σ T) - σ * Real.sqrt T)) := by
  have hexp2 : Real.exp (-r * T) ^ 2 = Real.exp (-2 * r * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : ∀ ω : Ω, (mcPayoff S_0 K r σ T (Z ω)) ^ 2
      = Real.exp (-2 * r * T) * (max (K - bsTerminal S_0 r σ T (Z ω)) 0) ^ 2 := by
    intro ω
    unfold mcPayoff
    rw [mul_pow, hexp2]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsq), integral_const_mul,
    secondMoment_putPayoff h]

/-- **The CLT limit variance in closed form** (lesson 0023, statement (2)'s
`σ_H² = e^{-2rT}·(truncated second moment) − P²`): the variance of the discounted
put payoff is a closed form, composed from `secondMoment_mcPayoff` (the truncated
second moment) and `bs_put_formula` (the price `P`). -/
theorem mc_put_variance (h : BSCallHyp μ S_0 K r σ T Z) :
    Var[fun ω => mcPayoff S_0 K r σ T (Z ω); μ]
      = Real.exp (-2 * r * T) *
          (K ^ 2 * Phi (-(bsd2 S_0 K r σ T))
            - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
                * Phi (-(bsd1 S_0 K r σ T))
            + S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
                * Phi (-(bsd1 S_0 K r σ T) - σ * Real.sqrt T))
        - (K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
            - S_0 * Phi (-(bsd1 S_0 K r σ T))) ^ 2 := by
  rw [variance_eq_sub (memLp2_mcPayoff h)]
  show ∫ ω, mcPayoff S_0 K r σ T (Z ω) ^ 2 ∂μ
      - (∫ ω, mcPayoff S_0 K r σ T (Z ω) ∂μ) ^ 2 = _
  rw [secondMoment_mcPayoff h, mean_mcPayoff_eq_bsPut h]

/-! ### The moment-layer cross-checks -/

/-- Cross-check with MathFin's lognormal moment layer: the same ensemble that drives
the MC pricer has, for its terminal price, the proved lognormal second moment
`E_Q[S_T²] = S₀²·exp(2rT + σ²T)` (`secondMoment_terminal`). -/
theorem mc_terminal_secondMoment (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω)) ^ 2 ∂μ
      = S_0 ^ 2 * Real.exp (2 * r * T + σ ^ 2 * T) :=
  secondMoment_terminal h

/-- Cross-check with MathFin's lognormal moment layer: the terminal-price variance
`Var_Q[S_T] = S₀²·e^{2rT}·(e^{σ²T} − 1)` (`variance_terminal`). -/
theorem mc_terminal_variance (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω)) ^ 2 ∂μ
      - (∫ ω, bsTerminal S_0 r σ T (Z ω) ∂μ) ^ 2
        = S_0 ^ 2 * Real.exp (2 * r * T) * (Real.exp (σ ^ 2 * T) - 1) :=
  variance_terminal h

end Moments

/-! ### The call variants — the call-variant MC theorems

The call is the honest case: the payoff `C(z) = e^{-rT}·max(S_T(z) − K, 0)` is
**unbounded**, so the put's constant-bound route (`MemLp.of_bound`) is gone. What
replaces it:

* **Integrability** by domination: `0 ≤ C ≤ e^{-rT}·S_T` (the discounted terminal),
  whose integral is exactly `S_0` — the discounted-forward identity
  `E[e^{-rT}·S_T] = S_0`. The engine is Mathlib's own Gaussian L¹ fact
  `integrable_exp_mul_gaussianReal` (`exp(t·x)` is integrable for `N(μ,v)`),
  transferred to the ensemble by `integrable_map_measure`.
* **L² membership** from the same domination squared, via
  `memLp_two_iff_integrable_sq_norm` (Mathlib `L2Space`): `MemLp f 2 ↔ ‖f‖²
  integrable` — no constant bound needed.
* **Price bridge**: MathFin's `bs_call_formula` (the expectation-form call price,
  the exact sibling of `bs_put_formula` consumed by the put build).
* **Second moment**: the exercise region is `{z > −d₂}`, so the completing-the-square
  atom is the `Ioi` sibling `integral_exp_mul_gaussianPDFReal_Ioi` (MathFin
  `StandardNormal.lean`), with `gaussianReal_Ioi_toReal` for the strike piece. -/

/-- The discounted European call payoff as a function of the standard-normal draw:
`C(z) = e^{-rT} · max(S_T(z) − K, 0)`. -/
noncomputable def mcCallPayoff (S_0 K r σ T z : ℝ) : ℝ :=
  Real.exp (-r * T) * max (bsTerminal S_0 r σ T z - K) 0

/-- The discounted call payoff is nonnegative. -/
lemma mcCallPayoff_nonneg (S_0 K r σ T z : ℝ) : 0 ≤ mcCallPayoff S_0 K r σ T z := by
  unfold mcCallPayoff
  exact mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

/-- **The call payoff is dominated by the discounted terminal**: `C ≤ e^{-rT}·S_T`.
The unbounded-but-integrable envelope that replaces the put's constant bound. -/
lemma mcCallPayoff_le_terminal (hS_0 : 0 < S_0) (hK : 0 ≤ K) (r σ T z : ℝ) :
    mcCallPayoff S_0 K r σ T z ≤ Real.exp (-r * T) * bsTerminal S_0 r σ T z := by
  unfold mcCallPayoff
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact max_le (sub_le_self _ hK) (bsTerminal_nonneg hS_0.le r σ T z)

/-- The call payoff is a measurable (indeed continuous) function of the draw. -/
lemma measurable_mcCallPayoff (S_0 K r σ T : ℝ) : Measurable (mcCallPayoff S_0 K r σ T) := by
  unfold mcCallPayoff bsTerminal
  fun_prop

section CallDraw
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ} {Z : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- Law-transfer of a.e. strong measurability: if `Z` has law `ν` and `g` is a.e.
strongly measurable for `ν`, then `g ∘ Z` is a.e. strongly measurable. -/
private lemma aestronglyMeasurable_comp_of_hasLaw (hZ : HasLaw Z (gaussianReal 0 1) μ)
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (gaussianReal 0 1)) :
    AEStronglyMeasurable (fun ω => g (Z ω)) μ :=
  ((HasLaw.comp (Y := g)
      (⟨hg.aemeasurable, rfl⟩ :
        HasLaw g ((gaussianReal 0 1).map g) (gaussianReal 0 1))
      hZ).aemeasurable.aestronglyMeasurable)

/-- Single draw: the sampled call payoff is a.e. strongly measurable. -/
theorem aestronglyMeasurable_mcCallPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    AEStronglyMeasurable (fun ω => mcCallPayoff S_0 K r σ T (Z ω)) μ :=
  aestronglyMeasurable_comp_of_hasLaw h.Z_law
    (by unfold mcCallPayoff bsTerminal; fun_prop)

omit [IsProbabilityMeasure μ] in
/-- Gaussian exponential integrability, transferred: `exp(c·Z)` is integrable
whenever `Z` is standard normal — Mathlib's `integrable_exp_mul_gaussianReal`
pulled through the law. This is the call build's replacement for boundedness. -/
theorem integrable_exp_of_hasLaw (hZ : HasLaw Z (gaussianReal 0 1) μ) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * Z ω)) μ := by
  have hsrc : Integrable (fun x : ℝ => Real.exp (c * x)) (μ.map Z) := by
    rw [hZ.map_eq]
    exact integrable_exp_mul_gaussianReal c
  exact (integrable_map_measure hsrc.aestronglyMeasurable hZ.aemeasurable).mp hsrc

/-- **Integrability of the squared terminal** — the L² envelope: `S_T²` is
integrable, being `S₀²·e^{2μ_log}·exp(2ν·Z)` with `exp(2ν·Z)` Gaussian-integrable.
(Facts not numbers: no closed form needed here — the closed form is
`mc_terminal_secondMoment` above.) -/
theorem integrable_sq_terminal (h : BSCallHyp μ S_0 K r σ T Z) :
    Integrable (fun ω => (bsTerminal S_0 r σ T (Z ω)) ^ 2) μ := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  have hsrc : Integrable (fun x : ℝ => S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T)
      * Real.exp ((2 * σ * Real.sqrt T) * x)) (μ.map Z) := by
    rw [hZ.map_eq]
    exact (integrable_exp_mul_gaussianReal (2 * σ * Real.sqrt T)).const_mul _
  have hcomp := (integrable_map_measure hsrc.aestronglyMeasurable hZ.aemeasurable).mp hsrc
  have hpt : ∀ ω : Ω, (fun x : ℝ => S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T)
      * Real.exp ((2 * σ * Real.sqrt T) * x)) (Z ω)
      = (bsTerminal S_0 r σ T (Z ω)) ^ 2 := by
    intro ω
    have e1 : Real.exp (2 * (r - σ^2 / 2) * T + (2 * σ * Real.sqrt T) * Z ω)
        = Real.exp (2 * (r - σ^2 / 2) * T) * Real.exp ((2 * σ * Real.sqrt T) * Z ω) :=
      Real.exp_add _ _
    have e2 : Real.exp (((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω)
          + ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω))
        = Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω)
            * Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω) :=
      Real.exp_add _ _
    have e3 : ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω)
        + ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω)
        = 2 * (r - σ^2 / 2) * T + (2 * σ * Real.sqrt T) * Z ω := by ring
    have e5 : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω) ^ 2
        = Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω)
            * Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω) :=
      pow_two _
    unfold bsTerminal
    rw [mul_pow, e5, ← e2, e3, e1]
    ring
  have hae : (fun x : ℝ => S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T)
      * Real.exp ((2 * σ * Real.sqrt T) * x)) ∘ Z
      =ᵐ[μ] (fun ω => (bsTerminal S_0 r σ T (Z ω)) ^ 2) :=
    Filter.Eventually.of_forall fun ω => hpt ω
  exact (integrable_congr hae).mp hcomp

/-- **Integrability of the discounted terminal** — the domination envelope
`e^{-rT}·S_T` for the call payoff (the put used the constant `e^{-rT}·K`; the call's
envelope is genuinely unbounded). -/
theorem integrable_discountedTerminal (h : BSCallHyp μ S_0 K r σ T Z) :
    Integrable (fun ω => Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω)) μ := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  have hsrc : Integrable (fun x : ℝ => S_0 * Real.exp ((r - σ^2 / 2) * T)
      * Real.exp (-r * T) * Real.exp (σ * Real.sqrt T * x)) (μ.map Z) := by
    rw [hZ.map_eq]
    exact (integrable_exp_mul_gaussianReal (σ * Real.sqrt T)).const_mul _
  have hcomp := (integrable_map_measure hsrc.aestronglyMeasurable hZ.aemeasurable).mp hsrc
  have hpt : ∀ ω : Ω, (fun x : ℝ => S_0 * Real.exp ((r - σ^2 / 2) * T)
      * Real.exp (-r * T) * Real.exp (σ * Real.sqrt T * x)) (Z ω)
      = Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω) := by
    intro ω
    have h1 : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * Z ω)
        = Real.exp ((r - σ^2 / 2) * T) * Real.exp (σ * Real.sqrt T * Z ω) :=
      Real.exp_add _ _
    unfold bsTerminal
    rw [h1]
    ring
  have hae : (fun x : ℝ => S_0 * Real.exp ((r - σ^2 / 2) * T)
      * Real.exp (-r * T) * Real.exp (σ * Real.sqrt T * x)) ∘ Z
      =ᵐ[μ] (fun ω => Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω)) :=
    Filter.Eventually.of_forall fun ω => hpt ω
  exact (integrable_congr hae).mp hcomp

/-- **The discounted-forward identity**: `E[e^{-rT}·S_T] = S_0`. The risk-neutral
engine's spot-price identity, read off the same transfer that proves integrability:
`e^{-rT}·S₀·e^{(r−σ²/2)T}·e^{σ²T/2} = S₀`. -/
theorem integral_discountedTerminal_eq (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω) ∂μ = S_0 := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => Real.exp (-r * T) * bsTerminal S_0 r σ T z) (gaussianReal 0 1) := by
    unfold bsTerminal
    fun_prop
  rw [show (fun ω => Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω))
      = (fun z => Real.exp (-r * T) * bsTerminal S_0 r σ T z) ∘ Z from rfl,
    hZ.integral_comp hmeas,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  have hsplit : ∀ z : ℝ,
      gaussianPDFReal 0 1 z • (Real.exp (-r * T) * bsTerminal S_0 r σ T z)
        = (S_0 * (Real.exp ((r - σ^2 / 2) * T) * Real.exp (-r * T)))
            * (Real.exp (σ * Real.sqrt T * z) * gaussianPDFReal 0 1 z) := by
    intro z
    unfold bsTerminal
    rw [smul_eq_mul, Real.exp_add]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_const_mul,
    integral_exp_mul_gaussianPDFReal_univ]
  have hν : (σ * Real.sqrt T) ^ 2 = σ ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt hT.le]
  have h0 : (r - σ^2 / 2) * T + -r * T + (σ * Real.sqrt T) ^ 2 / 2 = 0 := by
    rw [hν]; ring
  have hsplit2 : S_0 * (Real.exp ((r - σ^2 / 2) * T) * Real.exp (-r * T))
      * Real.exp ((σ * Real.sqrt T) ^ 2 / 2) = S_0 := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, h0, Real.exp_zero, mul_one]
  rw [hsplit2]

/-- **Call integrability** (deliverable 1): the sampled call payoff is integrable,
by domination `0 ≤ C ≤ e^{-rT}·S_T` with the discounted terminal integrable —
the honest case, where boundedness fails and domination replaces it. -/
theorem integrable_mcCallPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    Integrable (fun ω => mcCallPayoff S_0 K r σ T (Z ω)) μ := by
  refine (integrable_discountedTerminal h).mono' (aestronglyMeasurable_mcCallPayoff h) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mcCallPayoff_nonneg S_0 K r σ T _)]
  exact mcCallPayoff_le_terminal h.S_0_pos h.K_pos.le r σ T _

/-- The sampled call payoff is in L² — the CLT hypothesis, proved by domination
`‖C‖² ≤ (e^{-rT}·S_T)²` with `S_T²` integrable (`memLp_two_iff_integrable_sq_norm`
is the bridge; no constant bound exists). -/
theorem memLp2_mcCallPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    MemLp (fun ω => mcCallPayoff S_0 K r σ T (Z ω)) 2 μ := by
  have hdom : Integrable
      (fun ω => (Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω)) ^ 2) μ := by
    have h0 : Integrable
        (fun ω => Real.exp (-r * T) ^ 2 * (bsTerminal S_0 r σ T (Z ω)) ^ 2) μ :=
      (integrable_sq_terminal h).const_mul _
    refine (integrable_congr (Filter.Eventually.of_forall ?_)).mp h0
    intro ω
    exact (mul_pow (Real.exp (-r * T)) (bsTerminal S_0 r σ T (Z ω)) 2).symm
  have haes2 : AEStronglyMeasurable (fun x => mcCallPayoff S_0 K r σ T (Z x) ^ 2) μ :=
    aestronglyMeasurable_comp_of_hasLaw
      (g := fun z => mcCallPayoff S_0 K r σ T z ^ 2) h.Z_law
      (by unfold mcCallPayoff bsTerminal; fun_prop)
  have hint2 : Integrable (fun x => mcCallPayoff S_0 K r σ T (Z x) ^ 2) μ := by
    refine hdom.mono' haes2 ?_
    filter_upwards with ω
    have hpos : 0 ≤ Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω) :=
      mul_nonneg (Real.exp_pos _).le (bsTerminal_nonneg h.S_0_pos.le r σ T _)
    have habs : |mcCallPayoff S_0 K r σ T (Z ω)|
        ≤ |Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω)| := by
      rw [abs_of_nonneg (mcCallPayoff_nonneg S_0 K r σ T _), abs_of_nonneg hpos]
      exact mcCallPayoff_le_terminal h.S_0_pos h.K_pos.le r σ T _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (mcCallPayoff S_0 K r σ T (Z ω)))]
    exact sq_le_sq.2 habs
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_mcCallPayoff h)]
  refine (integrable_congr ?_).mp hint2
  filter_upwards with ω
  show mcCallPayoff S_0 K r σ T (Z ω) ^ 2 = ‖mcCallPayoff S_0 K r σ T (Z ω)‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs]

/-- The mean of one sampled call payoff is the Black–Scholes call price: MathFin's
`bs_call_formula` — the expectation-form bridge, sibling of the put's. -/
theorem mean_mcCallPayoff_eq_bsCall (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, mcCallPayoff S_0 K r σ T (Z ω) ∂μ
      = S_0 * Phi (bsd1 S_0 K r σ T)
        - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  simpa only [mcCallPayoff] using bs_call_formula h

end CallDraw

/-! ### The call ensemble: consistency (strong law) and error bars (CLT) -/

section CallEnsemble
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ} {Z : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- All sampled call payoffs have the same pushforward law. -/
theorem hasLaw_mcCallPayoff (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ) (i : ℕ) :
    HasLaw (fun ω => mcCallPayoff S_0 K r σ T (Z i ω))
      ((gaussianReal 0 1).map (mcCallPayoff S_0 K r σ T)) μ :=
  HasLaw.comp (Y := mcCallPayoff S_0 K r σ T)
    (⟨(measurable_mcCallPayoff S_0 K r σ T).aemeasurable, rfl⟩ :
      HasLaw (mcCallPayoff S_0 K r σ T) ((gaussianReal 0 1).map (mcCallPayoff S_0 K r σ T))
        (gaussianReal 0 1))
    (hlaw i)

omit [IsProbabilityMeasure μ] in
/-- The sampled call payoffs are identically distributed. -/
theorem identDistrib_mcCallPayoff (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ) (i : ℕ) :
    IdentDistrib (fun ω => mcCallPayoff S_0 K r σ T (Z i ω))
      (fun ω => mcCallPayoff S_0 K r σ T (Z 0 ω)) μ μ :=
  HasLaw.identDistrib (hasLaw_mcCallPayoff hlaw i) (hasLaw_mcCallPayoff hlaw 0)

omit [IsProbabilityMeasure μ] in
/-- Full independence of the ensemble transfers through the call payoff map. -/
theorem iIndepFun_mcCallPayoff (hindep : iIndepFun Z μ) :
    iIndepFun (fun i => fun ω => mcCallPayoff S_0 K r σ T (Z i ω)) μ :=
  hindep.comp (fun _ => mcCallPayoff S_0 K r σ T)
    (fun _ => measurable_mcCallPayoff S_0 K r σ T)

omit [IsProbabilityMeasure μ] in
/-- Pairwise independence of the ensemble transfers through the call payoff map —
the Etemadi hypothesis the strong law consumes. -/
theorem pairwise_mcCallPayoff (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on Z)) :
    ∀ i j : ℕ, i ≠ j →
      (fun ω => mcCallPayoff S_0 K r σ T (Z i ω)) ⟂ᵢ[μ]
        (fun ω => mcCallPayoff S_0 K r σ T (Z j ω)) := by
  intro i j hij
  exact (hindep hij).comp (measurable_mcCallPayoff S_0 K r σ T)
    (measurable_mcCallPayoff S_0 K r σ T)

/-- The Monte Carlo estimator for the call: the sample mean of `n` discounted call
payoffs. -/
noncomputable def mcCallMean (S_0 K r σ T : ℝ) {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, mcCallPayoff S_0 K r σ T (Z i ω)) / (n : ℝ)

/-- **Monte Carlo consistency for the call** (deliverable 2).

Under only **pairwise** independence of the standard-normal ensemble (Etemadi's
strong law — antithetic-pair samplers keep consistency) and the risk-neutral
lognormal model, the sample-mean estimator converges almost surely to the
Black–Scholes call price `S₀·Φ(d₁) − K·e^{-rT}·Φ(d₂)`. -/
theorem mc_call_consistency (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on Z)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => mcCallMean S_0 K r σ T Z n ω) atTop
      (𝓝 (S_0 * Phi (bsd1 S_0 K r σ T)
        - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T))) := by
  have hint : Integrable (fun ω => mcCallPayoff S_0 K r σ T (Z 0 ω)) μ :=
    integrable_mcCallPayoff h
  have hslln := strong_law_ae_real
    (X := fun i => fun ω => mcCallPayoff S_0 K r σ T (Z i ω))
    hint (pairwise_mcCallPayoff hindep) (fun i => identDistrib_mcCallPayoff hlaw i)
  filter_upwards [hslln] with ω hω
  rw [← mean_mcCallPayoff_eq_bsCall (Z := Z 0) h]
  exact hω.congr fun _ => rfl

/-- The i.i.d. specialization for the call: full independence gives the pairwise
hypothesis. -/
theorem mc_call_consistency_iid (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => mcCallMean S_0 K r σ T Z n ω) atTop
      (𝓝 (S_0 * Phi (bsd1 S_0 K r σ T)
        - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T))) := by
  refine mc_call_consistency h hlaw ?_
  intro i j hij
  exact hindep.indepFun hij

/-- **Monte Carlo error bars for the call** (deliverable 3) — the library-form CLT:
`(√n)⁻¹ · (∑_{i<n} C(Z i) − n·C_BS) ⇒ 𝓝(0, σ_C²)` in distribution, with the limit
variance identified as `Var(C)` (closed form: `mc_call_variance` below). Full
independence is genuinely needed here — variance-reduction schemes must re-prove
this for their dependent sequences. -/
theorem mc_call_clt_library (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y
      (gaussianReal 0 (Var[fun ω => mcCallPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) μ') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ *
        (∑ i ∈ Finset.range n, mcCallPayoff S_0 K r σ T (Z i ω)
          - (n : ℝ) * ∫ ω', mcCallPayoff S_0 K r σ T (Z 0 ω') ∂μ))
      atTop Y (fun _ => μ) μ' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY (memLp2_mcCallPayoff h)
    (iIndepFun_mcCallPayoff hindep) (fun i => identDistrib_mcCallPayoff hlaw i)

/-- **Monte Carlo error bars for the call, desk form** (deliverable 3):
`√n · (mcCallMean n − C_BS) ⇒ 𝓝(0, σ_C²)` in distribution, against the
`𝓝(0, σ_C²)` limit with `σ_C² = Var(C)`. -/
theorem mc_call_clt (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        (mcCallMean S_0 K r σ T Z n ω - ∫ ω', mcCallPayoff S_0 K r σ T (Z 0 ω') ∂μ))
      atTop (id : ℝ → ℝ) (fun _ => μ)
      (gaussianReal 0 (Var[fun ω => mcCallPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) := by
  have hlib := mc_call_clt_library (μ' := gaussianReal 0
      (Var[fun ω => mcCallPayoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) (Y := (id : ℝ → ℝ))
    h hlaw hindep ⟨by fun_prop, Measure.map_id⟩
  refine TendstoInDistribution.congr (fun n => ?_) Filter.EventuallyEq.rfl hlib
  filter_upwards with ω
  simp only [mcCallMean]
  exact inv_sqrt_mul_sub_eq (∑ i ∈ Finset.range n, mcCallPayoff S_0 K r σ T (Z i ω))
    (∫ ω', mcCallPayoff S_0 K r σ T (Z 0 ω') ∂μ) (n : ℝ) (by positivity)

end CallEnsemble

/-! ### The call's variance, in closed form

Single-draw section: `Z : Ω → ℝ` is one standard-normal sample; the exercise
region is `{z > −d₂}` (the `Ioi` mirror of the put's `Iic` computation). -/

section CallMoments
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ} {Z : Ω → ℝ}

/-- **Truncated second moment of the lognormal, call side**:

  `𝔼[(S_T − K)⁺²] = S₀²·e^{2μ + 2ν²}·Φ(d₁ + ν) − 2·K·S₀·e^{μ + ν²/2}·Φ(d₁)
                    + K²·Φ(d₂)`,

with `μ = (r − σ²/2)T`, `ν = σ√T`, computed from MathFin's `Ioi` completing-the-square
primitive `integral_exp_mul_gaussianPDFReal_Ioi` (the call's exercise region
`{z > −d₂}` is a right tail) and `gaussianReal_Ioi_toReal` for the strike piece. -/
theorem secondMoment_callPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (max (bsTerminal S_0 r σ T (Z ω) - K) 0) ^ 2 ∂μ
      = S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
          * Phi (bsd1 S_0 K r σ T + σ * Real.sqrt T)
        - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
            * Phi (bsd1 S_0 K r σ T)
        + K ^ 2 * Phi (bsd2 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_2 := bsd2 S_0 K r σ T with d_2_def
  set μ_log := (r - σ^2 / 2) * T with μ_log_def
  set ν_log := σ * Real.sqrt T with ν_log_def
  have hν_log_sq : ν_log ^ 2 = σ ^ 2 * T := by
    rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  have h_shift1 : ν_log - (-d_2) = bsd1 S_0 K r σ T := by
    rw [ν_log_def, d_2_def, bsd2, bsd1]
    ring
  have h_shift2 : 2 * ν_log - (-d_2) = bsd1 S_0 K r σ T + ν_log := by
    rw [ν_log_def, d_2_def, bsd2, bsd1]
    ring
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => (max (bsTerminal S_0 r σ T z - K) 0) ^ 2) (gaussianReal 0 1) := by
    unfold bsTerminal
    fun_prop
  -- Step 1-2: transfer to the standard normal, convert to the density
  rw [show (fun ω => (max (bsTerminal S_0 r σ T (Z ω) - K) 0) ^ 2)
        = (fun z => (max (bsTerminal S_0 r σ T z - K) 0) ^ 2) ∘ Z from rfl,
      hZ.integral_comp hmeas,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Step 3: the square lives on the exercise region `{z > −d₂}`
  rw [show (fun z : ℝ => gaussianPDFReal 0 1 z • (max (bsTerminal S_0 r σ T z - K) 0) ^ 2)
        = (Set.Ioi (-d_2)).indicator
            (fun z => gaussianPDFReal 0 1 z * (bsTerminal S_0 r σ T z - K) ^ 2) from
      funext fun z => by
        rw [smul_eq_mul]
        by_cases hz : z ∈ Set.Ioi (-d_2)
        · have h1 : K < bsTerminal S_0 r σ T z ↔ -d_2 < z :=
            bsTerminal_gt_K_iff hS_0 hK hσ hT z
          have hST : K < bsTerminal S_0 r σ T z := h1.mpr hz
          rw [Set.indicator_of_mem (by simpa using hz : z ∈ Set.Ioi (-d_2)),
            max_eq_left (sub_nonneg.mpr (le_of_lt hST))]
        · have h1 : K < bsTerminal S_0 r σ T z ↔ -d_2 < z :=
            bsTerminal_gt_K_iff hS_0 hK hσ hT z
          have hST : bsTerminal S_0 r σ T z ≤ K :=
            le_of_not_gt fun hc => hz (h1.mp hc)
          rw [Set.indicator_of_notMem (by simpa using hz : z ∉ Set.Ioi (-d_2)),
            max_eq_right (sub_nonpos.mpr hST),
            zero_pow (by norm_num), mul_zero]]
  rw [integral_indicator measurableSet_Ioi]
  -- Step 4: expand the square inside the exercise region
  have h_expand : ∀ z ∈ Set.Ioi (-d_2),
      gaussianPDFReal 0 1 z * (bsTerminal S_0 r σ T z - K) ^ 2
        = (S_0 ^ 2 * Real.exp (2 * μ_log)) * (Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z)
          - (2 * K * (S_0 * Real.exp μ_log)) * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)
          + K ^ 2 * gaussianPDFReal 0 1 z := by
    intro z _
    have hexp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
        = Real.exp μ_log * Real.exp (ν_log * z) := by
      rw [μ_log_def, ν_log_def, Real.exp_add]
    have hexp2 : Real.exp (2 * ν_log * z)
        = Real.exp (ν_log * z) * Real.exp (ν_log * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp3 : Real.exp (2 * μ_log)
        = Real.exp μ_log * Real.exp μ_log := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold bsTerminal
    rw [hexp, hexp2, hexp3]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_expand]
  -- Step 5: the three integrability pieces (the put's route, on `Ioi`)
  have hint_pdf : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi (-d_2)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hint_eν : IntegrableOn
      (fun z : ℝ => Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) (Set.Ioi (-d_2)) volume := by
    refine (((integrable_gaussianPDFReal ν_log 1).const_mul
      (Real.exp (ν_log ^ 2 / 2))).integrableOn).congr_fun ?_ measurableSet_Ioi
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one ν_log z).symm
  have hint_e2ν : IntegrableOn
      (fun z : ℝ => Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z)
      (Set.Ioi (-d_2)) volume := by
    refine (((integrable_gaussianPDFReal (2 * ν_log) 1).const_mul
      (Real.exp ((2 * ν_log) ^ 2 / 2))).integrableOn).congr_fun ?_ measurableSet_Ioi
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one (2 * ν_log) z).symm
  -- Step 6: linearity of the integral
  rw [integral_lin_comb3 measurableSet_Ioi hint_e2ν hint_eν hint_pdf
      (S_0 ^ 2 * Real.exp (2 * μ_log)) (2 * K * (S_0 * Real.exp μ_log)) (K ^ 2)]
  -- Step 7: the three Gaussian primitives — now the `Ioi` siblings
  rw [show ∫ z in Set.Ioi (-d_2), Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z
        = Real.exp ((2 * ν_log) ^ 2 / 2) * Phi (2 * ν_log - (-d_2)) from
      integral_exp_mul_gaussianPDFReal_Ioi _ _,
    show ∫ z in Set.Ioi (-d_2), Real.exp (ν_log * z) * gaussianPDFReal 0 1 z
        = Real.exp (ν_log ^ 2 / 2) * Phi (ν_log - (-d_2)) from
      integral_exp_mul_gaussianPDFReal_Ioi _ _,
    show ∫ z in Set.Ioi (-d_2), gaussianPDFReal 0 1 z = Phi d_2 from by
      rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Ioi (0 : ℝ),
        gaussianReal_Ioi_toReal, neg_neg]]
  rw [h_shift2, h_shift1, μ_log_def]
  -- Step 8: final algebra — merge the exponentials
  have h2ν : (2 * ν_log) ^ 2 / 2 = 2 * ν_log ^ 2 := by
    have h4 : (2 * ν_log) ^ 2 = 4 * ν_log ^ 2 := by ring
    rw [h4]
    ring
  have hm : Real.exp ((r - σ^2 / 2) * T) * Real.exp (ν_log ^ 2 / 2)
      = Real.exp ((r - σ^2 / 2) * T + ν_log ^ 2 / 2) := (Real.exp_add _ _).symm
  have hn : Real.exp (2 * (r - σ^2 / 2) * T) * Real.exp ((2 * ν_log) ^ 2 / 2)
      = Real.exp (2 * (r - σ^2 / 2) * T + 2 * ν_log ^ 2) := by
    rw [h2ν, Real.exp_add]
  linear_combination (norm := ring_nf)
    (S_0 ^ 2 * Phi (bsd1 S_0 K r σ T + ν_log)) * hn
    - (2 * K * S_0 * Phi (bsd1 S_0 K r σ T)) * hm

/-- **Discounted second moment** of the sampled call payoff: `𝔼[C²] = e^{-2rT}·M₂`
with `M₂` the call-side truncated second moment above. -/
theorem secondMoment_mcCallPayoff (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (mcCallPayoff S_0 K r σ T (Z ω)) ^ 2 ∂μ
      = Real.exp (-2 * r * T) *
          (S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
              * Phi (bsd1 S_0 K r σ T + σ * Real.sqrt T)
            - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
                * Phi (bsd1 S_0 K r σ T)
            + K ^ 2 * Phi (bsd2 S_0 K r σ T)) := by
  have hexp2 : Real.exp (-r * T) ^ 2 = Real.exp (-2 * r * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : ∀ ω : Ω, (mcCallPayoff S_0 K r σ T (Z ω)) ^ 2
      = Real.exp (-2 * r * T) * (max (bsTerminal S_0 r σ T (Z ω) - K) 0) ^ 2 := by
    intro ω
    unfold mcCallPayoff
    rw [mul_pow, hexp2]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsq), integral_const_mul,
    secondMoment_callPayoff h]

/-- **The CLT limit variance in closed form for the call** (deliverable 4):
`σ_C² = e^{-2rT}·(call-side truncated second moment) − C_BS²`, composed from
`secondMoment_mcCallPayoff` (the truncated second moment) and `bs_call_formula`
(the price `C_BS`). -/
theorem mc_call_variance (h : BSCallHyp μ S_0 K r σ T Z) :
    Var[fun ω => mcCallPayoff S_0 K r σ T (Z ω); μ]
      = Real.exp (-2 * r * T) *
          (S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
              * Phi (bsd1 S_0 K r σ T + σ * Real.sqrt T)
            - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
                * Phi (bsd1 S_0 K r σ T)
            + K ^ 2 * Phi (bsd2 S_0 K r σ T))
        - (S_0 * Phi (bsd1 S_0 K r σ T)
            - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T)) ^ 2 := by
  rw [variance_eq_sub (memLp2_mcCallPayoff h)]
  show ∫ ω, mcCallPayoff S_0 K r σ T (Z ω) ^ 2 ∂μ
      - (∫ ω, mcCallPayoff S_0 K r σ T (Z ω) ∂μ) ^ 2 = _
  rw [secondMoment_mcCallPayoff h, mean_mcCallPayoff_eq_bsCall h]

end CallMoments

/-! ### The multi-D seed (deliverable 5)

The honest scoping of the 1-D build — "the countable-product construction lives in
MathFin's broken-at-this-pin `Probability.ProductMeasure`" — is answered by Mathlib's
own product-measure layer, which is alive at this pin: `Measure.pi` (finite products,
`Mathlib/MeasureTheory/Constructions/Pi.lean`) carries
`iIndepFun.hasLaw_pi` (`Mathlib/Probability/HasLaw.lean`): **d independent scalars ARE
one d-dimensional vector with the product law**, and conversely. The seed theorem
below is the multi-D consistency statement: i.i.d. vector draws from the d-dim
standard Gaussian, any measurable integrable payoff `H` of the whole vector, Etemadi
strong law to `∫ H ∂(multiGauss d)`. What it deliberately does NOT do: a closed-form
multi-D price (the 1-D closed forms are Gaussian-∫ specials; multi-D needs the
multivariate-normal machinery MathFin grows elsewhere) and a multi-D CLT (the
`Fin d → ℝ`-valued CLT composes coordinate-wise — future layer). -/

/-- The `d`-dimensional standard Gaussian: the product of `d` standard normals on
`Fin d → ℝ` — the law of the joint vector `(Z 0, …, Z (d−1))`. -/
noncomputable def multiGauss (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance multiGauss_instIsProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (multiGauss d) := by
  unfold multiGauss
  infer_instance

section MultiD
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {d : ℕ}

omit [IsProbabilityMeasure μ] in
/-- **The joint bridge**: `d` independent standard normals ARE one `d`-dimensional
Gaussian vector — the joint vector `(Z 0, …, Z (d−1))` has law `multiGauss d`
(Mathlib's `iIndepFun.hasLaw_pi`, the fact that replaces the broken-at-pin MathFin
`ProductMeasure`). -/
theorem multiGauss_hasLaw_joint {Z : Fin d → Ω → ℝ}
    (hlaw : ∀ j, HasLaw (Z j) (gaussianReal 0 1) μ) (hindep : iIndepFun Z μ) :
    HasLaw (fun ω j => Z j ω) (multiGauss d) μ :=
  hindep.hasLaw_pi hlaw

omit [IsProbabilityMeasure μ] in
/-- **Multi-D consistency seed** (deliverable 5): i.i.d. draws `W i` from the
`d`-dimensional standard Gaussian and any measurable integrable payoff `H` of the
whole vector — the sample mean converges almost surely to `∫ H ∂(multiGauss d)`.

This is the same Etemadi route as the 1-D theorems, applied to the composed
variables `H ∘ W i`: integrability transfers through the law
(`integrable_map_measure`), pairwise independence through payoff measurability
(`IndepFun.comp`). The precise hypotheses for a full multi-D pricer: `H`
measurable + integrable against the product law (closed-form `∫ H` is a
multivariate-Gaussian computation, out of scope here), and independence in the
vector sense — `iIndepFun.hasLaw_pi`/`iIndepFun_iff_hasLaw_pi_pi` convert between
"d independent coordinates" and "one vector draw with product law". -/
theorem multiD_consistency {W : ℕ → Ω → (Fin d → ℝ)} {H : (Fin d → ℝ) → ℝ}
    (hHmeas : Measurable H) (hint : Integrable H (multiGauss d))
    (hlaw : ∀ i : ℕ, HasLaw (W i) (multiGauss d) μ)
    (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on W)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, H (W i ω)) / (n : ℝ)) atTop
      (𝓝 (∫ w, H w ∂(multiGauss d))) := by
  have hint0 : Integrable (fun ω => H (W 0 ω)) μ := by
    have hl0 := hlaw 0
    have hmap : Integrable H (μ.map (W 0)) := by
      rw [hl0.map_eq]
      exact hint
    exact (integrable_map_measure hmap.aestronglyMeasurable hl0.aemeasurable).mp hmap
  have hpair : ∀ i j : ℕ, i ≠ j →
      (fun ω => H (W i ω)) ⟂ᵢ[μ] (fun ω => H (W j ω)) := by
    intro i j hij
    exact (hindep hij).comp hHmeas hHmeas
  have hident : ∀ i : ℕ, IdentDistrib (fun ω => H (W i ω)) (fun ω => H (W 0 ω)) μ μ := by
    intro i
    have hlawH : HasLaw H ((multiGauss d).map H) (multiGauss d) :=
      ⟨hHmeas.aemeasurable, rfl⟩
    exact HasLaw.identDistrib (hlawH.comp (hlaw i)) (hlawH.comp (hlaw 0))
  have hslln := strong_law_ae_real (fun i => fun ω => H (W i ω)) hint0 hpair hident
  have heq : ∫ ω, H (W 0 ω) ∂μ = ∫ w, H w ∂(multiGauss d) := by
    have hAESM : AEStronglyMeasurable H (μ.map (W 0)) := by
      rw [(hlaw 0).map_eq]
      exact hint.aestronglyMeasurable
    rw [← integral_map (hlaw 0).aemeasurable hAESM, (hlaw 0).map_eq]
  filter_upwards [hslln] with ω hω
  have hω' : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, H (W i ω)) / (n : ℝ)) atTop
      (𝓝 (∫ w, H w ∂(multiGauss d))) := by
    rw [← heq]
    exact hω
  exact hω'

omit [IsProbabilityMeasure μ] in
/-- The i.i.d. specialization of the multi-D seed. -/
theorem multiD_consistency_iid {W : ℕ → Ω → (Fin d → ℝ)} {H : (Fin d → ℝ) → ℝ}
    (hHmeas : Measurable H) (hint : Integrable H (multiGauss d))
    (hlaw : ∀ i : ℕ, HasLaw (W i) (multiGauss d) μ)
    (hindep : iIndepFun W μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, H (W i ω)) / (n : ℝ)) atTop
      (𝓝 (∫ w, H w ∂(multiGauss d))) := by
  refine multiD_consistency hHmeas hint hlaw ?_
  intro i j hij
  exact hindep.indepFun hij

/-- The bounded-payoff instance of the seed's integrability hypothesis: any
a.e.-strongly-measurable payoff bounded by a constant (a **capped** claim — the
standard variance-reduction-friendly truncation of an unbounded payoff) is
integrable against the product law. -/
theorem multiD_integrable_of_bounded {H : (Fin d → ℝ) → ℝ}
    (hH : AEStronglyMeasurable H (multiGauss d)) (C : ℝ)
    (hb : ∀ w : Fin d → ℝ, ‖H w‖ ≤ C) : Integrable H (multiGauss d) :=
  memLp_one_iff_integrable.1 (MemLp.of_bound hH C (Filter.Eventually.of_forall hb))

end MultiD

/-! ### The moment of the course: audit -/

#print axioms mcPayoff_le
#print axioms integrable_mcPayoff
#print axioms mc_put_consistency
#print axioms mc_put_consistency_iid
#print axioms mc_put_clt
#print axioms secondMoment_putPayoff
#print axioms secondMoment_mcPayoff
#print axioms mc_put_variance
#print axioms mcCallPayoff_le_terminal
#print axioms integrable_discountedTerminal
#print axioms integral_discountedTerminal_eq
#print axioms integrable_mcCallPayoff
#print axioms memLp2_mcCallPayoff
#print axioms mean_mcCallPayoff_eq_bsCall
#print axioms mc_call_consistency
#print axioms mc_call_consistency_iid
#print axioms mc_call_clt_library
#print axioms mc_call_clt
#print axioms secondMoment_callPayoff
#print axioms secondMoment_mcCallPayoff
#print axioms mc_call_variance
#print axioms multiGauss_hasLaw_joint
#print axioms multiD_consistency
#print axioms multiD_consistency_iid
#print axioms multiD_integrable_of_bounded

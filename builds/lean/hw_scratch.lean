import Mathlib
import MathFin.FixedIncome.VasicekBondPrice

/-!
# Hull–White with deterministic θ: the first build (lesson 0020, steps 1–3, and step 4)

The model is `dr_t = (θ(t) − κ r_t) dt + σ dB_t` with `κ > 0` and `θ` deterministic
(continuity hypotheses stated where the FTC needs them). Built by generalizing the
proved Vasicek template:

* **HW-1** — the deterministic part: `hwDeterministic` is the particular solution
  `α(t) = e^{−κt}(r₀ + ∫₀ᵗ e^{κs} θ(s) ds)` with `α(0) = r₀`. The ODE lemma
  `hwDeterministic_solves_ODE` generalizes `vasicekDeterministic_solves_ODE`;
  constant θ reduces to Vasicek verbatim (`hwDeterministic_const`); uniqueness of
  the ODE solution gives the desk mean identity
  `𝔼[r_t] = α(t) + (r₀ − α(0)) e^{−κt}` (`hwMean`).
* **HW-2** — the short rate in Wiener representation: `hwIntegratedRate`
  (= `hwDeterministic` + `σ·`Wiener integral of the kernel `e^{−κ(t−u)}`) is
  Gaussian with the Vasicek variance `(σ²/2κ)(1 − e^{−2κt})` — θ shifts means,
  never variances (`hwIntegratedRate_hasLaw_gaussian`).
* **HW-3** — the affine bond price: the integrated rate reuses the Vasicek
  integrated kernel `vasicekIntegratedKernelLp` verbatim (integrating the diffusion
  kernel over `s ∈ [u, T]` is model-independent), so `hwBondPrice_eq` is the
  exponential-Gaussian moment with variance `vasicekBondV` again; `hwBondA` gains
  the θ-forcing integral and `hwBondPrice_affine` closes the affine term structure
  with `vasicekBondB` reused verbatim.

No `sorry`. `#print axioms` audit at the end (HW-4).

Structural note: the pinned Mathlib has no Fubini theorem for interval integrals,
so the HW-3 mean identity is proved by an antiderivative
(`hwBeta_integral`: `G(s) = (1/κ)(∫₀ˢ θ − e^{−κs}·∫₀ˢ e^{κu}θ)` has `G' = e^{−κs}·I(s)`,
`G(0) = 0`) plus a pointwise expansion of `θ(s)·B(t−s)` (`hwIntegral_theta_B`).

HW-5 (calibration, lesson 0020 step 4): `hwTheta` is the verified identity
`θ(t) = ∂_t f(0,t) + κ f(0,t) + (σ²/2κ)(1 − e^{−2κt})`; `hwCalibAlpha_solves_ODE`
verifies by differentiation that the closed-form `β(t) = f(0,t) +
(σ²/2κ²)(1 − e^{−κt})²` solves the HW ODE under this θ, uniqueness (`hwMean`'s
lemma) gives the calibrated mean, and the calibration integral lemma
`∫₀ᵀ α = ∫₀ᵀ f0 + σ²V/2` (`hwCalibIntegratedMean`, via the kernel reflection
`hwVar_eq_interval`) makes `hw_reprices_curve` exact:
`P^hw(0,T) = exp(−∫₀ᵀ f(0,s) ds)`. No Fubini anywhere — pointwise congruences,
linearity, and one `intervalIntegral.integral_comp_sub_left` reflection.

This landing adds three explicit calibration lemmas: `hwMean_eq_forward` (the
mean identity at the minimal hypothesis `κ ≠ 0`, subsuming `hwCalibMean`),
`hwDeterministic_const_closed_form` (Vasicek's closed mean-reversion form for
constant θ — the honest shape of the HW→Vasicek reduction: constant forcing `Θ`
means long-run level `Θ/κ`, *not* forcing `Θ/κ`), and
`hwCalibCorrection_integral` (the convexity correction = `(σ²/2)·V(T)` in
isolation — exactly the quantity `hw_reprices_curve` cancels against the
Gaussian moment).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open MathFin WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### HW-1: the deterministic part -/

/-- **Hull–White deterministic (particular) solution** with `α(0) = r₀`:
`α(t) = e^{−κt}·(r₀ + ∫₀ᵗ e^{κs} θ(s) ds)`. For non-integrable `θ` the integral is
junk; every meaningful statement below states its hypotheses on `θ` explicitly. -/
noncomputable def hwDeterministic (θ : ℝ → ℝ) (κ r₀ t : ℝ) : ℝ :=
  Real.exp (-(κ * t)) * (r₀ + ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)

/-- **Initial condition**: `α(0) = r₀` (no hypotheses — the empty integral is 0). -/
lemma hwDeterministic_at_zero (θ : ℝ → ℝ) (κ r₀ : ℝ) :
    hwDeterministic θ κ r₀ 0 = r₀ := by
  simp [hwDeterministic, intervalIntegral.integral_same]

/-- **The HW ODE lemma** (generalizes `vasicekDeterministic_solves_ODE`): with θ
continuous, the particular solution satisfies `α'(t) = θ(t) − κ·α(t)` at every
point. Proof: FTC (`integral_hasDerivAt_right`) for the integral term + product
rule; `e^{−κt}·e^{κt} = 1` collapses the forcing term. -/
theorem hwDeterministic_solves_ODE (θ : ℝ → ℝ) (hθ : Continuous θ) (κ r₀ t : ℝ) :
    HasDerivAt (hwDeterministic θ κ r₀) (θ t - κ * hwDeterministic θ κ r₀ t) t := by
  have hfc : Continuous (fun s : ℝ ↦ Real.exp (κ * s) * θ s) := by fun_prop
  have hI : HasDerivAt (fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, Real.exp (κ * s) * θ s)
      (Real.exp (κ * t) * θ t) t :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 t)
      (hfc.stronglyMeasurableAtFilter volume (nhds t)) hfc.continuousAt
  have hexp1 : HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
      (Real.exp (-(κ * t)) * (-κ)) t := by
    have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ t := by
      simpa using (hasDerivAt_id t).const_mul κ
    exact hk.neg.exp
  have hprod := hexp1.mul (hI.const_add r₀)
  have hexpmul : Real.exp (-(κ * t)) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hval : (θ t - κ * hwDeterministic θ κ r₀ t)
      = Real.exp (-(κ * t)) * (-κ) * (r₀ + ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)
        + Real.exp (-(κ * t)) * (Real.exp (κ * t) * θ t) := by
    have hsplit : Real.exp (-(κ * t)) * (Real.exp (κ * t) * θ t) = θ t := by
      rw [← mul_assoc, hexpmul, one_mul]
    simp only [hwDeterministic, hsplit]
    ring
  rw [hval]
  exact hprod

/-- Scalar integral: `∫₀ᵗ e^{κs}·Θ ds = Θ·(e^{κt} − 1)/κ`. -/
lemma hwIntegral_exp_pos_const (Θ κ t : ℝ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * Θ = Θ * (Real.exp (κ * t) - 1) / κ := by
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ Θ * Real.exp (κ * s) / κ) (Real.exp (κ * s) * Θ) s := by
    intro s _
    have hk : HasDerivAt (fun s : ℝ ↦ κ * s) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    have h := ((hk.exp).const_mul Θ).div_const κ
    have hval : (Θ * (Real.exp (κ * s) * κ)) / κ = Real.exp (κ * s) * Θ := by
      field_simp
    rw [hval] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp

/-- **Constant θ reduces to Vasicek**: `hwDeterministic (fun _ ↦ Θ) κ r₀ t =
vasicekDeterministic r₀ (Θ/κ) κ t` — the HW drift `Θ − κr` is Vasicek's
`κ(θ_v − r)` with `θ_v = Θ/κ`, so every proved Vasicek result transfers. -/
lemma hwDeterministic_const (Θ κ r₀ t : ℝ) (hκ : κ ≠ 0) :
    hwDeterministic (fun _ ↦ Θ) κ r₀ t = vasicekDeterministic r₀ (Θ / κ) κ t := by
  have hint : ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * Θ
      = Θ * (Real.exp (κ * t) - 1) / κ := hwIntegral_exp_pos_const Θ κ t hκ
  have hexpmul : Real.exp (-(κ * t)) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [hwDeterministic, hint, vasicekDeterministic]
  field_simp [hexpmul]
  linear_combination Θ * hexpmul

/-- **Vasicek's closed form for constant θ**: `hwDeterministic (fun _ ↦ Θ) κ r₀ t
= Θ/κ + (r₀ − Θ/κ)·e^{−κt}` — the mean-reversion solution to level `θ_v = Θ/κ`
in explicit form (reached through the bridge `hwDeterministic_const`;
`vasicekDeterministic`'s definition body). This is the honest shape of the
HW→Vasicek reduction: constant HW forcing `Θ` is Vasicek with long-run mean
`Θ/κ` — *not* HW forcing `Θ/κ`, which would be Vasicek with mean `Θ/κ²`. -/
theorem hwDeterministic_const_closed_form (Θ κ r₀ t : ℝ) (hκ : κ ≠ 0) :
    hwDeterministic (fun _ ↦ Θ) κ r₀ t = Θ / κ + (r₀ - Θ / κ) * Real.exp (-(κ * t)) := by
  rw [hwDeterministic_const Θ κ r₀ t hκ]
  rfl

/-- **Mean reversion for constant θ**: the deterministic part tends to `Θ/κ`,
mirroring `vasicekDeterministic_tendsto_mean`. -/
theorem hwDeterministic_const_tendsto (Θ κ r₀ : ℝ) (hκ : 0 < κ) :
    Filter.Tendsto (hwDeterministic (fun _ ↦ Θ) κ r₀) Filter.atTop (nhds (Θ / κ)) := by
  have h : hwDeterministic (fun _ ↦ Θ) κ r₀ = vasicekDeterministic r₀ (Θ / κ) κ := by
    funext t
    exact hwDeterministic_const Θ κ r₀ t hκ.ne'
  rw [h]
  exact vasicekDeterministic_tendsto_mean r₀ (Θ / κ) κ hκ

/-- Linearity of the particular solution in the initial condition: raising the
initial rate by `a` shifts `α(t)` by `a·e^{−κt}` for every `t`. -/
lemma hwDeterministic_add_exponential (θ : ℝ → ℝ) (κ r₀ a t : ℝ) :
    hwDeterministic θ κ (r₀ + a) t
      = hwDeterministic θ κ r₀ t + a * Real.exp (-(κ * t)) := by
  simp only [hwDeterministic]
  ring

/-- **Uniqueness of the ODE solution**: any `α` satisfying `α'(s) = θ(s) − κ·α(s)`
at every point (θ continuous) with `α(0) = r₀` equals `hwDeterministic θ κ r₀`.
Proof: `F(s) = e^{κs}(α(s) − α_hw(s))` has `F' = 0` everywhere, hence `F ≡ 0`. -/
theorem hwDeterministic_eq_of_solves_ODE (θ : ℝ → ℝ) (hθ : Continuous θ) (κ : ℝ)
    (α : ℝ → ℝ) (hα : ∀ s, HasDerivAt α (θ s - κ * α s) s) (t : ℝ) :
    hwDeterministic θ κ (α 0) t = α t := by
  have hhwd : ∀ s : ℝ, HasDerivAt (hwDeterministic θ κ (α 0))
      (θ s - κ * hwDeterministic θ κ (α 0) s) s := fun s ↦
    hwDeterministic_solves_ODE θ hθ κ (α 0) s
  have hgap : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ α x - hwDeterministic θ κ (α 0) x)
      (-(κ * (α s - hwDeterministic θ κ (α 0) s))) s := by
    intro s
    have h := (hα s).sub (hhwd s)
    rw [show (θ s - κ * α s) - (θ s - κ * hwDeterministic θ κ (α 0) s)
        = -(κ * (α s - hwDeterministic θ κ (α 0) s)) from by ring] at h
    exact h
  have hF : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ ↦ Real.exp (κ * x) * (α x - hwDeterministic θ κ (α 0) x)) 0 s := by
    intro s
    have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    have h := (hk.exp).mul (hgap s)
    rw [show Real.exp (κ * s) * κ * (α s - hwDeterministic θ κ (α 0) s)
        + Real.exp (κ * s) * (-(κ * (α s - hwDeterministic θ κ (α 0) s))) = 0 from by
      ring] at h
    exact h
  have hint : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hF s) hint
  rw [intervalIntegral.integral_const] at hsub
  simp only [sub_zero, smul_zero, mul_zero, Real.exp_zero, one_mul] at hsub
  have hF0 : α 0 - hwDeterministic θ κ (α 0) 0 = 0 := by
    rw [hwDeterministic_at_zero]; ring
  rw [hF0, sub_zero] at hsub
  have hgap : α t - hwDeterministic θ κ (α 0) t = 0 := by
    refine mul_left_cancel₀ (Real.exp_ne_zero (κ * t)) ?_
    rw [mul_zero]
    exact hsub.symm
  exact (eq_of_sub_eq_zero hgap).symm

/-- **The mean of the HW short rate** (the desk identity, HW-2(b)): with any `α`
solving `α' = θ − κα` pointwise (θ continuous),
`𝔼[r_t] = α(t) + (r₀ − α(0))·e^{−κt}` — the particular solution plus the
exponentially decaying initial gap. -/
theorem hwMean (θ : ℝ → ℝ) (κ : ℝ) (α : ℝ → ℝ)
    (hα : ∀ s, HasDerivAt α (θ s - κ * α s) s) (hθ : Continuous θ) (r₀ t : ℝ) :
    hwDeterministic θ κ r₀ t = α t + (r₀ - α 0) * Real.exp (-(κ * t)) := by
  have hsplit : α 0 + (r₀ - α 0) = r₀ := by ring
  rw [show r₀ = α 0 + (r₀ - α 0) from hsplit.symm, hwDeterministic_add_exponential,
    hwDeterministic_eq_of_solves_ODE θ hθ κ α hα]
  ring

/-! ### HW-2: the short rate and its Gaussian law -/

/-- The HW diffusion kernel `e^{−κ(t−u)}` — the deterministic integrand of the
short rate's Wiener part `σ∫₀ᵗ e^{−κ(t−u)} dB_u`. -/
noncomputable def hwKernel (κ t : ℝ) : ℝ → ℝ := fun u ↦ Real.exp (-(κ * (t - u)))

/-- The kernel's L²-norm over `(0, t]`: `∫₀ᵗ e^{−2κ(t−u)} du = (1 − e^{−2κt})/(2κ)`
— exactly the Vasicek variance factor `/2κ`. -/
noncomputable def hwKernelV (κ t : ℝ) : ℝ := (1 - Real.exp (-(2 * κ * t))) / (2 * κ)

/-- The HW kernel is in `L²((0, t])`: on the support it lies in `(0, 1]` for
`κ > 0` (mirrors `vasicekIntegratedKernel_memLp` with bound `1`). -/
lemma hwKernel_memLp {κ : ℝ} (hκ : 0 < κ) (t : ℝ≥0) :
    MemLp (hwKernel κ (t : ℝ)) 2 (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
  refine (memLp_top_of_bound (by unfold hwKernel; fun_prop) 1 ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro u hu
  rw [hwKernel, Real.norm_eq_abs]
  have htu : 0 ≤ (t : ℝ) - u := by linarith [hu.2]
  rw [abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ.le htu])

/-- The HW kernel as an element of `L²((0, t])`. -/
noncomputable def hwKernelLp {κ : ℝ} (hκ : 0 < κ) (t : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) :=
  (hwKernel_memLp hκ t).toLp _

/-- **The variance-fixing integral** (mirrors `vasicekIntegratedKernel_integral_sq`):
`∫₀ᵗ e^{−2κ(t−u)} du = (1 − e^{−2κt})/(2κ)`, by the FTC with antiderivative
`F(u) = e^{−2κ(t−u)}/(2κ)`. -/
lemma hwKernel_integral_sq {κ : ℝ} (hκ : κ ≠ 0) (t : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (hwKernel κ (t : ℝ) u) ^ 2 ∂volume
      = hwKernelV κ (t : ℝ) := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (t : ℝ),
      HasDerivAt (fun u : ℝ ↦ Real.exp (-(2 * κ * ((t : ℝ) - u))) / (2 * κ))
        ((hwKernel κ (t : ℝ) u) ^ 2) u := by
    intro u _
    have hsq : Real.exp (-(2 * κ * ((t : ℝ) - u)))
        = (Real.exp (-(κ * ((t : ℝ) - u)))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have harg : HasDerivAt (fun u : ℝ ↦ -(2 * κ * ((t : ℝ) - u))) (2 * κ) u := by
      have h : HasDerivAt (fun u : ℝ ↦ -(2 * κ * ((t : ℝ) - u))) (-(2 * κ * (-1))) u := by
        apply HasDerivAt.neg
        apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id u).const_sub (t : ℝ)
      simpa using h
    have hcomb := harg.exp.div_const (2 * κ)
    have hval : Real.exp (-(2 * κ * ((t : ℝ) - u))) * (2 * κ) / (2 * κ)
        = (hwKernel κ (t : ℝ) u) ^ 2 := by
      rw [hsq, hwKernel]
      field_simp
    rw [hval] at hcomb
    exact hcomb
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; unfold hwKernel; fun_prop)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]
  rw [hwKernelV]
  ring

/-- `∫₀ᵗ kernel² = hwKernelV` for the `L²`-representative (a.e. the honest kernel). -/
private lemma hwKernelLp_integral_sq {κ : ℝ} (hκ : 0 < κ) (t : ℝ≥0) :
    (∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (hwKernelLp hκ t u) ^ 2 ∂volume)
      = hwKernelV κ (t : ℝ) := by
  rw [show (∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (hwKernelLp hκ t u) ^ 2 ∂volume)
        = ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (hwKernel κ (t : ℝ) u) ^ 2 ∂volume by
      refine integral_congr_ae ?_
      filter_upwards [(hwKernel_memLp hκ t).coeFn_toLp] with u hu
      rw [hwKernelLp, hu]]
  exact hwKernel_integral_sq hκ.ne' t

/-- `hwKernelV ≥ 0` (an integral of a square). -/
private lemma hwKernelV_nonneg {κ : ℝ} (hκ : 0 < κ) (t : ℝ≥0) :
    (0 : ℝ) ≤ hwKernelV κ (t : ℝ) := by
  rw [← hwKernelLp_integral_sq hκ t]
  exact integral_nonneg fun u ↦ sq_nonneg _

/-- The centred diffusion law for the HW kernel: `σ∫₀ᵗ e^{−κ(t−u)} dB_u`'s core is
centred Gaussian with variance `hwKernelV κ t` (mirrors the private
`vasicekWienerLaw` of the template). -/
private lemma hwKernelWienerLaw (hB : IsPreBrownianReal B μ) {κ : ℝ} (hκ : 0 < κ)
    (t : ℝ≥0) :
    HasLaw (fun ω ↦ wienerIntegralLp B hB t (hwKernelLp hκ t) ω)
      (gaussianReal 0 (hwKernelV κ (t : ℝ)).toNNReal) μ := by
  have h0 := wienerIntegralLp_hasLaw_gaussian hB t (hwKernelLp hκ t)
  rwa [hwKernelLp_integral_sq hκ t] at h0

/-- **The HW short rate in Wiener representation** (mirror of
`vasicekIntegratedRate`): `r_t = α(t) + σ·∫₀ᵗ e^{−κ(t−u)} dB_u` with `α` the
particular solution `hwDeterministic θ κ r₀`. -/
noncomputable def hwIntegratedRate (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  hwDeterministic θ κ r₀ (t : ℝ)
    + σ * (wienerIntegralLp B hB t (hwKernelLp hκ t) ω)

/-- **The HW short rate is Gaussian**: `r_t ~ N(α(t), σ²(1 − e^{−2κt})/(2κ))` —
θ(t) shifted the mean and left the Vasicek variance untouched (the affine-map
argument `x ↦ α(t) + σx` applied to the centred Wiener integral, exactly as in
`vasicekIntegratedRate_hasLaw_gaussian`). -/
theorem hwIntegratedRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    HasLaw (hwIntegratedRate hB θ κ σ r₀ hκ t)
      (gaussianReal (hwDeterministic θ κ r₀ (t : ℝ))
        ((σ ^ 2 * hwKernelV κ (t : ℝ)).toNNReal)) μ := by
  have hW := hwKernelWienerLaw hB hκ t
  have hV_nonneg : (0 : ℝ) ≤ hwKernelV κ (t : ℝ) := hwKernelV_nonneg hκ t
  have hShift := gaussianReal_const_add (gaussianReal_const_mul hW σ)
    (hwDeterministic θ κ r₀ (t : ℝ))
  convert hShift using 2
  · rfl
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hV_nonneg), NNReal.coe_mul,
      NNReal.coe_mk, Real.coe_toNNReal _ hV_nonneg]

/-! ### HW-3: the affine bond price -/

/-- The deterministic mean of the integrated HW short rate: `∫₀ᵗ α(s) ds`. -/
noncomputable def hwIntegratedMean (θ : ℝ → ℝ) (κ r₀ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, hwDeterministic θ κ r₀ s

/-- The Vasicek affine coefficient is the integrated diffusion kernel:
`∫₀ᵗ e^{−κs} ds = (1 − e^{−κt})/κ = vasicekBondB κ t` — the identity that makes
`B` carry over from Vasicek to HW verbatim. -/
lemma hwIntegral_exp_neg_eq_bondB (κ t : ℝ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(κ * s)) = vasicekBondB κ t := by
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ -Real.exp (-(κ * s)) / κ) (Real.exp (-(κ * s))) s := by
    intro s _
    have hk : HasDerivAt (fun s : ℝ ↦ κ * s) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    have hexpneg : HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
        (Real.exp (-(κ * s)) * (-κ)) s := by
      simpa using hk.neg.exp
    have h := hexpneg.neg.div_const κ
    have hval : -((Real.exp (-(κ * s)) * -κ)) / κ = Real.exp (-(κ * s)) := by
      field_simp
    rw [hval] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  rw [vasicekBondB]
  field_simp
  ring

/-- Continuity of the partial-solution integral `s ↦ ∫₀ˢ e^{κu}θ(u) du` (from the
FTC: it is differentiable, hence continuous). -/
private lemma hwI_continuous (θ : ℝ → ℝ) (hθ : Continuous θ) (κ : ℝ) :
    Continuous (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u) := by
  have hI : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)
      (Real.exp (κ * s) * θ s) s := by
    intro s
    have hfc : Continuous (fun u : ℝ ↦ Real.exp (κ * u) * θ u) := by fun_prop
    exact intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 s)
      (hfc.stronglyMeasurableAtFilter volume (nhds s)) hfc.continuousAt
  exact Differentiable.continuous (fun x ↦ (hI x).differentiableAt)

/-- **The forcing integral** (the HW-3 engine, antiderivative route — the pinned
Mathlib has no Fubini for interval integrals):
`∫₀ᵗ e^{−κs}·(∫₀ˢ e^{κu}θ(u) du) ds = (1/κ)·(∫₀ᵗ θ − e^{−κt}·∫₀ᵗ e^{κu}θ(u) du)`.
`G(s) = (1/κ)(∫₀ˢ θ − e^{−κs}·∫₀ˢ e^{κu}θ)` satisfies `G' = e^{−κs}·I(s)`,
`G(0) = 0`. -/
lemma hwBeta_integral (θ : ℝ → ℝ) (hθ : Continuous θ) (κ t : ℝ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)
      = (1 / κ) * ((∫ s in (0 : ℝ)..t, θ s)
          - Real.exp (-(κ * t)) * (∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)) := by
  have hI : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)
      (Real.exp (κ * s) * θ s) s := by
    intro s
    have hfc : Continuous (fun u : ℝ ↦ Real.exp (κ * u) * θ u) := by fun_prop
    exact intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 s)
      (hfc.stronglyMeasurableAtFilter volume (nhds s)) hfc.continuousAt
  have hD : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, θ u) (θ s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (hθ.intervalIntegrable 0 s)
      (hθ.stronglyMeasurableAtFilter volume (nhds s)) hθ.continuousAt
  have hE : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
      (Real.exp (-(κ * s)) * (-κ)) s := by
    intro s
    have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    exact hk.neg.exp
  have hG : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ ↦ (1 / κ) * ((∫ u in (0 : ℝ)..x, θ u)
        - Real.exp (-(κ * x)) * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)))
      (Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)) s := by
    intro s
    have hexpmul : Real.exp (-(κ * s)) * Real.exp (κ * s) = 1 := by
      rw [← Real.exp_add]; simp
    have h := ((hD s).sub ((hE s).mul (hI s))).const_mul (1 / κ)
    rw [← mul_assoc (Real.exp (-(κ * s))) (Real.exp (κ * s)) (θ s), hexpmul, one_mul] at h
    have hval : (1 / κ) * (θ s
        - (Real.exp (-(κ * s)) * -κ * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u) + θ s))
        = Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ Real.exp (-(κ * s))
        * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)) volume 0 t := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun x : ℝ ↦ Real.exp (-(κ * x)))).mul
      (hwI_continuous θ hθ κ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hG s) hint]
  have h0 : (1 / κ) * ((∫ u in (0 : ℝ)..0, θ u)
      - Real.exp (-(κ * 0)) * (∫ u in (0 : ℝ)..0, Real.exp (κ * u) * θ u)) = 0 := by
    simp [intervalIntegral.integral_same]
  rw [h0, sub_zero]

/-- The A-integral in split form: `∫₀ᵗ θ(s)·B(t−s) ds =
(1/κ)·(∫₀ᵗ θ − e^{−κt}·∫₀ᵗ e^{κs}θ(s) ds)` — pure pointwise algebra on
`B(τ) = (1 − e^{−κτ})/κ`, no Fubini. -/
lemma hwIntegral_theta_B (θ : ℝ → ℝ) (κ t : ℝ) (hθ : Continuous θ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s)
      = (1 / κ) * ((∫ s in (0 : ℝ)..t, θ s)
          - Real.exp (-(κ * t)) * (∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)) := by
  have hpt : ∀ s : ℝ, θ s * vasicekBondB κ (t - s)
      = (1 / κ) * θ s - (1 / κ) * (Real.exp (-(κ * t)) * (Real.exp (κ * s) * θ s)) := by
    intro s
    rw [vasicekBondB]
    have hrw : Real.exp (-(κ * (t - s))) = Real.exp (-(κ * t)) * Real.exp (κ * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hrw]
    field_simp
  rw [intervalIntegral.integral_congr
    (show EqOn (fun s : ℝ ↦ θ s * vasicekBondB κ (t - s))
      (fun s : ℝ ↦ (1 / κ) * θ s - (1 / κ) * (Real.exp (-(κ * t)) * (Real.exp (κ * s) * θ s)))
      (Set.uIcc (0 : ℝ) t) from fun s _ ↦ hpt s)]
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun s : ℝ ↦ (1 / κ) * θ s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (fun s : ℝ ↦ (1 / κ) * (Real.exp (-(κ * t))
      * (Real.exp (κ * s) * θ s)))).intervalIntegrable 0 t)]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- **Mean of the integrated HW rate in B-form**: `∫₀ᵗ α(s) ds = r₀·B(t) +
∫₀ᵗ θ(s)·B(t−s) ds` — the r₀-separation that makes A r₀-free (the affine content;
Vasicek's closed form `r₀·B + θ_v·(t − B)` is the constant-θ special case). -/
lemma hwIntegratedMean_eq (θ : ℝ → ℝ) (hθ : Continuous θ) (κ r₀ t : ℝ) (hκ : κ ≠ 0) :
    hwIntegratedMean θ κ r₀ t
      = r₀ * vasicekBondB κ t + ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s) := by
  have hsplit : ∀ s : ℝ, hwDeterministic θ κ r₀ s
      = r₀ * Real.exp (-(κ * s))
        + Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u) := by
    intro s
    simp only [hwDeterministic]
    rw [mul_add, mul_comm r₀ (Real.exp (-(κ * s)))]
  have hbeta : ∫ s in (0 : ℝ)..t,
      Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)
      = ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s) := by
    rw [hwBeta_integral θ hθ κ t hκ, hwIntegral_theta_B θ κ t hθ hκ]
  have hsplitint : ∫ x in (0 : ℝ)..t, hwDeterministic θ κ r₀ x ∂volume
      = ∫ x in (0 : ℝ)..t, (r₀ * Real.exp (-(κ * x))
        + Real.exp (-(κ * x)) * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)) ∂volume :=
    intervalIntegral.integral_congr (fun x _ ↦ hsplit x)
  have hadd : ∫ x in (0 : ℝ)..t, (r₀ * Real.exp (-(κ * x))
        + Real.exp (-(κ * x)) * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)) ∂volume
      = ∫ x in (0 : ℝ)..t, r₀ * Real.exp (-(κ * x)) ∂volume
        + ∫ x in (0 : ℝ)..t, Real.exp (-(κ * x))
          * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u) ∂volume := by
    refine intervalIntegral.integral_add ?_ ?_
    · exact (by fun_prop : Continuous
        (fun s : ℝ ↦ r₀ * Real.exp (-(κ * s)))).intervalIntegrable 0 t
    · exact ((by fun_prop : Continuous
        (fun x : ℝ ↦ Real.exp (-(κ * x)))).mul
        (hwI_continuous θ hθ κ)).intervalIntegrable 0 t
  rw [hwIntegratedMean, hsplitint, hadd, intervalIntegral.integral_const_mul,
    hwIntegral_exp_neg_eq_bondB κ t hκ, hbeta]

/-- **The integrated HW short rate** in Wiener representation (mirror of
`vasicekIntegratedRate`): `∫₀ᵗ r_s ds = ∫₀ᵗ α + σ·∫₀ᵗ g(u) dB_u` with `g` the
**Vasicek integrated kernel reused verbatim** (`vasicekIntegratedKernelLp`):
integrating the diffusion kernel `e^{−κ(s−u)}` over `s ∈ [u, T]` is
model-independent, so kernel, L²-element and variance all carry over. -/
noncomputable def hwBondRate (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (κ σ r₀ : ℝ)
    (hκ : 0 < κ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  hwIntegratedMean θ κ r₀ (T : ℝ)
    + σ * (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)

/-- `∫₀ᵀ g² = vasicekBondV κ T` for the `L²`-representative integrated kernel
(reconstructs the template's private `vasicekIntegratedKernelLp_integral_sq`
from public pieces). -/
private lemma hwVasKernelLp_integral_sq {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume)
      = vasicekBondV κ (T : ℝ) := by
  rw [show (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume)
        = ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernel κ T u) ^ 2 ∂volume by
      refine integral_congr_ae ?_
      filter_upwards [(vasicekIntegratedKernel_memLp hκ T).coeFn_toLp] with u hu
      rw [vasicekIntegratedKernelLp, hu]]
  exact vasicekIntegratedKernel_integral_sq hκ.ne' T

/-- `vasicekBondV ≥ 0` (an integral of a square; reconstructs the template's
private `vasicekBondV_nonneg`). -/
private lemma hwVasKernelV_nonneg {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    (0 : ℝ) ≤ vasicekBondV κ (T : ℝ) := by
  rw [← hwVasKernelLp_integral_sq hκ T]
  exact integral_nonneg fun u ↦ sq_nonneg _

/-- The centred Wiener law for the Vasicek integrated kernel (reconstructs the
template's private `vasicekWienerLaw`). -/
private lemma hwVasKernelWienerLaw (hB : IsPreBrownianReal B μ) {κ : ℝ} (hκ : 0 < κ)
    (T : ℝ≥0) :
    HasLaw (fun ω ↦ wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)
      (gaussianReal 0 (vasicekBondV κ (T : ℝ)).toNNReal) μ := by
  have h0 := wienerIntegralLp_hasLaw_gaussian hB T (vasicekIntegratedKernelLp hκ T)
  rwa [hwVasKernelLp_integral_sq hκ T] at h0

/-- **The HW zero-coupon bond price** — the exponential-Gaussian moment:
`P(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−∫₀ᵀ α + σ²·V(T)/2)` with `V = vasicekBondV`
the Vasicek variance, unchanged — the exact analogue of `vasicekBondPrice_eq`. -/
theorem hwBondPrice_eq (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (κ σ r₀ : ℝ)
    (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(hwBondRate hB θ κ σ r₀ hκ T ω)) ∂μ
      = Real.exp (-(hwIntegratedMean θ κ r₀ (T : ℝ))
          + σ ^ 2 * vasicekBondV κ (T : ℝ) / 2) := by
  set M : ℝ := hwIntegratedMean θ κ r₀ (T : ℝ) with hM
  set V : ℝ := vasicekBondV κ (T : ℝ) with hV
  have hV_nonneg : (0 : ℝ) ≤ V := hV ▸ hwVasKernelV_nonneg hκ T
  have hW : HasLaw (fun ω ↦ wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)
      (gaussianReal 0 V.toNNReal) μ := hV ▸ hwVasKernelWienerLaw hB hκ T
  -- Factor the integrand: exp(−(M + σW)) = exp(−M)·exp((−σ)·W).
  have hfactor : ∀ ω, Real.exp (-(hwBondRate hB θ κ σ r₀ hκ T ω))
      = Real.exp (-M) * Real.exp ((-σ) *
          (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)) := by
    intro ω
    rw [hwBondRate, ← hM, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [integral_const_mul,
    show (fun ω ↦ Real.exp ((-σ) * (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)))
        = (fun x ↦ Real.exp ((-σ) * x))
          ∘ (fun ω ↦ wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω) from rfl,
    hW.integral_comp (by fun_prop : AEStronglyMeasurable (fun x ↦ Real.exp ((-σ) * x))
      (gaussianReal 0 V.toNNReal)),
    integral_exp_mul_gaussianReal_zero (-σ) V.toNNReal,
    Real.coe_toNNReal _ hV_nonneg, ← Real.exp_add]
  congr 1
  ring

/-- The HW affine coefficient `A(T) = exp(−∫₀ᵀ θ(s)·B(T−s) ds + σ²·V(T)/2)` —
Vasicek's `vasicekBondA` with the constant-drift term `θ_v·(T − B(T))` replaced by
the θ-forcing integral. (`∫₀ᵀ B(T−s)² ds = vasicekBondV κ T`, so the variance
term is exactly `(σ²/2)·∫₀ᵀ B(τ)² dτ` — the mission's `A`-shape.) -/
noncomputable def hwBondA (θ : ℝ → ℝ) (σ κ t : ℝ) : ℝ :=
  Real.exp (-(∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s))
    + σ ^ 2 * vasicekBondV κ t / 2)

/-- **The affine term structure**: `P(0,T) = A(T)·exp(−B(T)·r₀)` with `B` the
Vasicek coefficient **verbatim** and `A` carrying the θ-forcing — the defining
shape of an affine term-structure model (the exact analogue of
`vasicekBondPrice_affine`). -/
theorem hwBondPrice_affine (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (κ σ r₀ : ℝ)
    (hθ : Continuous θ) (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(hwBondRate hB θ κ σ r₀ hκ T ω)) ∂μ
      = hwBondA θ σ κ (T : ℝ) * Real.exp (-(vasicekBondB κ (T : ℝ) * r₀)) := by
  rw [hwBondPrice_eq hB θ κ σ r₀ hκ T, hwBondA,
    hwIntegratedMean_eq θ hθ κ r₀ (T : ℝ) hκ.ne', ← Real.exp_add]
  congr 1
  ring

/-! ### HW-5: calibration — θ from the initial forward curve (lesson 0020, step 4) -/

/-- **The calibrated drift** (lesson 0020 step 4, the research addendum's verified
identity): `θ(t) = ∂_t f(0,t) + κ·f(0,t) + (σ²/2κ)·(1 − e^{−2κt})` — the initial
instantaneous forward curve's slope, plus mean reversion, plus the HJM convexity
correction. Defined with `deriv` (total, junk off-curve); every theorem below
binds `hf0 : ContDiff ℝ 1 f0`, which packages differentiability of `f0` and
continuity of `deriv f0` (`contDiff_one_iff_deriv`). -/
noncomputable def hwTheta (f0 : ℝ → ℝ) (κ σ : ℝ) (t : ℝ) : ℝ :=
  deriv f0 t + κ * f0 t + (σ ^ 2 / (2 * κ)) * (1 - Real.exp (-(2 * κ * t)))

/-- The calibrated particular solution in closed form: `β(t) = f(0,t) +
(σ²/2κ²)·(1 − e^{−κt})²` — the initial forward plus the convexity correction,
i.e. the calibrated expected short rate (lesson 0020 step 3's desk quantity). -/
noncomputable def hwCalibAlpha (f0 : ℝ → ℝ) (κ σ : ℝ) (t : ℝ) : ℝ :=
  f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * t))) ^ 2

/-- The pointwise algebra behind the calibrated ODE: with `E = e^{−κt}`,
`(1 − E²) − (1 − E)² = 2E(1 − E)` — the identity that converts the `−2κt`
exponent of the θ-formula into the `(1 − e^{−κt})²` of β. -/
private lemma hwCalib_deriv_eq (d v E κ σ : ℝ) (hκ : κ ≠ 0) :
    d + (σ ^ 2 / (2 * κ ^ 2)) * (2 * (1 - E) * (κ * E))
      = d + κ * v + (σ ^ 2 / (2 * κ)) * (1 - E ^ 2)
        - κ * (v + (σ ^ 2 / (2 * κ ^ 2)) * (1 - E) ^ 2) := by
  field_simp
  ring

/-- `hwTheta` is continuous for a `C¹` curve — `deriv f0` is continuous by
`contDiff_one_iff_deriv`. -/
lemma hwTheta_continuous (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) :
    Continuous (hwTheta f0 κ σ) := by
  obtain ⟨_, hdd⟩ := contDiff_one_iff_deriv.mp hf0
  exact (hdd.add (hf0.continuous.const_mul κ)).add
    (by fun_prop : Continuous fun t : ℝ ↦ (σ ^ 2 / (2 * κ)) * (1 - Real.exp (-(2 * κ * t))))

/-- **The calibrated β solves the HW ODE** (the research addendum's identity,
verified by differentiation): with `f0` a `C¹` curve,
`β(t) = f(0,t) + (σ²/2κ²)(1 − e^{−κt})²` satisfies
`β'(t) = θ(t) − κ·β(t)` pointwise for `θ = hwTheta f0 κ σ`. Chain rule on β plus
`hwCalib_deriv_eq`; this is what makes the θ-formula *the* calibration. -/
theorem hwCalibAlpha_solves_ODE (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ)
    (hκ : κ ≠ 0) (t : ℝ) :
    HasDerivAt (hwCalibAlpha f0 κ σ) (hwTheta f0 κ σ t - κ * hwCalibAlpha f0 κ σ t) t := by
  have hfd : HasDerivAt f0 (deriv f0 t) t := (hf0.differentiable_one t).hasDerivAt
  have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ t := by
    simpa using (hasDerivAt_id t).const_mul κ
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
      (Real.exp (-(κ * t)) * (-κ)) t := hk.neg.exp
  have hsub : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-(κ * x)))
      (κ * Real.exp (-(κ * t))) t := by
    have h0 := (hasDerivAt_const t 1).sub hexp
    rwa [show (0 : ℝ) - Real.exp (-(κ * t)) * (-κ)
        = κ * Real.exp (-(κ * t)) from by ring] at h0
  have hsq : HasDerivAt (fun x : ℝ ↦ (1 - Real.exp (-(κ * x))) ^ 2)
      (2 * (1 - Real.exp (-(κ * t))) * (κ * Real.exp (-(κ * t)))) t := by
    have h0 := hsub.mul hsub
    rw [show κ * Real.exp (-(κ * t)) * (1 - Real.exp (-(κ * t)))
          + (1 - Real.exp (-(κ * t))) * (κ * Real.exp (-(κ * t)))
          = 2 * (1 - Real.exp (-(κ * t))) * (κ * Real.exp (-(κ * t))) from by ring] at h0
    exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ pow_two _)
  have hcm : HasDerivAt
      (fun x : ℝ ↦ (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * x))) ^ 2)
      ((σ ^ 2 / (2 * κ ^ 2)) * (2 * (1 - Real.exp (-(κ * t)))
          * (κ * Real.exp (-(κ * t))))) t := hsq.const_mul (σ ^ 2 / (2 * κ ^ 2))
  have hE2 : Real.exp (-(2 * κ * t)) = Real.exp (-(κ * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hval : hwTheta f0 κ σ t - κ * hwCalibAlpha f0 κ σ t
      = deriv f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (2 * (1 - Real.exp (-(κ * t)))
          * (κ * Real.exp (-(κ * t)))) := by
    simp only [hwTheta, hwCalibAlpha, hE2]
    exact (hwCalib_deriv_eq (deriv f0 t) (f0 t) (Real.exp (-(κ * t))) κ σ hκ).symm
  rw [hval]
  exact hfd.add hcm

/-- **The mean identity** (lesson 0020 step 3's desk quantity under calibration;
the calibration build's deliverable 1): the HW particular solution driven by
`hwTheta` and started at the initial forward `r₀ = f(0,0)` is exactly
`β(t) = f(0,t) + (σ²/2κ²)(1 − e^{−κt})²` — the initial forward plus the convexity
correction, so the expected short rate is the forward curve plus a known,
explicitly integrable correction. Route: `hwCalibAlpha_solves_ODE` (verified by
differentiation) + ODE uniqueness (`hwDeterministic_eq_of_solves_ODE`; note
`β(0) = f(0,0)` automatically, since `(1 − e^{−κ·0})² = 0`). Only `κ ≠ 0` is
needed — the θ-formula divides by κ; no positivity enters the deterministic
identity. -/
theorem hwMean_eq_forward (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : κ ≠ 0) (t : ℝ) :
    hwDeterministic (hwTheta f0 κ σ) κ (f0 0) t
      = f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * t))) ^ 2 := by
  have h := hwDeterministic_eq_of_solves_ODE (hwTheta f0 κ σ)
    (hwTheta_continuous f0 hf0 κ σ) κ (hwCalibAlpha f0 κ σ)
    (fun s ↦ hwCalibAlpha_solves_ODE f0 hf0 κ σ hκ s) t
  rwa [show hwCalibAlpha f0 κ σ 0 = f0 0 from by simp [hwCalibAlpha]] at h

/-- The calibrated mean at the `0 < κ` hypothesis (the original landing name,
kept for the consumers below and in the lesson text) — `hwMean_eq_forward`
specialized. -/
theorem hwCalibMean (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ) :
    hwDeterministic (hwTheta f0 κ σ) κ (f0 0) t
      = f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * t))) ^ 2 :=
  hwMean_eq_forward f0 hf0 κ σ hκ.ne' t

/-- **The mean identity at the law level**: `𝔼[r_t] = f(0,t) +
(σ²/2κ²)(1 − e^{−κt})²` — the expected HW short rate under calibration is the
initial forward plus the convexity correction (the centred Gaussian part
contributes zero: `hwIntegratedRate_hasLaw_gaussian` +
`integral_id_gaussianReal`). -/
theorem hwCalibMean_eq_forward (hB : IsPreBrownianReal B μ) (f0 : ℝ → ℝ)
    (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    ∫ ω, hwIntegratedRate hB (hwTheta f0 κ σ) κ σ (f0 0) hκ t ω ∂μ
      = f0 (t : ℝ) + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * (t : ℝ)))) ^ 2 := by
  have hlaw := hwIntegratedRate_hasLaw_gaussian hB (hwTheta f0 κ σ) κ σ (f0 0) hκ t
  rw [hlaw.integral_eq, integral_id_gaussianReal,
    hwCalibMean f0 hf0 κ σ hκ (t : ℝ)]

/-- **The variance identity for calibration**: `V(T) = ∫₀ᵀ B(u)² du` in interval
form. Route: `vasicekIntegratedKernel_integral_sq` gives the `Ioc`-integral of
the integrated kernel `g(u) = B(T−u)`; `intervalIntegral.integral_of_le` moves to
interval form, the integrand is `vasicekBondB κ (T−u)` definitionally, and the
reflection `∫₀ᵀ φ(u) du = ∫₀ᵀ φ(T−u) du` (`integral_comp_sub_left`) lands on
`B(u)` — the L²-norm is symmetric under `u ↦ T−u`. -/
lemma hwVar_eq_interval (κ : ℝ) (hκ : κ ≠ 0) (𝕋 : ℝ≥0) :
    vasicekBondV κ (𝕋 : ℝ) = ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ u) ^ 2 := by
  have href : ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ u) ^ 2
      = ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ ((𝕋 : ℝ) - u)) ^ 2 := by
    rw [intervalIntegral.integral_comp_sub_left
      (f := fun u : ℝ ↦ (vasicekBondB κ u) ^ 2) (𝕋 : ℝ)]
    simp
  have h2 := vasicekIntegratedKernel_integral_sq hκ 𝕋
  have h3 : (∫ u in Set.Ioc (0 : ℝ) (𝕋 : ℝ),
      (vasicekIntegratedKernel κ (𝕋 : ℝ) u) ^ 2 ∂volume)
      = ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekIntegratedKernel κ (𝕋 : ℝ) u) ^ 2 ∂volume :=
    (intervalIntegral.integral_of_le 𝕋.prop).symm
  rw [← h2, h3, intervalIntegral.integral_congr
    (show EqOn (fun u : ℝ ↦ (vasicekIntegratedKernel κ (𝕋 : ℝ) u) ^ 2)
      (fun u : ℝ ↦ (vasicekBondB κ ((𝕋 : ℝ) - u)) ^ 2) (Set.uIcc (0 : ℝ) (𝕋 : ℝ))
      from fun u _ ↦ rfl)]
  exact href.symm

/-- The κ²-scaling bridge: `κ²·∫₀ᵀ B(u)² du = ∫₀ᵀ (1 − e^{−κu})² du` — pure
pointwise algebra on `B(u) = (1 − e^{−κu})/κ`. -/
private lemma hwCalibVar_key (κ : ℝ) (hκ : κ ≠ 0) (𝕋 : ℝ≥0) :
    κ ^ 2 * (∫ s in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ s) ^ 2)
      = ∫ s in (0 : ℝ)..(𝕋 : ℝ), (1 - Real.exp (-(κ * s))) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr
    (show EqOn (fun s : ℝ ↦ κ ^ 2 * (vasicekBondB κ s) ^ 2)
      (fun s : ℝ ↦ (1 - Real.exp (-(κ * s))) ^ 2) (Set.uIcc (0 : ℝ) (𝕋 : ℝ))
      from fun s _ ↦ ?_)
  show κ ^ 2 * ((1 - Real.exp (-(κ * s))) / κ) ^ 2 = (1 - Real.exp (-(κ * s))) ^ 2
  field_simp

/-- **The convexity-correction integral in isolation**:
`∫₀ᵀ (σ²/2κ²)(1 − e^{−κs})² ds = (σ²/2)·V(T)` — the mean-correction term of
`hwMean_eq_forward`, integrated, equals half the integrated-rate variance: the
exact quantity the Gaussian bond moment's `σ²V/2` cancels, which is why
`hw_reprices_curve` is exact (`hwCalibIntegratedMean` = `∫₀ᵀ f0` + this). -/
theorem hwCalibCorrection_integral (κ σ : ℝ) (hκ : κ ≠ 0) (𝕋 : ℝ≥0) :
    ∫ s in (0 : ℝ)..(𝕋 : ℝ), (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * s))) ^ 2
      = σ ^ 2 / 2 * vasicekBondV κ (𝕋 : ℝ) := by
  rw [intervalIntegral.integral_const_mul (r := (σ ^ 2 / (2 * κ ^ 2)))
      (f := fun s : ℝ ↦ (1 - Real.exp (-(κ * s))) ^ 2),
    ← hwCalibVar_key κ hκ 𝕋, ← hwVar_eq_interval κ hκ 𝕋]
  field_simp

/-- **The calibrated integrated mean**: `∫₀ᵀ α(s) ds = ∫₀ᵀ f(0,s) ds +
(σ²/2)·V(T)` — the forward-discount integral plus half the integrated-rate
variance. This is the identity the repricing exactness lives on: the convexity
correction in the mean exactly offsets the `σ²V/2` in the Gaussian moment. -/
theorem hwCalibIntegratedMean (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ)
    (hκ : 0 < κ) (𝕋 : ℝ≥0) :
    hwIntegratedMean (hwTheta f0 κ σ) κ (f0 0) (𝕋 : ℝ)
      = (∫ s in (0 : ℝ)..(𝕋 : ℝ), f0 s) + σ ^ 2 / 2 * vasicekBondV κ (𝕋 : ℝ) := by
  have hV := hwVar_eq_interval κ hκ.ne' 𝕋
  have hfa : IntervalIntegrable f0 volume (0 : ℝ) (𝕋 : ℝ) :=
    hf0.continuous.intervalIntegrable _ _
  have hgb : IntervalIntegrable (fun s : ℝ ↦ (σ ^ 2 / (2 * κ ^ 2))
      * (1 - Real.exp (-(κ * s))) ^ 2) volume (0 : ℝ) (𝕋 : ℝ) :=
    (by fun_prop : Continuous fun s : ℝ ↦ (σ ^ 2 / (2 * κ ^ 2))
      * (1 - Real.exp (-(κ * s))) ^ 2).intervalIntegrable _ _
  have hsplit : ∫ s in (0 : ℝ)..(𝕋 : ℝ),
      (f0 s + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * s))) ^ 2)
      = (∫ s in (0 : ℝ)..(𝕋 : ℝ), f0 s)
        + (σ ^ 2 / (2 * κ ^ 2)) * (∫ s in (0 : ℝ)..(𝕋 : ℝ), (1 - Real.exp (-(κ * s))) ^ 2) := by
    refine Eq.trans (intervalIntegral.integral_add hfa hgb) ?_
    rw [← intervalIntegral.integral_const_mul (r := (σ ^ 2 / (2 * κ ^ 2)))
      (f := fun s : ℝ ↦ (1 - Real.exp (-(κ * s))) ^ 2)]
  have hkey : (σ ^ 2 / (2 * κ ^ 2)) * (∫ s in (0 : ℝ)..(𝕋 : ℝ), (1 - Real.exp (-(κ * s))) ^ 2)
      = σ ^ 2 / 2 * (∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ u) ^ 2) := by
    rw [← hwCalibVar_key κ hκ.ne' 𝕋]
    field_simp
  unfold hwIntegratedMean
  rw [intervalIntegral.integral_congr
    (show EqOn (fun s : ℝ ↦ hwDeterministic (hwTheta f0 κ σ) κ (f0 0) s)
      (fun s : ℝ ↦ f0 s + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * s))) ^ 2)
      (Set.uIcc (0 : ℝ) (𝕋 : ℝ)) from fun s _ ↦ hwCalibMean f0 hf0 κ σ hκ s),
    hsplit, hkey, ← hV]

/-- **The repricing identity** (lesson 0020 step 4, the headline): with θ defined
by the verified calibration formula, the HW model's initial bond curve exactly
reprices the market curve read off the initial forwards:
`P^hw(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−∫₀ᵀ f(0,s) ds) = P^mkt(0,T)`.
Route: `hwBondPrice_eq` (the exponential-Gaussian moment) +
`hwCalibIntegratedMean` (`∫₀ᵀ α = ∫₀ᵀ f0 + σ²V/2`) — the `σ²V/2` cancels. -/
theorem hw_reprices_curve (hB : IsPreBrownianReal B μ) (f0 : ℝ → ℝ)
    (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(hwBondRate hB (hwTheta f0 κ σ) κ σ (f0 0) hκ T ω)) ∂μ
      = Real.exp (-(∫ s in (0 : ℝ)..(T : ℝ), f0 s)) := by
  rw [hwBondPrice_eq hB (hwTheta f0 κ σ) κ σ (f0 0) hκ T,
    hwCalibIntegratedMean f0 hf0 κ σ hκ T]
  congr 1
  ring

/-! ### HW-4: audit -/

#print axioms hwDeterministic_solves_ODE
#print axioms hwDeterministic_const_tendsto
#print axioms hwDeterministic_eq_of_solves_ODE
#print axioms hwMean
#print axioms hwIntegratedRate_hasLaw_gaussian
#print axioms hwBondPrice_eq
#print axioms hwBondPrice_affine
#print axioms hwCalibAlpha_solves_ODE
#print axioms hwTheta_continuous
#print axioms hwCalibMean
#print axioms hwCalibMean_eq_forward
#print axioms hwVar_eq_interval
#print axioms hwCalibIntegratedMean
#print axioms hw_reprices_curve
#print axioms hwDeterministic_const_closed_form
#print axioms hwMean_eq_forward
#print axioms hwCalibCorrection_integral

import Mathlib
import MathFin.Foundations.PoissonCounting
import MathFin.Foundations.PoissonInterarrival
import MathFin.FixedIncome.CDSTimeVarying

/-!
# Tier-1 build: Cox-intensity credit (lesson 0032)

The upgrade from deterministic hazard curves to stochastic intensity, per lesson
0032's four-step plan, reusing the proved Poisson layer and the deterministic CDS
formulas — with the filtration scope drawn honestly.

## The model (restricted Cox, per lesson 0032)

An intensity `λ(t) ≥ 0`, cumulative intensity `Λ(t) = ∫₀ᵗ λ`, default time `τ`
= first arrival. Everything reduces to two facts:

* **survival**: `P(τ > t) = e^{−Λ(t)}`;
* **density pricing**: `E[e^{−rτ} 1{τ ≤ T}] = ∫₀ᵀ e^{−rs} λ(s) e^{−Λ(s)} ds`.

A CDS prices as premium leg (`c · risky annuity`) vs protection leg
(`(1−R) · default-density integral`), and the fair spread equates them.

## What is built (layer by layer)

* **Layer 1 — counting/first-arrival substrate (consumed, not re-proved).** The
  pin's `PoissonInterarrival.survival_eq` and
  `PoissonInterarrival.map_firstArrival_eq_expMeasure` already prove, from the
  bare counting axioms, `P(N_t = 0) = e^{−rate·t}` and `τ ∼ Exp(rate)`. The
  credit reading is packaged as `defaultSurvival_const` / `defaultTimeLaw_const`
  (one rewrite each — the build here is the consumption interface, exactly as
  the plan anticipates). The alternative route via the count law
  (`PoissonCounting.map_count_eq_poissonMeasure`, line 191 at the pin — lesson
  0032 Exercise 1's derivation) is imported and recorded but not duplicated.

* **Layer 2 — constant intensity: the two legs in closed form.**
  `riskyAnnuity` (the discount × survival kernel at constant `λ`) has the closed
  form `(1 − e^{−(r+λ)T})/(r+λ)` (`riskyAnnuity_eq`), is positive for `T > 0`,
  and the **protection leg is the hazard times the same annuity**
  (`protectionLeg_const`). `cdsLegs_balance_const` then realizes the pin's
  abstract leg-equality `cds_leg_equality` with the *concrete integral* as the
  annuity factor: the fair spread is `cdsFairSpread λ R = λ(1−R)` — the
  constant-`λ` regression test of lesson 0032 step 3.

* **Layer 3 — deterministic time-varying intensity: the survival identity.**
  With `h : ℝ → ℝ` continuous, strictly positive (for all calendar time), and
  divergent cumulative `Λ = MathFin.cumHazard h`, a unit-exponential clock
  `ξ ∼ Exp(1)` inverted through `Λ` builds a default time with
  `P(τ > t) = e^{−Λ(t)}` (`cox_survival_timeVarying`) and
  `P(τ ≤ a) = 1 − e^{−Λ(a)}` (`cox_cdf_timeVarying`) — the honest
  deterministic-`λ(t)` intermediate of build step 3. The mechanism is a.e. set
  equality: `{τ > t}` and `{ξ > Λ t}` differ only on the null set `{ξ < 0}`, so
  no inverse continuity or inverse measurability is ever needed (there is no
  `Monotone.invFun` continuity API at this pin — the a.e. route dodges it
  entirely).

* **Layer 4 — the CDS upgrade (the headline).** The risky annuity and the
  default-density (protection) integrals under `λ(t)`: `cdsAnnuity`,
  `cdsLosses`; both legs as explicit definitions (`premiumLeg`,
  `protectionLeg`); the balance theorem `cdsFairSpread_TV_balances` — premium
  leg = protection leg iff `c = (1−R)·losses/annuity` — instantiating the pin's
  `cdsFairSpread_TV_cash_flow_balance` at the *concrete integrals*, with the
  annuity-positivity hypothesis discharged (`cdsAnnuity_pos`). The
  **constant-`λ` regression** `cdsFairSpread_TV_const` collapses the
  time-varying spread to `cdsFairSpread λ R`. The density-pricing identity
  lands at `r = 0`: the constructed default time satisfies
  `P(τ ≤ a) = ∫₀^a h·S` (`cox_defaultProb_density`) — the integral of the
  default density equals the default probability, via
  `defaultDensity_antideriv` and `clockTail_eq_defaultDensity` (the
  clock-change identity `∫₀^{Λa} e^{−y} dy = ∫₀^a h e^{−Λ}`, proved by FTC on
  the shared antiderivative `−e^{−Λ}` — no change-of-variables lemma needed).

* **Layer 5 — restricted Cox mixing (stretch, landed).** On the product of a
  path space with the exponential-clock space, the joint measure of the
  survival event `{(path, clock) : clock > Λ(path, t)}` equals the path-average
  of the pathwise survivals `e^{−Λ(path, t)}` (`cox_mixing_survival`) — the
  tower identity `E[E[1{τ>t} | path]] = E[e^{−Λ_t}]` at the Fubini level, with
  the intensity a *random* cumulative process. `cox_mixed_survival` packages it
  as the survival of a default time defined on the product (its per-path
  construction hypothesis is the honest scoping fence, see below).

## Scope fences (documented, per lesson 0032 step 4)

* **Filtration enlargement is out of scope**: in restricted Cox the *same*
  filtration carries the intensity and the compensator; the general Cox case
  (τ's own information entering `F`) is Tier-2. Nothing here conditions on
  survival.
* **The conditional-expectation σ-algebra statement** — `E[1{τ>t} | σ(path)]`
  as a `condExp` object — is replaced by its Fubini (iterated-integral)
  content, which is what pricing consumes. The Doob–Dynkin upgrade needs the
  per-path inverse construction on the product space (each path's `Λ(ω)` is a
  homeomorphism of the half-line, so the construction is routine but its Lean
  measurability plumbing is the remaining gap).
* **The discounted density identity** `E[e^{−rτ}1{τ≤T}] = ∫₀ᵀ e^{−rs} h S ds`
  for `r > 0` needs generalized-inverse continuity (for the substitution
  `y = Λ(s)` inside the integrand) — the `r = 0` case needs no inverse and is
  landed.
* **The measure-change layer** for `λ_t = λ(S_t)`: the pin's
  `GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted` and
  `GirsanovPredictableTheta.isExpQMartingale_BthetaPredictable` are the proved
  predictable-θ Girsanov machinery the driven-intensity case consumes; not
  exercised in this build (steps 1–4 do not require it).

## Stack consumed (pin 784a831, all grep-verified)

`PoissonInterarrival.survival_eq` / `.survival_factorizes` /
`.map_firstArrival_eq_expMeasure`; `PoissonCounting.map_count_eq_poissonMeasure`;
`Credit.survivalProbability` / `.creditSpread_eq_hazard` / `.cdsFairSpread` /
`.cds_leg_equality` (via `FixedIncome.CDS` re-export);
`HazardCurve.cumHazard` / `.hazardSurvival` / `.hazardSurvival_pos` /
`.hazardSurvival_eq_const_survival`;
`CDSTimeVarying.cdsFairSpread_TV_cash_flow_balance`;
`ExponentialDiscount.cumulativeIntensity` / `.survivalFromIntensity`;
Mathlib: `cdf_expMeasure_eq`, `poissonMeasure_singleton`, `Measure.prod_apply`,
`intervalIntegral.integral_pos`, `intervalIntegral.integral_congr`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt`,
`intervalIntegral.integral_add_adjacent_intervals`,
`intermediate_value_Icc`, `Function.invFun_eq`,
`strictMono_of_hasDerivAt_pos`, `HasDerivAt.differentiableAt`.
-/

open MeasureTheory ProbabilityTheory Real MathFin
open scoped NNReal ENNReal

namespace Cox

/-! ## Layer 1 — the counting/first-arrival substrate, in credit variables -/

section Layer1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Survival of the default time under constant intensity** — the credit
reading of the pin's first-arrival survival law: under a rate-`rate` Poisson
counting process, a default time `τ` characterized by `τ > t ↔ N_t = 0` has
`P(τ > t) = e^{−rate·t}`. Consumes `PoissonInterarrival.survival_eq`. -/
theorem defaultSurvival_const {rate : ℝ≥0} {N : ℝ → Ω → ℕ}
    (hmeas : ∀ t, Measurable (N t)) (hzero : ∀ ω, N 0 ω = 0)
    (hincr : ∀ ⦃s t : ℝ⦄, 0 ≤ s → (hst : s ≤ t) →
      Measure.map (fun ω ↦ N t ω - N s ω) μ
        = poissonMeasure (rate * ⟨t - s, sub_nonneg.mpr hst⟩))
    {_τ : Ω → ℝ} (_hτmeas : Measurable _τ) (_hτnn : ∀ ω, 0 ≤ _τ ω)
    (hτfirst : ∀ ⦃t : ℝ⦄, 0 ≤ t → {ω | t < _τ ω} = {ω | N t ω = 0})
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < _τ ω} = ENNReal.ofReal (rexp (-((rate : ℝ) * t))) := by
  rw [hτfirst ht]
  exact PoissonInterarrival.survival_eq hmeas hzero hincr ht

/-- **Law of the default time under constant intensity**: the first arrival is
exponentially distributed — `τ ∼ Exp(rate)`. Consumes
`PoissonInterarrival.map_firstArrival_eq_expMeasure`. -/
theorem defaultTimeLaw_const [IsProbabilityMeasure μ] {rate : ℝ≥0} (hrate : 0 < rate)
    {N : ℝ → Ω → ℕ}
    (hmeas : ∀ t, Measurable (N t)) (hzero : ∀ ω, N 0 ω = 0)
    (hincr : ∀ ⦃s t : ℝ⦄, 0 ≤ s → (hst : s ≤ t) →
      Measure.map (fun ω ↦ N t ω - N s ω) μ
        = poissonMeasure (rate * ⟨t - s, sub_nonneg.mpr hst⟩))
    {τ : Ω → ℝ} (hτmeas : Measurable τ) (hτnn : ∀ ω, 0 ≤ τ ω)
    (hτfirst : ∀ ⦃t : ℝ⦄, 0 ≤ t → {ω | t < τ ω} = {ω | N t ω = 0}) :
    μ.map τ = expMeasure rate :=
  PoissonInterarrival.map_firstArrival_eq_expMeasure hrate hmeas hzero hincr
    hτmeas hτnn hτfirst

end Layer1

/-! ## Layer 2 — constant intensity: the two CDS legs in closed form -/

/-- The **risky annuity** at constant intensity `lam` and discount rate `r`:
`∫₀ᵀ e^{−rs} e^{−lam·s} ds`. -/
noncomputable def riskyAnnuity (r lam T : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..T, rexp (-((r + lam) * s))

/-- Closed form: `∫₀ᵀ e^{−(r+lam)s} ds = (1 − e^{−(r+lam)T}) / (r+lam)`. -/
theorem riskyAnnuity_eq (r lam T : ℝ) (hne : r + lam ≠ 0) :
    riskyAnnuity r lam T = (1 - rexp (-((r + lam) * T))) / (r + lam) := by
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ ↦ -rexp (-((r + lam) * u)) / (r + lam))
      (rexp (-((r + lam) * s))) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ ↦ (r + lam) * u) (r + lam) s :=
      by simpa using (hasDerivAt_id s).const_mul (r + lam)
    have h2 : HasDerivAt (fun u : ℝ ↦ rexp (-((r + lam) * u)))
        (rexp (-((r + lam) * s)) * -(r + lam)) s := (h1.neg).exp
    have h2' := h2.neg
    have hv : (-(rexp (-((r + lam) * s)) * -(r + lam)))
        = rexp (-((r + lam) * s)) * (r + lam) := by ring
    rw [hv] at h2'
    have h4 := h2'.div_const (r + lam)
    have hv3 : rexp (-((r + lam) * s)) * (r + lam) / (r + lam) = rexp (-((r + lam) * s)) := by
      field_simp
    rwa [hv3] at h4
  have hint : IntervalIntegrable (fun s ↦ rexp (-((r + lam) * s))) volume 0 T :=
    ((continuous_const.mul continuous_id).neg.rexp).intervalIntegrable 0 T
  rw [riskyAnnuity, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ key s) hint, mul_zero]
  simp only [neg_zero, Real.exp_zero]
  field_simp
  ring

/-- The risky annuity is positive for positive maturity (the integrand is
strictly positive everywhere). -/
theorem riskyAnnuity_pos (r lam T : ℝ) (hT : 0 < T) : 0 < riskyAnnuity r lam T := by
  have hfc : ContinuousOn (fun s : ℝ ↦ rexp (-((r + lam) * s))) (Set.Icc 0 T) :=
    (continuous_const.mul continuous_id).neg.rexp.continuousOn
  rw [riskyAnnuity]
  exact intervalIntegral.integral_pos hT hfc (fun x _ ↦ le_of_lt (Real.exp_pos _))
    ⟨T / 2, ⟨by linarith, by linarith⟩, Real.exp_pos _⟩

/-- **Protection leg in closed form at constant intensity**: `(1−R) · ∫₀ᵀ e^{−rs} ·
(lam e^{−lam·s}) ds = (1−R) · lam · riskyAnnuity` — the default density
`lam·e^{−lam·s}` is the hazard times the survival, and it shares the annuity's
kernel. -/
theorem protectionLeg_const (r lam R T : ℝ) :
    (1 - R) * ∫ s in (0:ℝ)..T, rexp (-(r * s)) * (lam * rexp (-(lam * s)))
      = (1 - R) * lam * riskyAnnuity r lam T := by
  have hpt : ∀ s : ℝ, rexp (-(r * s)) * (lam * rexp (-(lam * s)))
      = lam * rexp (-((r + lam) * s)) := by
    intro s
    rw [mul_left_comm, ← Real.exp_add]
    congr 1
    ring
  rw [intervalIntegral.integral_congr
      (f := fun s : ℝ ↦ rexp (-(r * s)) * (lam * rexp (-(lam * s))))
      (g := fun s : ℝ ↦ lam * rexp (-((r + lam) * s))) (fun s _ ↦ hpt s),
    intervalIntegral.integral_const_mul, riskyAnnuity]
  ring

/-- **Leg balance at constant intensity** — the abstract annuity-factor
characterization `MathFin.cds_leg_equality` realized at the concrete integral:
the premium leg `c · riskyAnnuity` equals the protection leg
`(1−R) · lam · riskyAnnuity` iff the spread is `cdsFairSpread lam R = lam(1−R)`. -/
theorem cdsLegs_balance_const (r lam R T c : ℝ) (hT : 0 < T) :
    c * riskyAnnuity r lam T = (1 - R) * lam * riskyAnnuity r lam T
      ↔ c = cdsFairSpread lam R :=
  cds_leg_equality lam R (riskyAnnuity r lam T) c
    (ne_of_gt (riskyAnnuity_pos r lam T hT))

/-- The fair spread balances the legs (the "if" direction of the balance,
regression-tested against the pin's `cdsFairSpread`). -/
theorem cdsFairSpread_const_balances (r lam R T : ℝ) (hT : 0 < T) :
    cdsFairSpread lam R * riskyAnnuity r lam T = (1 - R) * lam * riskyAnnuity r lam T := by
  rw [cdsLegs_balance_const r lam R T (cdsFairSpread lam R) hT]

/-! ## Layer 3 — deterministic time-varying intensity: the survival identity

All identities in this section hold for an arbitrary base measure `μ` (in the
credit model `μ` is a probability measure; nothing below needs it). The
exponential-clock facts carry their own `IsProbabilityMeasure (expMeasure 1)`
instances. -/

section Layer3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The survival function of the time-varying-hazard model is the exponential
of the (negative) cumulative hazard — `hazardSurvival` unfolds to it. -/
lemma hazardSurvival_eq_exp (h : ℝ → ℝ) (t : ℝ) :
    hazardSurvival h t = rexp (-(cumHazard h t)) := rfl

/-- The cumulative hazard vanishes at 0. -/
lemma cumHazard_zero (h : ℝ → ℝ) : cumHazard h 0 = 0 := by
  exact intervalIntegral.integral_same

/-- The cumulative hazard is nonnegative on the half-line under a positive
intensity. -/
lemma cumHazard_nonneg {h : ℝ → ℝ} (hpos : ∀ s, 0 < h s) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cumHazard h t :=
  intervalIntegral.integral_nonneg ht fun s _ ↦ le_of_lt (hpos s)

/-- Fundamental theorem of calculus for the cumulative hazard: `Λ' = h`. -/
theorem cumHazard_deriv {h : ℝ → ℝ} (hh : Continuous h) (s : ℝ) :
    HasDerivAt (cumHazard h) (h s) s :=
  intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 s)
    (hh.stronglyMeasurableAtFilter _ _) hh.continuousAt

/-- Continuity of the cumulative hazard (via its differentiability). -/
theorem cumHazard_continuous {h : ℝ → ℝ} (hh : Continuous h) : Continuous (cumHazard h) :=
  Differentiable.continuous fun s => (cumHazard_deriv hh s).differentiableAt

/-- Under a strictly positive hazard intensity (for all calendar time) the
cumulative hazard is strictly increasing. -/
theorem cumHazard_strictMono {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ s, 0 < h s) :
    StrictMono (cumHazard h) :=
  strictMono_of_hasDerivAt_pos (fun s => cumHazard_deriv hh s) hpos

/-- Under a divergent cumulative hazard, `Λ` maps the half-line onto the
half-line (IVT from `Λ 0 = 0` and `Λ → ∞`). -/
theorem cumHazard_surjOn_Ici {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) (y : ℝ) (hy : 0 ≤ y) :
    ∃ s : ℝ, 0 ≤ s ∧ cumHazard h s = y := by
  have h0 := cumHazard_zero h
  obtain ⟨T, hTy⟩ : ∃ T : ℝ, y ≤ cumHazard h T :=
    (Filter.Tendsto.eventually_ge_atTop hdiv y).exists
  have hT0 : 0 ≤ T := by
    by_contra hTneg
    have hTneg' : T < 0 := not_le.mp hTneg
    have hlt : cumHazard h T < cumHazard h 0 := cumHazard_strictMono hh hpos hTneg'
    rw [cumHazard_zero] at hlt
    linarith
  have hIVT := intermediate_value_Icc (a := (0:ℝ)) (b := T) hT0
    (cumHazard_continuous hh).continuousOn
  obtain ⟨s, hsIcc, hsΛ⟩ := hIVT ⟨by rw [h0]; exact hy, hTy⟩
  exact ⟨s, hsIcc.1, hsΛ⟩

/-- **CDF of the unit exponential clock**: for `ν = Exp(1)` and `x ≥ 0`,
`ν(−∞, x] = 1 − e^{−x}`. -/
private theorem expClock_Iic {x : ℝ} (hx : 0 ≤ x) :
    expMeasure 1 (Set.Iic x) = ENNReal.ofReal (1 - rexp (-x)) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _),
    show ENNReal.toReal (expMeasure 1 (Set.Iic x)) = cdf (expMeasure 1) x from by
      rw [cdf_eq_real, measureReal_def],
    cdf_expMeasure_eq one_pos x, if_pos hx]
  simp only [one_mul]

/-- **Tail of the unit exponential clock**: for `ν = Exp(1)` and `x ≥ 0`,
`ν(x, ∞) = e^{−x}`. -/
private theorem expClock_Ioi {x : ℝ} (hx : 0 ≤ x) :
    expMeasure 1 (Set.Ioi x) = ENNReal.ofReal (rexp (-x)) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hset : Set.Ioi x = (Set.Iic x)ᶜ := by
    ext y
    simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_Iic, not_le]
  have hnn : 0 ≤ 1 - rexp (-x) := by
    have hle : rexp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  rw [hset, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    expClock_Iic hx, show ((1:ℝ≥0∞)) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub 1 hnn]
  congr 1
  ring

/-- The unit exponential clock is almost surely positive. -/
theorem expClock_null_neg {ξ : Ω → ℝ} (hξmeas : Measurable ξ)
    (hξlaw : Measure.map ξ μ = expMeasure 1) : μ {ω | ξ ω < 0} = 0 := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [show {ω | ξ ω < 0} = ξ ⁻¹' Set.Iio 0 from rfl,
    ← Measure.map_apply hξmeas measurableSet_Iio, hξlaw]
  refine le_antisymm
    (le_trans (measure_mono (show {y : ℝ | y < 0} ⊆ Set.Iic 0 from Set.Iio_subset_Iic_self)) ?_)
    zero_le
  rw [expClock_Iic le_rfl]
  norm_num

/-- Almost-sure nonnegativity of the clock. -/
theorem expClock_nonneg_ae {ξ : Ω → ℝ} (hξmeas : Measurable ξ)
    (hξlaw : Measure.map ξ μ = expMeasure 1) : ∀ᵐ ω ∂μ, 0 ≤ ξ ω := by
  rw [ae_iff]
  simp only [not_le]
  exact expClock_null_neg hξmeas hξlaw

/-- **The Cox default time (deterministic-intensity layer)**: invert a
unit-exponential clock through the cumulative hazard `Λ`. -/
noncomputable def coxDefaultTime (h : ℝ → ℝ) (ξ : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ Function.invFun (cumHazard h) (ξ ω)

/-- The inverse of `Λ` inverts exactly on the half-line, and lands there. -/
private theorem invFun_on_halfline {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {y : ℝ} (hy : 0 ≤ y) :
    cumHazard h (Function.invFun (cumHazard h) y) = y
      ∧ 0 ≤ Function.invFun (cumHazard h) y := by
  obtain ⟨s, hs0, hsΛ⟩ := cumHazard_surjOn_Ici hh hpos hdiv y hy
  have heq : cumHazard h (Function.invFun (cumHazard h) y) = y :=
    Function.invFun_eq ⟨s, hsΛ⟩
  refine ⟨heq, ?_⟩
  by_contra hneg
  have hneg' : Function.invFun (cumHazard h) y < 0 := not_le.mp hneg
  have hlt : cumHazard h (Function.invFun (cumHazard h) y) < cumHazard h 0 :=
    cumHazard_strictMono hh hpos hneg'
  rw [heq, cumHazard_zero] at hlt
  linarith

/-- The clock survival event, a.e.: `{τ > t} = {ξ > Λ t}` (for every `t`; the
pointwise equivalence needs no sign bound, only the global strict monotonicity
and the half-line inversion). -/
private theorem coxDefaultTime_survSet {h : ℝ → ℝ} (hh : Continuous h)
    (hpos : ∀ s, 0 < h s) (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop)
    {ξ : Ω → ℝ} (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1)
    (t : ℝ) :
    {ω | coxDefaultTime h ξ ω > t} =ᵐ[μ] {ω | cumHazard h t < ξ ω} := by
  have hpt : ∀ ω : Ω, 0 ≤ ξ ω → (coxDefaultTime h ξ ω > t ↔ cumHazard h t < ξ ω) := by
    intro ω hω
    obtain ⟨hinv_eq, -⟩ := invFun_on_halfline hh hpos hdiv hω
    unfold coxDefaultTime
    constructor
    · intro hgt
      calc ξ ω = cumHazard h (Function.invFun (cumHazard h) (ξ ω)) := hinv_eq.symm
        _ > cumHazard h t := cumHazard_strictMono hh hpos (by linarith)
    · intro hlt
      by_contra hcon
      have hle : cumHazard h (Function.invFun (cumHazard h) (ξ ω)) ≤ cumHazard h t :=
        (cumHazard_strictMono hh hpos).monotone (by linarith)
      rw [hinv_eq] at hle
      linarith
  filter_upwards [expClock_nonneg_ae hξmeas hξlaw] with ω hω
  exact propext (hpt ω hω)

/-- The clock CDF event, a.e.: `{τ ≤ a} = {ξ ≤ Λ a}` (for every `a`). -/
private theorem coxDefaultTime_cdfSet {h : ℝ → ℝ} (hh : Continuous h)
    (hpos : ∀ s, 0 < h s) (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop)
    {ξ : Ω → ℝ} (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1)
    (a : ℝ) :
    {ω | coxDefaultTime h ξ ω ≤ a} =ᵐ[μ] {ω | ξ ω ≤ cumHazard h a} := by
  have hpt : ∀ ω : Ω, 0 ≤ ξ ω → (coxDefaultTime h ξ ω ≤ a ↔ ξ ω ≤ cumHazard h a) := by
    intro ω hω
    obtain ⟨hinv_eq, -⟩ := invFun_on_halfline hh hpos hdiv hω
    unfold coxDefaultTime
    constructor
    · intro hle
      rw [hinv_eq.symm]
      exact (cumHazard_strictMono hh hpos).monotone hle
    · intro hle
      by_contra hcon
      have hlt : cumHazard h (Function.invFun (cumHazard h) (ξ ω)) > cumHazard h a :=
        cumHazard_strictMono hh hpos (by linarith)
      rw [hinv_eq] at hlt
      linarith
  filter_upwards [expClock_nonneg_ae hξmeas hξlaw] with ω hω
  exact propext (hpt ω hω)

/-- **The Cox survival identity, deterministic-intensity layer.** With `h`
continuous, strictly positive, and `∫₀ᵗ h → ∞`, the default time built by
inverting a unit-exponential clock through `Λ = cumHazard h` satisfies
`P(τ > t) = e^{−Λ(t)} = hazardSurvival h t` — the mixing of
`PoissonInterarrival.survival_eq` at a deterministic time-varying intensity
(build step 3 of lesson 0032, honest intermediate). -/
theorem cox_survival_timeVarying {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop)
    {ξ : Ω → ℝ} (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | coxDefaultTime h ξ ω > t} = ENNReal.ofReal (hazardSurvival h t) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hΛt : 0 ≤ cumHazard h t := cumHazard_nonneg hpos ht
  rw [measure_congr (coxDefaultTime_survSet hh hpos hdiv hξmeas hξlaw t),
    show {ω | cumHazard h t < ξ ω} = ξ ⁻¹' Set.Ioi (cumHazard h t) from rfl,
    ← Measure.map_apply hξmeas measurableSet_Ioi, hξlaw, expClock_Ioi hΛt]
  rfl

/-- **The Cox CDF identity, deterministic-intensity layer**: the same model
satisfies `P(τ ≤ a) = 1 − e^{−Λ(a)}`. -/
theorem cox_cdf_timeVarying {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop)
    {ξ : Ω → ℝ} (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1)
    {a : ℝ} (ha : 0 ≤ a) :
    μ {ω | coxDefaultTime h ξ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hΛa : 0 ≤ cumHazard h a := cumHazard_nonneg hpos ha
  rw [measure_congr (coxDefaultTime_cdfSet hh hpos hdiv hξmeas hξlaw a),
    show {ω | ξ ω ≤ cumHazard h a} = ξ ⁻¹' Set.Iic (cumHazard h a) from rfl,
    ← Measure.map_apply hξmeas measurableSet_Iic, hξlaw, expClock_Iic hΛa,
    show ((1:ℝ≥0∞)) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub 1 (le_of_lt (hazardSurvival_pos h a))]
  rfl

end Layer3

/-! ## Layer 4 — the CDS upgrade: legs and fair spread under λ(t) -/

section Layer4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Continuity of the time-varying survival function (h continuous). -/
private theorem hazardSurvival_continuous {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (hazardSurvival h) :=
  (cumHazard_continuous hh).neg.rexp

/-- The **risky annuity** (premium-leg kernel) under deterministic intensity
`h`: `∫₀ᵀ e^{−rs} S(s) ds` with `S = hazardSurvival h`. -/
noncomputable def cdsAnnuity (r : ℝ) (h : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..T, rexp (-(r * s)) * hazardSurvival h s

/-- The **default-density integral** (protection-leg kernel) under
deterministic intensity `h`: `∫₀ᵀ e^{−rs} h(s) S(s) ds`. -/
noncomputable def cdsLosses (r : ℝ) (h : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..T, rexp (-(r * s)) * h s * hazardSurvival h s

/-- The **premium leg** at spread `c`. -/
noncomputable def premiumLeg (c r : ℝ) (h : ℝ → ℝ) (T : ℝ) : ℝ := c * cdsAnnuity r h T

/-- The **protection leg** at recovery `R`. -/
noncomputable def protectionLeg (R r : ℝ) (h : ℝ → ℝ) (T : ℝ) : ℝ :=
  (1 - R) * cdsLosses r h T

/-- The **time-varying fair spread**: `(1−R) · losses / annuity`. -/
noncomputable def cdsFairSpread_TV (r : ℝ) (h : ℝ → ℝ) (R T : ℝ) : ℝ :=
  (1 - R) * cdsLosses r h T / cdsAnnuity r h T

/-- The risky annuity is positive for `T > 0` (discount × survival is strictly
positive; `S > 0` unconditionally by `hazardSurvival_pos`). -/
theorem cdsAnnuity_pos {r : ℝ} {h : ℝ → ℝ} (hh : Continuous h) {T : ℝ} (hT : 0 < T) :
    0 < cdsAnnuity r h T := by
  have hfc : ContinuousOn (fun s : ℝ ↦ rexp (-(r * s)) * hazardSurvival h s)
      (Set.Icc 0 T) :=
    (((continuous_const.mul continuous_id).neg.rexp).mul
      (hazardSurvival_continuous hh)).continuousOn
  rw [cdsAnnuity]
  exact intervalIntegral.integral_pos hT hfc
    (fun x _ ↦ mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (hazardSurvival_pos h x)))
    ⟨0, ⟨le_refl 0, hT.le⟩, by rw [hazardSurvival_at_zero]; norm_num⟩

/-- **The default density integrates to the default probability** (pure
calculus): `∫₀^a h·S = 1 − S(a)` — the antiderivative of `h·S` is `−S`. -/
theorem defaultDensity_antideriv {h : ℝ → ℝ} (hh : Continuous h) (a : ℝ) :
    ∫ s in (0:ℝ)..a, h s * rexp (-(cumHazard h s)) = 1 - rexp (-(cumHazard h a)) := by
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ ↦ -rexp (-(cumHazard h u)))
      (h s * rexp (-(cumHazard h s))) s := by
    intro s
    have h2 : HasDerivAt (fun u : ℝ ↦ rexp (-(cumHazard h u)))
        (rexp (-(cumHazard h s)) * -(h s)) s := (cumHazard_deriv hh s).neg.exp
    have h3 := h2.neg
    have h4 : (-(rexp (-(cumHazard h s)) * -(h s)))
        = h s * rexp (-(cumHazard h s)) := by ring
    rwa [h4] at h3
  have hint : IntervalIntegrable (fun s : ℝ ↦ h s * rexp (-(cumHazard h s))) volume 0 a :=
    (hh.mul (hazardSurvival_continuous hh)).intervalIntegrable 0 a
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ key s) hint, cumHazard_zero]
  norm_num [Real.exp_zero]
  ring

/-- **The clock-change identity**: `∫₀^{Λ(a)} e^{−y} dy = ∫₀^a h(s) e^{−Λ(s)} ds`
— the exponential-clock integral equals the default-density integral. FTC on
the shared antiderivative `−e^{−Λ}`; no change-of-variables lemma needed. -/
theorem clockTail_eq_defaultDensity {h : ℝ → ℝ} (hh : Continuous h) (a : ℝ) :
    ∫ y in (0:ℝ)..(cumHazard h a), rexp (-y)
      = ∫ s in (0:ℝ)..a, h s * rexp (-(cumHazard h s)) := by
  have key : ∀ y : ℝ, HasDerivAt (fun u : ℝ ↦ -rexp (-u)) (rexp (-y)) y := by
    intro y
    have h1 : HasDerivAt (fun u : ℝ ↦ -u) (-1) y := (hasDerivAt_id y).neg
    have h2 := h1.exp
    have hv : rexp (-y) * -1 = -rexp (-y) := by ring
    rw [hv] at h2
    have h3 := h2.neg
    rw [show (-(-rexp (-y))) = rexp (-y) from by ring] at h3
    exact h3
  have hint : IntervalIntegrable (fun y : ℝ ↦ rexp (-y)) volume 0 (cumHazard h a) :=
    ((continuous_id.neg).rexp).intervalIntegrable 0 (cumHazard h a)
  rw [show (∫ y in (0:ℝ)..(cumHazard h a), rexp (-y)) = 1 - rexp (-(cumHazard h a)) from by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ key y) hint]
      norm_num [Real.exp_zero]
      ring,
    defaultDensity_antideriv hh a]

/-- **Balance of the CDS legs under a time-varying intensity** (the headline):
the premium leg equals the protection leg iff the spread is the time-varying
fair spread `(1−R) · losses / annuity` — the pin's abstract cash-flow balance
`cdsFairSpread_TV_cash_flow_balance` realized at the concrete integrals, with
annuity-positivity discharged. -/
theorem cdsFairSpread_TV_balances {r : ℝ} {h : ℝ → ℝ} (hh : Continuous h) {T : ℝ}
    (hT : 0 < T) (c R : ℝ) :
    premiumLeg c r h T = protectionLeg R r h T ↔ c = cdsFairSpread_TV r h R T := by
  unfold premiumLeg protectionLeg cdsFairSpread_TV
  exact cdsFairSpread_TV_cash_flow_balance c R _ _ (ne_of_gt (cdsAnnuity_pos hh hT))

/-- At constant intensity the time-varying annuity is the Layer-2 risky
annuity (the survival curve specializes via `hazardSurvival_eq_const_survival`). -/
theorem cdsAnnuity_eq_riskyAnnuity (r lam T : ℝ) :
    cdsAnnuity r (fun _ ↦ lam) T = riskyAnnuity r lam T := by
  have hpt : ∀ s : ℝ, rexp (-(r * s)) * hazardSurvival (fun _ ↦ lam) s
      = rexp (-((r + lam) * s)) := by
    intro s
    have hS : hazardSurvival (fun _ ↦ lam) s = rexp (-(lam * (s - 0))) := by
      rw [hazardSurvival_eq_const_survival]
      rfl
    rw [hS, sub_zero, ← Real.exp_add]
    congr 1
    ring
  rw [cdsAnnuity, riskyAnnuity, intervalIntegral.integral_congr
    (f := fun s : ℝ ↦ rexp (-(r * s)) * hazardSurvival (fun _ ↦ lam) s)
    (g := fun s : ℝ ↦ rexp (-((r + lam) * s))) (fun s _ ↦ hpt s)]

/-- At constant intensity the default-density integral is the hazard times the
annuity — the Layer-2 protection-leg closed form. -/
theorem cdsLosses_eq_riskyAnnuity_mul (r lam T : ℝ) :
    cdsLosses r (fun _ ↦ lam) T = lam * riskyAnnuity r lam T := by
  have hpt : ∀ s : ℝ, rexp (-(r * s)) * (fun _ ↦ lam) s * hazardSurvival (fun _ ↦ lam) s
      = lam * rexp (-((r + lam) * s)) := by
    intro s
    have hS : hazardSurvival (fun _ ↦ lam) s = rexp (-(lam * (s - 0))) := by
      rw [hazardSurvival_eq_const_survival]
      rfl
    rw [hS, sub_zero]
    show rexp (-(r * s)) * lam * rexp (-(lam * s)) = lam * rexp (-((r + lam) * s))
    rw [mul_comm (rexp (-(r * s))) lam, mul_assoc, ← Real.exp_add]
    congr 1
    ring
  rw [cdsLosses, riskyAnnuity, intervalIntegral.integral_congr
    (f := fun s : ℝ ↦ rexp (-(r * s)) * (fun _ ↦ lam) s * hazardSurvival (fun _ ↦ lam) s)
    (g := fun s : ℝ ↦ lam * rexp (-((r + lam) * s))) (fun s _ ↦ hpt s),
    intervalIntegral.integral_const_mul]

/-- **The constant-`λ` regression test** (lesson 0032, build step 3 / Answer 3):
the time-varying fair spread at a constant intensity collapses to the pin's
constant-hazard fair spread `cdsFairSpread lam R = lam(1−R)`. -/
theorem cdsFairSpread_TV_const (r lam R T : ℝ) (hT : 0 < T) :
    cdsFairSpread_TV r (fun _ ↦ lam) R T = cdsFairSpread lam R := by
  have hA : riskyAnnuity r lam T ≠ 0 :=
    ne_of_gt (riskyAnnuity_pos r lam T hT)
  unfold cdsFairSpread_TV
  rw [cdsAnnuity_eq_riskyAnnuity, cdsLosses_eq_riskyAnnuity_mul,
    show cdsFairSpread lam R = lam * (1 - R) from rfl, div_eq_iff hA]
  ring

/-- **The density-pricing identity at zero discount** (deterministic-intensity
Cox): the constructed default time satisfies
`P(τ ≤ a) = ∫₀^a h·S` — the default probability is the integral of the default
density. The `r > 0` case (needs generalized-inverse continuity for the
substitution inside the integrand) is the documented remaining gap. -/
theorem cox_defaultProb_density {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop)
    {ξ : Ω → ℝ} (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1)
    {a : ℝ} (ha : 0 ≤ a) :
    μ {ω | coxDefaultTime h ξ ω ≤ a}
      = ENNReal.ofReal (∫ s in (0:ℝ)..a, h s * hazardSurvival h s) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [cox_cdf_timeVarying hh hpos hdiv hξmeas hξlaw ha,
    show ((1:ℝ≥0∞)) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub 1 (le_of_lt (hazardSurvival_pos h a))]
  congr 1
  exact (defaultDensity_antideriv hh a).symm

end Layer4

/-! ## Layer 5 — restricted Cox: the mixing identity (stretch, landed) -/

section Mixing

variable {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁}

/-- **The restricted-Cox mixing identity** (lesson 0032, build step 2 at the
Fubini level). On the product of an intensity-path space with the
unit-exponential-clock space, the joint measure of the survival event
`{(path, clock) : Λ(path, t) < clock}` equals the path-average of the pathwise
survivals: `E[E[1{τ > t} | path]] = E[e^{−Λ_t}]`. The intensity here is a
*random* cumulative process, nonnegative pathwise; only the measurability of
its time sections is needed. -/
theorem cox_mixing_survival {Λ : ℝ → Ω₁ → ℝ} (hΛmeas : ∀ t, Measurable fun ω => Λ t ω)
    (hΛnn : ∀ t ω, 0 ≤ Λ t ω) (t : ℝ) :
    (μ₁.prod (expMeasure 1)) {p : Ω₁ × ℝ | Λ t p.1 < p.2}
      = ∫⁻ ω : Ω₁, ENNReal.ofReal (rexp (-(Λ t ω))) ∂μ₁ := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hmap : Measurable fun p : Ω₁ × ℝ => (Λ t p.1, p.2) :=
    ((hΛmeas t).comp measurable_fst).prodMk measurable_snd
  have hset : MeasurableSet {p : Ω₁ × ℝ | Λ t p.1 < p.2} :=
    hmap (measurableSet_lt measurable_fst measurable_snd)
  rw [Measure.prod_apply hset]
  refine lintegral_congr fun ω => ?_
  have hpre : Prod.mk ω ⁻¹' {p : Ω₁ × ℝ | Λ t p.1 < p.2} = Set.Ioi (Λ t ω) := by
    ext y
    simp
  rw [hpre]
  exact expClock_Ioi (hΛnn t ω)

/-- The mixed survival event is a probability (`≤ 1`) — `e^{−Λ} ∈ [0,1]`
pathwise. -/
theorem cox_mixing_survival_le {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₁]
    {Λ : ℝ → Ω₁ → ℝ} (hΛmeas : ∀ t, Measurable fun ω => Λ t ω)
    (hΛnn : ∀ t ω, 0 ≤ Λ t ω) (t : ℝ) :
    (μ₁.prod (expMeasure 1)) {p : Ω₁ × ℝ | Λ t p.1 < p.2} ≤ 1 := by
  calc (μ₁.prod (expMeasure 1)) {p : Ω₁ × ℝ | Λ t p.1 < p.2}
      = ∫⁻ ω : Ω₁, ENNReal.ofReal (rexp (-(Λ t ω))) ∂μ₁ :=
        cox_mixing_survival hΛmeas hΛnn t
    _ ≤ ∫⁻ _ : Ω₁, (1:ℝ≥0∞) ∂μ₁ := by
        refine lintegral_mono fun ω => ?_
        have hle : rexp (-(Λ t ω)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by have := hΛnn t ω; linarith)
        calc ENNReal.ofReal (rexp (-(Λ t ω))) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
          _ = 1 := ENNReal.ofReal_one
    _ = 1 := by rw [lintegral_one, measure_univ]

/-- **Mixed survival of a restricted-Cox default time**: a default time `τ` on
the product space whose survival event is (pointwise) the clock beating the
pathwise compensator has survival `P(τ > t) = E[e^{−Λ_t}]`. The per-path
construction of such a `τ` (invert each path's `Λ(ω)`, a homeomorphism of the
half-line) is the documented remaining step of the restricted-Cox scoping. -/
theorem cox_mixed_survival {τ : Ω₁ × ℝ → ℝ} {Λ : ℝ → Ω₁ → ℝ}
    (hΛmeas : ∀ t, Measurable fun ω => Λ t ω)
    (hΛnn : ∀ t ω, 0 ≤ Λ t ω)
    {t : ℝ} (hτ : ∀ p : Ω₁ × ℝ, t < τ p ↔ Λ t p.1 < p.2) :
    (μ₁.prod (expMeasure 1)) {p : Ω₁ × ℝ | t < τ p}
      = ∫⁻ ω : Ω₁, ENNReal.ofReal (rexp (-(Λ t ω))) ∂μ₁ := by
  have hset : {p : Ω₁ × ℝ | t < τ p} = {p : Ω₁ × ℝ | Λ t p.1 < p.2} := by
    ext p
    exact hτ p
  rw [hset]
  exact cox_mixing_survival hΛmeas hΛnn t

end Mixing

end Cox

#print axioms Cox.defaultSurvival_const
#print axioms Cox.defaultTimeLaw_const
#print axioms Cox.riskyAnnuity_eq
#print axioms Cox.riskyAnnuity_pos
#print axioms Cox.protectionLeg_const
#print axioms Cox.cdsLegs_balance_const
#print axioms Cox.cdsFairSpread_const_balances
#print axioms Cox.cumHazard_strictMono
#print axioms Cox.cumHazard_surjOn_Ici
#print axioms Cox.cox_survival_timeVarying
#print axioms Cox.cox_cdf_timeVarying
#print axioms Cox.cdsAnnuity_pos
#print axioms Cox.defaultDensity_antideriv
#print axioms Cox.clockTail_eq_defaultDensity
#print axioms Cox.cdsFairSpread_TV_balances
#print axioms Cox.cdsFairSpread_TV_const
#print axioms Cox.cox_defaultProb_density
#print axioms Cox.cox_mixing_survival
#print axioms Cox.cox_mixing_survival_le
#print axioms Cox.cox_mixed_survival

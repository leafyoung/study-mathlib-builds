import Mathlib
import MathFin.FixedIncome.VasicekBondPrice

/-!
# The affine engine, stage 1: exponential-affine invariance for the OU/Vasicek generator

Scratch development for lesson 0033 (`0033-tier2-affine-engine-cir.md`): the tangency check
that makes exponential-affine functions invariant for an affine diffusion, in the
one-dimensional OU/Vasicek case

`dX_t = (a - κ X_t) dt + σ dW_t`.

Everything here is pure Mathlib: no probability, only the deterministic observation that
applying the generator `ouGenerator a κ σ` to a member `expAffine φ ψ` of the
exponential-affine family returns `x ↦ (c₀ + c₁ x) * expAffine φ ψ x` with the bracket
affine in `x`. This is the right-hand side of Bagaria ch. 14, eqs. 14.4–14.6: matching
powers of `x` against `μ = a + bx`, `v = c + dx` turns the pricing PDE into the Riccati
system `ψ' = bψ + ½dψ²`, `φ' = aψ + ½cψ²` (here `b = -κ`, `d = σ²`, `c = 0`).

Stage 2 (Riccati ODE solutions) consumes `ouBracket_affine`; the derivative helpers
`hasDerivAt_affine`, `hasDerivAt_expAffine`, `deriv_expAffine`, `deriv_deriv_expAffine`
are reusable substrate.

House-style anchors: `MathFin/Foundations/MarketMakingRiccati.lean` (`hasDerivAt_tanh`,
`hasDerivAt_riccatiCoeff`), Mathlib `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`
(`Real.hasDerivAt_exp`, `HasDerivAt.exp`).
-/

/-- The exponential-affine family `x ↦ e^(φ + ψ x)` (Bagaria ch. 14, eq. 14.4). -/
noncomputable def expAffine (φ ψ x : ℝ) : ℝ := Real.exp (φ + ψ * x)

/-- The one-dimensional affine (OU/Vasicek) generator
`Lf = (a - κ x) f' + (σ²/2) f''`. -/
noncomputable def ouGenerator (a κ σ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (a - κ * x) * deriv f x + (σ ^ 2 / 2) * deriv (deriv f) x

/-! ### Derivative helpers for the exponential-affine family -/

/-- The affine inner function `y ↦ φ + ψ * y` has derivative `ψ`. -/
theorem hasDerivAt_affine (φ ψ x : ℝ) : HasDerivAt (fun y => φ + ψ * y) ψ x := by
  have h : HasDerivAt (fun y => ψ * y) ψ x := by
    simpa using (hasDerivAt_id x).const_mul ψ
  exact HasDerivAt.const_add φ h

/-- Chain rule instance: `e^(φ + ψ ·)` has derivative `ψ * e^(φ + ψ x)`
(Mathlib's `HasDerivAt.exp`). -/
theorem hasDerivAt_expAffine (φ ψ x : ℝ) :
    HasDerivAt (expAffine φ ψ) (Real.exp (φ + ψ * x) * ψ) x :=
  (hasDerivAt_affine φ ψ x).exp

/-- First derivative of the exponential-affine family: `ψ * e^(φ + ψ x)`. -/
theorem deriv_expAffine (φ ψ : ℝ) :
    deriv (expAffine φ ψ) = fun x => ψ * expAffine φ ψ x := by
  funext x
  simp only [expAffine]
  have h : deriv (expAffine φ ψ) x = Real.exp (φ + ψ * x) * ψ :=
    (hasDerivAt_affine φ ψ x).exp.deriv
  rw [h]
  ring

/-- Bridge form with the right-hand side unfolded (used once, to compute the second
derivative). -/
theorem deriv_expAffine_mul (φ ψ : ℝ) :
    deriv (expAffine φ ψ) = fun x => Real.exp (φ + ψ * x) * ψ := by
  funext x
  exact (hasDerivAt_expAffine φ ψ x).deriv

/-- Second derivative of the exponential-affine family: `ψ² * e^(φ + ψ x)`. -/
theorem deriv_deriv_expAffine (φ ψ : ℝ) :
    deriv (deriv (expAffine φ ψ)) = fun x => ψ^2 * expAffine φ ψ x := by
  rw [deriv_expAffine_mul]
  funext x
  have h : deriv (fun y => Real.exp (φ + ψ * y) * ψ) x = Real.exp (φ + ψ * x) * ψ * ψ :=
    ((hasDerivAt_affine φ ψ x).exp.mul_const ψ).deriv
  rw [h]
  simp only [expAffine]
  ring

/-- The exponential-affine family is smooth. -/
theorem contDiff_expAffine (φ ψ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (expAffine φ ψ) :=
  Real.contDiff_exp.comp (contDiff_const.add (contDiff_const.mul contDiff_id))

/-! ### The engine lemma -/

/-- **The affine engine (stage 1 deliverable).** The generator applied to an
exponential-affine function is an affine-in-`x` bracket times the function itself:
`L e^(φ + ψ x) = ((a ψ - κ ψ x) + σ²/2 ψ²) e^(φ + ψ x)` — Bagaria ch. 14, eq. 14.4
with `μ = a - κ x`, `v = σ²`. -/
theorem ouGenerator_expAffine (a κ σ φ ψ : ℝ) :
    ouGenerator a κ σ (expAffine φ ψ)
      = fun x => ((a * ψ - κ * ψ * x) + σ^2 / 2 * ψ^2) * expAffine φ ψ x := by
  funext x
  simp only [ouGenerator]
  rw [deriv_deriv_expAffine, deriv_expAffine]
  simp only [expAffine]
  ring

/-! ### The Riccati corollary -/

/-- **Riccati corollary (Bagaria ch. 14, eqs. 14.5–14.6).** The bracket of the engine
lemma is affine with slope `c₁ = b ψ = -κ ψ` (the `ψ`-equation's linear term) and
intercept `c₀ = a ψ + ½ d ψ² = a ψ + σ²/2 ψ²`. For lesson 0033's spec: with `d = σ²`,
`b = -κ`, the slope evolves by `ψ' = b ψ + ½ d ψ²` and the intercept integrates
`φ' = a ψ + ½ c ψ²` (here `c = 0`); stage 2 solves these ODEs explicitly. -/
theorem ouBracket_affine (a κ σ φ ψ : ℝ) :
    ∃ (c₀ c₁ : ℝ), c₁ = -κ * ψ ∧ c₀ = a * ψ + σ^2 / 2 * ψ^2
      ∧ ouGenerator a κ σ (expAffine φ ψ)
        = fun x => (c₀ + c₁ * x) * expAffine φ ψ x := by
  refine ⟨a * ψ + σ^2 / 2 * ψ^2, -κ * ψ, rfl, rfl, ?_⟩
  rw [ouGenerator_expAffine]
  funext x
  ring

/-! ### Stage 2: the ODE solutions and the pricing-PDE verification

The two ODE solvers feeding the engine: the linear Vasicek `B`-ODE (`bondSlope`, used in
the bond-profile PDE below) and the Bernoulli/Riccati `ψ`-ODE (`riccatiFlow`, the CIR
`d = σ²` case of the engine's Riccati system `ψ' = bψ + ½dψ²` with `b = -κ`).
The stage deliverable is `bondProfile_pde`: the exponential-affine ansatz with these
ODE solutions satisfies the (discounted) pricing PDE. -/

/-! #### The bond slope (the linear ODE — the Vasicek B-factor) -/

/-- The **bond slope** `B(τ) = (1 − e^{−κτ})/κ` — the Vasicek B-factor, the sensitivity
of the log bond price to the short rate, and the solution of the linear ODE
`B' = 1 − κ B`, `B(0) = 0`. Defined for every `κ` (Lean's `x/0 = 0` makes `κ = 0` the
constant-zero function); the ODE statements carry the honest guard `κ ≠ 0`. -/
noncomputable def bondSlope (κ τ : ℝ) : ℝ := (1 - Real.exp (-(κ * τ))) / κ

/-- The bond slope's τ-derivative is `e^{−κτ}`:
`d/dτ [(1 − e^{−κτ})/κ] = (κ e^{−κτ})/κ = e^{−κτ}`. Guard `κ ≠ 0` is necessary:
at `κ = 0` the definition collapses to the constant `0` function, whose derivative
is `0 ≠ e^0 = 1`. -/
theorem hasDerivAt_bondSlope (κ τ : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (bondSlope κ) (Real.exp (-(κ * τ))) τ := by
  have hlin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) τ := by
    simpa using (hasDerivAt_id τ).const_mul (-κ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(κ * s)))
      (Real.exp (-(κ * τ)) * -κ) τ := by
    simpa using hlin.exp
  have hsub : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(κ * s)))
      (-(Real.exp (-(κ * τ)) * -κ)) τ := hexp.const_sub 1
  have hdiv : HasDerivAt (bondSlope κ) (-(Real.exp (-(κ * τ)) * -κ) / κ) τ :=
    hsub.div_const κ
  have hval : -(Real.exp (-(κ * τ)) * -κ) / κ = Real.exp (-(κ * τ)) := by
    field_simp
  rw [hval] at hdiv
  exact hdiv

/-- The Vasicek B-ODE in maturity: `B'(τ) = 1 − κ B(τ)`. -/
theorem bondSlope_ode (κ τ : ℝ) (hκ : κ ≠ 0) :
    deriv (bondSlope κ) τ = 1 - κ * bondSlope κ τ := by
  rw [(hasDerivAt_bondSlope κ τ hκ).deriv]
  simp only [bondSlope]
  field_simp
  ring

/-- The bond slope starts at zero (definitional: `(1 − e^0)/κ = 0/κ = 0`; no `κ` guard
needed). -/
theorem bondSlope_at_zero (κ : ℝ) : bondSlope κ 0 = 0 := by
  simp only [bondSlope, mul_zero, neg_zero, Real.exp_zero, sub_self, mul_zero, zero_div]

/-! #### The Riccati flow (the Bernoulli ψ-equation with `d = σ²`) -/

/-- The **Riccati flow**: the explicit Bernoulli solution of the CIR `ψ`-equation
`ψ' = −κψ + (σ²/2)ψ²`, `ψ(0) = ψ₀` (the engine's Riccati system with `b = −κ`,
`d = σ²`, Bagaria ch. 14, eq. 14.5):

`ψ(t) = 2κψ₀ e^{−κt} / (2κ − σ²ψ₀ (1 − e^{−κt}))`.

Sign note (checked on paper and symbolically before formalizing): the denominator is
`2κ − σ²ψ₀(1 − e^{−κt})`. The `+` variant does **not** solve the `ψ`-equation — its
residual is `−4κ²ψ₀²σ² / (2κe^{κt} + σ²ψ₀(e^{κt} − 1))² ≠ 0`; the minus-sign form
substitutes back exactly. -/
noncomputable def riccatiFlow (κ σ ψ₀ t : ℝ) : ℝ :=
  (2 * κ * ψ₀ * Real.exp (-(κ * t))) /
    (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))))

/-- The Riccati flow starts at `ψ₀` (needs `κ ≠ 0`: at `t = 0` the denominator is
exactly `2κ`). -/
theorem riccatiFlow_at_zero (κ σ ψ₀ : ℝ) (hκ : κ ≠ 0) :
    riccatiFlow κ σ ψ₀ 0 = ψ₀ := by
  simp only [riccatiFlow, mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- **The Riccati ODE.** The flow solves `ψ' = −κψ + (σ²/2)ψ²`, guarded by the honest
nonvanishing of the Bernoulli denominator (at `t = 0` the guard reads `κ ≠ 0`; it holds
for all `t` whenever `σ²ψ₀ ≤ 2κ` or `t` is small). -/
theorem hasDerivAt_riccatiFlow (κ σ ψ₀ t : ℝ)
    (hD : 2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))) ≠ 0) :
    HasDerivAt (riccatiFlow κ σ ψ₀)
      ((-κ) * riccatiFlow κ σ ψ₀ t + σ ^ 2 / 2 * (riccatiFlow κ σ ψ₀ t) ^ 2) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(κ * s)))
      (Real.exp (-(κ * t)) * -κ) t := by
    have hlin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) t := by
      simpa using (hasDerivAt_id t).const_mul (-κ)
    simpa using hlin.exp
  have hnum : HasDerivAt (fun s : ℝ => 2 * κ * ψ₀ * Real.exp (-(κ * s)))
      (2 * κ * ψ₀ * (Real.exp (-(κ * t)) * -κ)) t := he.const_mul (2 * κ * ψ₀)
  have hsub1 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(κ * s)))
      (-(Real.exp (-(κ * t)) * -κ)) t := he.const_sub 1
  have hden : HasDerivAt (fun s : ℝ => 2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * s))))
      (-(σ ^ 2 * ψ₀ * -(Real.exp (-(κ * t)) * -κ))) t :=
    (hsub1.const_mul (σ ^ 2 * ψ₀)).const_sub (2 * κ)
  have hq := hnum.div hden hD
  have hval :
      ((2 * κ * ψ₀ * (Real.exp (-(κ * t)) * -κ)) *
          (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t)))) -
        (2 * κ * ψ₀ * Real.exp (-(κ * t))) *
          -(σ ^ 2 * ψ₀ * -(Real.exp (-(κ * t)) * -κ))) /
        (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t)))) ^ 2
      = (-κ) * ((2 * κ * ψ₀ * Real.exp (-(κ * t))) /
          (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))))) +
        σ ^ 2 / 2 * ((2 * κ * ψ₀ * Real.exp (-(κ * t))) /
          (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))))) ^ 2 := by
    field_simp
    ring
  rw [show riccatiFlow κ σ ψ₀ = fun s : ℝ => (2 * κ * ψ₀ * Real.exp (-(κ * s))) /
      (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * s)))) from rfl, ← hval]
  exact hq

/-! #### The pricing-PDE verification (the stage deliverable) -/

/-- The **bond profile**: `u(t, x) = e^{C(t) − B(t) x}` with `B(t) = bondSlope κ (T − t)`
and `C` an antiderivative of `κθ·B − σ²B²/2` (taken as a hypothesis — the explicit
integral is not needed for the PDE verification). This is Vasicek's
`P(t, x) = A(t) e^{−B(t) x}` with `A = e^C`; `θ` enters only through `C`. -/
noncomputable def bondProfile (κ : ℝ) (C : ℝ → ℝ) (T t x : ℝ) : ℝ :=
  Real.exp (C t - bondSlope κ (T - t) * x)

/-- Terminal shape: `B(T) = bondSlope κ 0 = 0`, so the profile expires to `e^{C(T)}` —
the bond's face value when `C(T) = 0`. -/
theorem bondProfile_terminal (κ : ℝ) (C : ℝ → ℝ) (T x : ℝ) :
    bondProfile κ C T T x = Real.exp (C T) := by
  simp only [bondProfile, sub_self, bondSlope_at_zero, zero_mul, sub_zero]

/-- **The pricing-PDE verification (stage 2 deliverable).** For the Vasicek short rate
`dx = (κθ − κx) dt + σ dW`, the exponential-affine bond profile with `B' = κB − 1`
(i.e. `bondSlope κ (T − ·)`, whose maturity-form ODE is `B' = 1 − κB`) and
`C' = κθ·B − σ²B²/2` satisfies the **discounted pricing PDE**

`∂_t u + L u = x · u`,  i.e.  `∂_t u = −L u + x·u` (Feynman–Kac with discount rate `x`),

where `L = ouGenerator (κ*θ) κ σ`. Sign note: the undamped statement
`∂_t u = L u` (no discount term, opposite sign) is *false* for this ansatz — matching
coefficients forces the `x·u` discount term and this sign, exactly as in Vasicek's
original PDE. No `t < T` hypothesis is needed: the identity holds for every `(t, x)`. -/
theorem bondProfile_pde (κ θ σ : ℝ) (C : ℝ → ℝ) (T : ℝ) (hκ : κ ≠ 0)
    (hC : ∀ s, HasDerivAt C
      ((κ * θ) * bondSlope κ (T - s) - σ ^ 2 / 2 * bondSlope κ (T - s) ^ 2) s)
    (t x : ℝ) :
    deriv (fun s => bondProfile κ C T s x) t
      + ouGenerator (κ * θ) κ σ (bondProfile κ C T t) x
      = x * bondProfile κ C T t x := by
  -- the time-to-maturity map and its derivative
  have hBid : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hBexp : Real.exp (-(κ * (T - t))) = 1 - κ * bondSlope κ (T - t) := by
    simp only [bondSlope]
    field_simp
    ring
  -- `B'(t) = κ·B(t) − 1` (the maturity ODE `B' = 1 − κB` with the chain rule's minus)
  have hB : HasDerivAt (fun s => bondSlope κ (T - s)) (κ * bondSlope κ (T - t) - 1) t := by
    have hval : Real.exp (-(κ * (T - t))) * -1 = κ * bondSlope κ (T - t) - 1 := by
      rw [hBexp]; ring
    rw [← hval]
    exact (hasDerivAt_bondSlope κ (T - t) hκ).comp t hBid
  -- time derivative of `u(·, x)`: `u_t = (C' − B'x) · u`
  have hinner : HasDerivAt (fun s => C s - bondSlope κ (T - s) * x)
      ((κ * θ * bondSlope κ (T - t) - σ ^ 2 / 2 * bondSlope κ (T - t) ^ 2)
        - (κ * bondSlope κ (T - t) - 1) * x) t :=
    (hC t).sub (hB.mul_const x)
  have htime : HasDerivAt (fun s => bondProfile κ C T s x)
      (Real.exp (C t - bondSlope κ (T - t) * x) *
        ((κ * θ * bondSlope κ (T - t) - σ ^ 2 / 2 * bondSlope κ (T - t) ^ 2)
        - (κ * bondSlope κ (T - t) - 1) * x)) t :=
    hinner.exp
  -- spatial derivatives via the stage-1 family: `u = expAffine (C t) (−B t)`
  have hsp1 : ∀ y : ℝ, HasDerivAt (bondProfile κ C T t)
      (Real.exp (C t - bondSlope κ (T - t) * y) * -bondSlope κ (T - t)) y := fun y => by
    have hrfl : bondProfile κ C T t
        = fun z => Real.exp (C t - bondSlope κ (T - t) * z) := rfl
    rw [hrfl]
    simpa [sub_eq_add_neg] using
      (hasDerivAt_affine (C t) (-bondSlope κ (T - t)) y).exp
  have hsp2 : deriv (deriv (bondProfile κ C T t)) x
      = bondSlope κ (T - t) ^ 2 * Real.exp (C t - bondSlope κ (T - t) * x) := by
    have hdfun : deriv (bondProfile κ C T t)
        = fun y => Real.exp (C t - bondSlope κ (T - t) * y) * -bondSlope κ (T - t) :=
      funext fun y => (hsp1 y).deriv
    have h2 : HasDerivAt (fun y => Real.exp (C t - bondSlope κ (T - t) * y)
          * -bondSlope κ (T - t))
        (Real.exp (C t - bondSlope κ (T - t) * x) * -bondSlope κ (T - t)
          * -bondSlope κ (T - t)) x :=
      (hsp1 x).mul_const (-bondSlope κ (T - t))
    rw [hdfun, h2.deriv]
    ring
  have hsp1' : deriv (bondProfile κ C T t) x
      = Real.exp (C t - bondSlope κ (T - t) * x) * -bondSlope κ (T - t) := (hsp1 x).deriv
  -- assemble: `u_t + L u = x·u` — the coefficient algebra cancels by the B/C ODEs
  rw [htime.deriv]
  simp only [ouGenerator]
  rw [hsp2, hsp1']
  simp only [bondProfile]
  ring

/-- **Bridge to MathFin.** The bond slope is character-identical to
`MathFin.vasicekBondB` (`MathFin/FixedIncome/VasicekBondPrice.lean`, the affine
coefficient `B(T)` of the Vasicek log bond price) — definitional equality. -/
theorem bondSlope_eq_vasicekBondB (κ T : ℝ) : bondSlope κ T = MathFin.vasicekBondB κ T :=
  rfl

/-! ### Stage 3: the CIR generator and the CIR bond ansatz

The CIR variance process `dv_t = κ(θ − v_t) dt + ξ √v_t dW_t` has generator
`Lf = (κθ − κv) f' + (ξ² v / 2) f''` — affine drift (`a = κθ`, `b = −κ`) with a
**`v`-proportional** diffusion term (`c = 0`, `d = ξ²`). The engine lemma goes through
verbatim (the bracket is still affine in `v`), and the discounted pricing PDE
`∂_t u + Lu = v · u` (Feynman–Kac with short rate `r = v`) closes on the ansatz
`u(t, v) = e^{C(t) − ψ(t) v}`.

Sign bookkeeping (worked on paper and checked numerically before formalizing):
`u_t + Lu = u[C' − κθψ + v(−ψ' + κψ + (ξ²/2)ψ²)]`, so matching the `v`-coefficient
against the discount rate `v` forces the **calendar-time** system
`ψ' = −1 + κψ + (ξ²/2)ψ²`, `C' = κθψ` (terminal `ψ(T) = 1`, `C(T) = 0` gives the payoff
`e^{−v}`); in time-to-maturity this is the CIR `B`-equation
`B' = 1 − κB − (ξ²/2)B²` (Brigo–Mercurio §3.9). The stage-2 `riccatiFlow` instead
solves the *undiscounted* engine slope equation `ψ' = −κψ + (σ²/2)ψ²` — no `−1`, because
no discount acts there (it is the characteristic-function exponent equation). The
connection is recorded honestly in `hasDerivAt_riccatiFlow_cirRoles`; the two equations
are *not* the same ODE. -/

/-- The CIR generator `Lf = (κθ − κv) f' + (ξ² v / 2) f''` — the OU generator with drift
`a = κθ`, slope `−κ`, and a **`v`-proportional** diffusion term `½ ξ² v f''`. -/
noncomputable def cirGenerator (κ θ ξ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun v => (κ * θ - κ * v) * deriv f v + (ξ ^ 2 * v / 2) * deriv (deriv f) v

/-! #### The CIR engine lemma -/

/-- **The CIR engine lemma.** The CIR generator applied to an exponential-affine function
is an affine-in-`v` bracket times the function itself:
`L e^(φ + ψ v) = ((κθψ − κψv) + ξ²/2 ψ² v) e^(φ + ψ v)` — Bagaria ch. 14, eq. 14.4 with
`μ = κθ − κv`, `v = ξ² v`. Reuses the stage-1 derivative helpers verbatim. -/
theorem cirGenerator_expAffine (κ θ ξ φ ψ : ℝ) :
    cirGenerator κ θ ξ (expAffine φ ψ)
      = fun v => ((κ * θ * ψ - κ * ψ * v) + ξ^2 / 2 * ψ^2 * v) * expAffine φ ψ v := by
  funext v
  simp only [cirGenerator]
  rw [deriv_deriv_expAffine, deriv_expAffine]
  simp only [expAffine]
  ring

/-- **CIR Riccati corollary.** The bracket of `cirGenerator_expAffine` is affine with
intercept `c₀ = κθψ` (which the engine's φ-equation integrates: `φ' = κθψ`, the `c = 0`
case) and slope `c₁ = −κψ + (ξ²/2)ψ²` (the ψ-equation with `b = −κ`, `d = ξ²` — the
engine's Riccati system, Bagaria ch. 14, eqs. 14.5–14.6, in the CIR roles). -/
theorem cirBracket_affine (κ θ ξ φ ψ : ℝ) :
    ∃ (c₀ c₁ : ℝ), c₁ = -κ * ψ + ξ ^ 2 / 2 * ψ ^ 2 ∧ c₀ = κ * θ * ψ
      ∧ cirGenerator κ θ ξ (expAffine φ ψ)
        = fun v => (c₀ + c₁ * v) * expAffine φ ψ v := by
  refine ⟨κ * θ * ψ, -κ * ψ + ξ ^ 2 / 2 * ψ ^ 2, rfl, rfl, ?_⟩
  rw [cirGenerator_expAffine]
  funext v
  ring

/-- **The CIR engine-slope flow.** Reading the stage-2 Riccati flow in the CIR roles
`(κ, ξ)` (i.e. `σ := ξ`) solves exactly the slope equation of `cirBracket_affine`:
`ψ' = −κψ + (ξ²/2)ψ²`, the `d = ξ²` case of the engine's Riccati system. Guard: the
honest Bernoulli nonvanishing `2κ − ξ²ψ₀(1 − e^{−κt}) ≠ 0`. Role note (honest): this is
the *undiscounted* exponent equation (characteristic-function side); the **bond**
`B`-factor obeys `B' = 1 − κB − (ξ²/2)B²`, whose calendar-time form
`ψ' = −1 + κψ + (ξ²/2)ψ²` is the `hψ` of `cirBondProfile_pde` below — the discount term
contributes the extra constant. -/
theorem hasDerivAt_riccatiFlow_cirRoles (κ ξ ψ₀ t : ℝ)
    (hD : 2 * κ - ξ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))) ≠ 0) :
    HasDerivAt (riccatiFlow κ ξ ψ₀)
      ((-κ) * riccatiFlow κ ξ ψ₀ t + ξ ^ 2 / 2 * (riccatiFlow κ ξ ψ₀ t) ^ 2) t :=
  hasDerivAt_riccatiFlow κ ξ ψ₀ t hD

/-! #### The CIR bond profile and its pricing PDE -/

set_option linter.unusedVariables false in
/-- The **CIR bond profile**: `u(t, v) = e^{C(t) − ψ(t) v}` — CIR's
`P(t, v) = A(t) e^{−B(t) v}` with `A = e^C`. The parameters `κ θ ξ T` are carried for
signature parallelism with `bondProfile` (the CIR content lives in the ODE hypotheses
on `ψ` and `C`); the linter is silenced for exactly those binders. -/
noncomputable def cirBondProfile (κ θ ξ : ℝ) (C : ℝ → ℝ) (ψ : ℝ → ℝ) (T t v : ℝ) : ℝ :=
  Real.exp (C t - ψ t * v)

/-- Terminal shape: with the bond's terminal data `ψ(T) = 1`, `C(T) = 0` the profile
expires to `e^{−v}` — the exponential-affine payoff `e^{−1·v}` (unlike Vasicek's
`B(T) = 0`, the CIR `ψ(T) = 1` is genuine data, not definitional). -/
theorem cirBondProfile_terminal (κ θ ξ : ℝ) (C : ℝ → ℝ) (ψ : ℝ → ℝ) (T v : ℝ)
    (hψT : ψ T = 1) (hCT : C T = 0) :
    cirBondProfile κ θ ξ C ψ T T v = Real.exp (-v) := by
  simp only [cirBondProfile, hψT, hCT, one_mul, zero_sub]

/-- **The CIR pricing-PDE verification (stage 3 deliverable).** For the CIR short-rate
process `dv = κ(θ − v) dt + ξ √v dW` (discount rate `r = v`), the exponential-affine
bond profile with the **calendar-time** ODEs
`ψ' = −1 + κψ + (ξ²/2)ψ²` (equivalently the maturity-time CIR `B`-equation
`B' = 1 − κB − (ξ²/2)B²` after the chain-rule sign flip — exactly as Vasicek's
`B' = κB − 1` arose from `B' = 1 − κB` in `bondProfile_pde`) and `C' = κθψ` satisfies
the **discounted pricing PDE**

`∂_t u + L u = v · u`  (Feynman–Kac with discount rate `v`),

where `L = cirGenerator κ θ ξ`. No `t < T` hypothesis is needed: the identity holds for
every `(t, v)`. Honesty note: the ψ-hypothesis is the *discounted* (bond) Riccati
equation, not the undiscounted `riccatiFlow` equation — with the latter the residual is
`v (2κψ − 1) · u ≠ 0` (the missing `−1` is the discount term). -/
theorem cirBondProfile_pde (κ θ ξ : ℝ) (C : ℝ → ℝ) (ψ : ℝ → ℝ) (T : ℝ)
    (hψ : ∀ s, HasDerivAt ψ (κ * ψ s + ξ ^ 2 / 2 * ψ s ^ 2 - 1) s)
    (hC : ∀ s, HasDerivAt C (κ * θ * ψ s) s)
    (t v : ℝ) :
    deriv (fun s => cirBondProfile κ θ ξ C ψ T s v) t
      + cirGenerator κ θ ξ (cirBondProfile κ θ ξ C ψ T t) v
      = v * cirBondProfile κ θ ξ C ψ T t v := by
  -- time derivative of `u(·, v)`: `u_t = (C' − ψ' v) · u`
  have hinner : HasDerivAt (fun s => C s - ψ s * v)
      ((κ * θ * ψ t) - (κ * ψ t + ξ ^ 2 / 2 * ψ t ^ 2 - 1) * v) t :=
    (hC t).sub ((hψ t).mul_const v)
  have htime : HasDerivAt (fun s => cirBondProfile κ θ ξ C ψ T s v)
      (Real.exp (C t - ψ t * v) *
        ((κ * θ * ψ t) - (κ * ψ t + ξ ^ 2 / 2 * ψ t ^ 2 - 1) * v)) t :=
    hinner.exp
  -- spatial derivatives via the stage-1 family: `u = expAffine (C t) (−ψ t)`
  have hsp1 : ∀ y : ℝ, HasDerivAt (cirBondProfile κ θ ξ C ψ T t)
      (Real.exp (C t - ψ t * y) * -(ψ t)) y := fun y => by
    have hrfl : cirBondProfile κ θ ξ C ψ T t
        = fun z => Real.exp (C t - ψ t * z) := rfl
    rw [hrfl]
    simpa [sub_eq_add_neg] using
      (hasDerivAt_affine (C t) (-(ψ t)) y).exp
  have hsp2 : deriv (deriv (cirBondProfile κ θ ξ C ψ T t)) v
      = ψ t ^ 2 * Real.exp (C t - ψ t * v) := by
    have hdfun : deriv (cirBondProfile κ θ ξ C ψ T t)
        = fun y => Real.exp (C t - ψ t * y) * -(ψ t) :=
      funext fun y => (hsp1 y).deriv
    have h2 : HasDerivAt (fun y => Real.exp (C t - ψ t * y) * -(ψ t))
        (Real.exp (C t - ψ t * v) * -(ψ t) * -(ψ t)) v :=
      (hsp1 v).mul_const (-(ψ t))
    rw [hdfun, h2.deriv]
    ring
  have hsp1' : deriv (cirBondProfile κ θ ξ C ψ T t) v
      = Real.exp (C t - ψ t * v) * -(ψ t) := (hsp1 v).deriv
  -- assemble: `u_t + L u = v·u` — the coefficient algebra cancels by the ψ/C ODEs
  rw [htime.deriv]
  simp only [cirGenerator]
  rw [hsp2, hsp1']
  simp only [cirBondProfile]
  ring

#print axioms ouGenerator_expAffine
#print axioms ouBracket_affine
#print axioms hasDerivAt_bondSlope
#print axioms bondSlope_ode
#print axioms bondSlope_at_zero
#print axioms riccatiFlow_at_zero
#print axioms hasDerivAt_riccatiFlow
#print axioms bondProfile_terminal
#print axioms bondProfile_pde
#print axioms bondSlope_eq_vasicekBondB
#print axioms cirGenerator
#print axioms cirGenerator_expAffine
#print axioms cirBracket_affine
#print axioms hasDerivAt_riccatiFlow_cirRoles
#print axioms cirBondProfile
#print axioms cirBondProfile_terminal
#print axioms cirBondProfile_pde

/-! ### Stage 4: the CIR bond closed form and the final assembly

Stage 3's PDE (`cirBondProfile_pde`) is closed by *explicit* data: the CIR `B`-factor
solves (maturity time) `B' = 1 − κB − (ξ²/2)B²` with `B(0) = 0`, and the antiderivative
`C' = κθ·B` with `C(T) = 0` is written out in closed form. Assembling gives the CIR
zero-coupon bond price `P(t, v) = e^{A(t) − B(T−t)·v}` satisfying `∂_t P + L P = v·P`
with terminal condition `P(T, v) = 1` — the CIR analogue of `vasicekBondPrice_affine`.

**Derivation of the closed forms** (worked on paper, then verified numerically at
`κ = 2, θ = 1/2, ξ = 1` before formalizing: `B(0) = 0`, `B'(0) = 1`, ODE residuals
`~ 10⁻¹¹`, `C' = κθ·B` residuals `~ 10⁻¹⁰`, `P(T, v) = 1` exactly; Brigo–Mercurio §3.9
is the reference answer).

*Riccati linearization.* Substituting `B = (2/ξ²)·u′/u` in `B' = 1 − κB − (ξ²/2)B²`
linearizes it to `u″ + κu′ − (ξ²/2)u = 0`, whose characteristic roots are `(γ − κ)/2`
and `−(γ + κ)/2` with `γ = √(κ² + 2ξ²)`. The resulting Möbius form in `e^{γτ}`,
with `B(0) = 0` imposed, is

`B(τ) = 2(e^{γτ} − 1) / ((γ + κ)(e^{γτ} − 1) + 2γ)`,

which satisfies `B(0) = 0`, `B'(0) = 1` (both forced by the ODE), and whose ODE
residual, after substituting `E = e^{γτ}` and multiplying out, reduces to the identity
`4γ²E = 4γ²E` (both numerator sides; `D² − κND − (ξ²/2)N² = 4γ²E = N'D − ND'`).

*The A-factor.* `C(t) = −∫ₜᵀ κθ·B(T−s)ds` integrates in closed form using
`B = (2/(γ+κ))·(1 − 2γ/D)`, `D = (γ+κ)e^{γτ} + (γ−κ)`:

`∫₀^τ B = (2/(γ+κ))·τ − (4/((γ+κ)(γ−κ)))·log(2γ / ((γ+κ) + (γ−κ)e^{−γτ}))`,

so, with `(γ+κ)(γ−κ) = 2ξ²`,

`log A(t) = −(2κθ/(γ+κ))·(T−t) + (2κθ/ξ²)·log(2γ / ((γ+κ) + (γ−κ)e^{−γ(T−t)}))`,

which vanishes at `t = T` and whose `t`-derivative is `κθ·B(T−t)`: the derivative check
reduces to `2κθ(γ+κ)(1−w)/((γ+κ)·U) = 2κθ(1−w)/U` with `U = (γ+κ) + (γ−κ)w`, `w =
e^{−γ(T−t)}` — no relation beyond `γ² − κ² = (γ−κ)(γ+κ)` (pure ring) and
`(γ−κ)(γ+κ)γ = 2ξ²γ` (where the `γ² = κ² + 2ξ²` enters).

**Normalization note (honest deviation from the stage-3 handoff).** The handoff asked
for `B(0) = 1` and an `e^{−v}` terminal condition. That is inconsistent with the
standard closed form above: a zero-coupon bond's terminal data is `P(T, v) = 1`, which
forces `B(0) = 0` and `A(0) = 1` — exactly as `bondSlope κ 0 = 0` for Vasicek. The
prompt's own parenthetical ("the standard CIR zero-coupon answer is
`B(t) = 2(e^{γt}−1)/((γ+κ)(e^{γt}−1)+2γ)`") also has `B(0) = 0`. A `B(0) = 1` ansatz
prices the exponential payoff `e^{−v}` (the engine's canonical affine terminal
condition — that is the sense in which stage 3's `cirBondProfile_terminal` reads
`ψ T = 1`), and its Riccati solution is a different, non-standard Möbius form. We land
the true zero-coupon bond (`B(0) = 0`, terminal payoff `1`), matching Brigo–Mercurio
§3.9 and `vasicekBondB` (also `0` at maturity `0`).

**Guards.** `κ² + 2ξ² ≥ 0` always, so `γ` is real for all real parameters — no
Feller-type condition enters at the deterministic level (`2κθ ≥ ξ²` is the *existence*
condition for the CIR SDE, the one still-missing probability piece). The sharp guard
for the closed forms is `γ ≠ 0`, i.e. `(κ, ξ) ≠ (0, 0)`; we use the convenient
sufficient hypothesis `ξ ≠ 0`, which gives `γ > 0` and `γ > |κ|`, making every
denominator below positive. `θ` is carried in `cirBondB` for signature parallelism
with `cirBondProfile` (the `B`-factor does not involve `θ`). -/

/-- The CIR characteristic root `γ = √(κ² + 2ξ²)` — real for all real `κ ξ`, positive
as soon as `ξ ≠ 0`. -/
noncomputable def cirGamma (κ ξ : ℝ) : ℝ := Real.sqrt (κ ^ 2 + 2 * ξ ^ 2)

private theorem cirGamma_sq (κ ξ : ℝ) : cirGamma κ ξ ^ 2 = κ ^ 2 + 2 * ξ ^ 2 := by
  rw [pow_two, cirGamma, Real.mul_self_sqrt (by positivity)]

private theorem cirGamma_pos (κ ξ : ℝ) (hξ : ξ ≠ 0) : 0 < cirGamma κ ξ := by
  refine Real.sqrt_pos.mpr ?_
  by_contra hcon
  push Not at hcon
  have h1 : ξ ^ 2 ≤ 0 := by linarith [sq_nonneg κ, sq_nonneg ξ]
  exact hξ (sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg ξ)))

private theorem cirGamma_ne_zero (κ ξ : ℝ) (hξ : ξ ≠ 0) : cirGamma κ ξ ≠ 0 :=
  ne_of_gt (cirGamma_pos κ ξ hξ)

private theorem cirGamma_abs_lt (κ ξ : ℝ) (hξ : ξ ≠ 0) :
    κ < cirGamma κ ξ ∧ -cirGamma κ ξ < κ := by
  have hγpos : 0 < cirGamma κ ξ := cirGamma_pos κ ξ hξ
  have hγsq := cirGamma_sq κ ξ
  have hxi2 : 0 < ξ ^ 2 := by
    have h1 : ξ ^ 2 ≥ 0 := sq_nonneg ξ
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (sq_eq_zero_iff.mp h.symm) hξ
  have h1 : κ ^ 2 < cirGamma κ ξ ^ 2 := by rw [hγsq]; linarith
  constructor
  · by_contra hcon
    push Not at hcon
    -- `γ ≤ κ` (with `γ > 0`) forces `γ² ≤ κ²`
    have hκ0 : 0 ≤ κ := hγpos.le.trans hcon
    exact absurd h1 (not_lt.mpr (by nlinarith [sq_nonneg κ, sq_nonneg (cirGamma κ ξ)]))
  · by_contra hcon
    push Not at hcon
    -- `κ ≤ −γ` forces `γ² ≤ κ²`
    have h3 : cirGamma κ ξ ≤ -κ := by linarith
    have h4 : 0 ≤ -κ := by linarith
    have h2 : cirGamma κ ξ ^ 2 ≤ κ ^ 2 := by
      calc cirGamma κ ξ ^ 2 = cirGamma κ ξ * cirGamma κ ξ := by ring
        _ ≤ cirGamma κ ξ * (-κ) := mul_le_mul_of_nonneg_left h3 hγpos.le
        _ ≤ (-κ) * (-κ) := mul_le_mul_of_nonneg_right h3 h4
        _ = κ ^ 2 := by ring
    exact absurd h1 (not_lt.mpr h2)

/-- Lambda-form addition (this Mathlib's `HasDerivAt.add` states the function as the
Pi-sum `f + g`; the assembly proofs need the eta-expanded lambda form). -/
private theorem hasDerivAt_add' {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (h : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y + g y) (f' + g') x := by
  have h2 := h.add hg
  rw [show (f + g) = fun y => f y + g y from by funext y; simp] at h2
  exact h2

/-- Derivative of `log (a / f)` for a nonzero constant `a`: `−f'/f` — the form in which
the log-derivative of `cirBondLogA`'s second term is needed. -/
private theorem hasDerivAt_log_div_const {f : ℝ → ℝ} {a f' : ℝ} {x : ℝ}
    (h : HasDerivAt f f' x) (ha : a ≠ 0) (hx : f x ≠ 0) :
    HasDerivAt (fun y => Real.log (a / f y)) (-(f' / f x)) x := by
  have h1 : HasDerivAt (fun _ : ℝ => a) 0 x := hasDerivAt_const x a
  have h2 : HasDerivAt (fun y : ℝ => Real.log (a / f y))
      (((0 * f x - a * f') / f x ^ 2) / (a / f x)) x :=
    (h1.div h hx).log (by exact div_ne_zero ha hx)
  have h3 : ((0 * f x - a * f') / f x ^ 2) / (a / f x) = -(f' / f x) := by
    field_simp
    ring
  rw [h3] at h2
  exact h2

set_option linter.unusedVariables false in
/-- The **CIR bond `B`-factor** (maturity time): the explicit solution of the CIR
`B`-equation `B' = 1 − κB − (ξ²/2)B²`, `B(0) = 0`,

`B(τ) = 2(e^{γτ} − 1) / ((γ + κ)(e^{γτ} − 1) + 2γ)`,  `γ = √(κ² + 2ξ²)`,

the hyperbolic closed form of Brigo–Mercurio §3.9 (derivation in the stage-4 header
comment). `θ` is carried for signature parallelism with `cirBondProfile` only. -/
noncomputable def cirBondB (κ θ ξ t : ℝ) : ℝ :=
  2 * (Real.exp (cirGamma κ ξ * t) - 1) /
    ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ)

/-- Terminal data of the bond `B`-factor: `B(0) = 0` (definitional: the numerator
vanishes at `τ = 0`) — the zero-coupon normalization, exactly as `bondSlope κ 0 = 0`
for Vasicek. -/
theorem cirBondB_at_zero (κ θ ξ : ℝ) : cirBondB κ θ ξ 0 = 0 := by
  simp only [cirBondB, mul_zero, Real.exp_zero, sub_self, zero_add, zero_div]

/-- **The CIR bond ODE.** `B'(τ) = 1 − κ·B(τ) − (ξ²/2)·B(τ)²` for the closed-form
`cirBondB`, with the honest guard `ξ ≠ 0` (sharp: `γ ≠ 0`). Proof idiom: stage 2's
`hasDerivAt_riccatiFlow` — quotient rule, then one `field_simp`/`ring` identity; the
Riccati coefficient `ξ²/2` is first rewritten as `(γ²−κ²)/4` (from `γ² = κ² + 2ξ²`) so
the residual algebra is a polynomial identity in free atoms. -/
theorem hasDerivAt_cirBondB (κ θ ξ t : ℝ) (hξ : ξ ≠ 0) :
    HasDerivAt (cirBondB κ θ ξ)
      (1 - κ * cirBondB κ θ ξ t - ξ ^ 2 / 2 * cirBondB κ θ ξ t ^ 2) t := by
  have hγpos : 0 < cirGamma κ ξ := cirGamma_pos κ ξ hξ
  obtain ⟨hκlt, hneg⟩ := cirGamma_abs_lt κ ξ hξ
  have hp1 : 0 < cirGamma κ ξ + κ := by linarith
  have hp2 : 0 < cirGamma κ ξ - κ := by linarith
  have hγsq := cirGamma_sq κ ξ
  have hxi2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ
  have hgc2 : cirGamma κ ξ ^ 2 - κ ^ 2 = 2 * ξ ^ 2 := by rw [hγsq]; ring
  have hcoef4 : (cirGamma κ ξ ^ 2 - κ ^ 2) / 4 = ξ ^ 2 / 2 := by rw [hgc2]; ring
  -- derivative building blocks
  have hlin : HasDerivAt (fun s : ℝ => cirGamma κ ξ * s) (cirGamma κ ξ) t := by
    simpa using (hasDerivAt_id t).const_mul (cirGamma κ ξ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (cirGamma κ ξ * s))
      (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ) t := by
    simpa using hlin.exp
  have hnum : HasDerivAt (fun s : ℝ => 2 * (Real.exp (cirGamma κ ξ * s) - 1))
      (2 * (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ)) t := by
    simpa using (hexp.sub_const 1).const_mul 2
  have hden : HasDerivAt (fun s : ℝ => (cirGamma κ ξ + κ)
        * (Real.exp (cirGamma κ ξ * s) - 1) + 2 * cirGamma κ ξ)
      ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ)) t := by
    simpa using hasDerivAt_add' ((hexp.sub_const 1).const_mul (cirGamma κ ξ + κ))
      (hasDerivAt_const t (2 * cirGamma κ ξ))
  -- the denominator is positive, hence nonzero
  have hDne : (cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1)
      + 2 * cirGamma κ ξ ≠ 0 := by
    have hrw : (cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ
        = (cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * t) + (cirGamma κ ξ - κ) := by ring
    rw [hrw]
    exact ne_of_gt (add_pos (mul_pos hp1 (Real.exp_pos _)) hp2)
  -- the quotient-rule derivative value, in raw closed form
  have hq : HasDerivAt (fun s : ℝ => 2 * (Real.exp (cirGamma κ ξ * s) - 1) /
      ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * s) - 1) + 2 * cirGamma κ ξ))
      ((2 * (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ) *
          ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ) -
        2 * (Real.exp (cirGamma κ ξ * t) - 1) *
          ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ))) /
        ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ) ^ 2) t :=
    hnum.div hden hDne
  have hcoef4ne : (cirGamma κ ξ ^ 2 - κ ^ 2) / 4 ≠ 0 :=
    div_ne_zero (by rw [hgc2]; exact mul_ne_zero two_ne_zero hxi2)
      (by norm_num : (4:ℝ) ≠ 0)
  -- the algebraic identity: both numerator sides equal `4γ²E`
  have hval :
      ((2 * (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ) *
          ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ) -
        2 * (Real.exp (cirGamma κ ξ * t) - 1) *
          ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) * cirGamma κ ξ))) /
        ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ) ^ 2)
      = 1 - κ * (2 * (Real.exp (cirGamma κ ξ * t) - 1) /
          ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ))
        - ξ ^ 2 / 2 * (2 * (Real.exp (cirGamma κ ξ * t) - 1) /
          ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ)) ^ 2 := by
    rw [← hcoef4]
    field_simp
    ring
  rw [show cirBondB κ θ ξ = fun s : ℝ => 2 * (Real.exp (cirGamma κ ξ * s) - 1) /
      ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * s) - 1) + 2 * cirGamma κ ξ) from rfl]
  show HasDerivAt (fun s : ℝ => 2 * (Real.exp (cirGamma κ ξ * s) - 1) /
      ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * s) - 1) + 2 * cirGamma κ ξ))
    (1 - κ * (2 * (Real.exp (cirGamma κ ξ * t) - 1) /
        ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ))
      - ξ ^ 2 / 2 * (2 * (Real.exp (cirGamma κ ξ * t) - 1) /
        ((cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * t) - 1) + 2 * cirGamma κ ξ)) ^ 2) t
  rw [← hval]
  exact hq

/-- The **CIR log-`A` factor** (calendar time): the explicit antiderivative of
`κθ·B(T−·)` vanishing at `t = T`,

`A(t) = exp(−(2κθ/(γ+κ))·(T−t)) · (2γ / ((γ+κ) + (γ−κ)e^{−γ(T−t)}))^{2κθ/ξ²}`

(the integral `∫₀^τ B = (2/(γ+κ))τ − (4/((γ+κ)(γ−κ)))·log(2γ/((γ+κ)+(γ−κ)e^{−γτ}))`
with `(γ+κ)(γ−κ) = 2ξ²`; Brigo–Mercurio §3.9's `A(t,T)` in log form). -/
noncomputable def cirBondLogA (κ θ ξ T t : ℝ) : ℝ :=
  -(2 * κ * θ / (cirGamma κ ξ + κ)) * (T - t)
    + (2 * κ * θ / ξ ^ 2) * Real.log
        (2 * cirGamma κ ξ / ((cirGamma κ ξ + κ)
          + (cirGamma κ ξ - κ) * Real.exp (-(cirGamma κ ξ * (T - t)))))

/-- Terminal data: `A(T) = 1`, i.e. `C(T) = 0` (the log form vanishes: the first term
dies at `T − T = 0` and the logarithm sees `2γ/(2γ) = 1`). -/
theorem cirBondLogA_at_maturity (κ θ ξ T : ℝ) (hξ : ξ ≠ 0) :
    cirBondLogA κ θ ξ T T = 0 := by
  have hgne : cirGamma κ ξ ≠ 0 := cirGamma_ne_zero κ ξ hξ
  have h2 : 2 * cirGamma κ ξ / (cirGamma κ ξ + κ + (cirGamma κ ξ - κ)) = 1 := by
    have hsum : (cirGamma κ ξ + κ) + (cirGamma κ ξ - κ) = 2 * cirGamma κ ξ := by ring
    rw [hsum]; exact div_self (mul_ne_zero two_ne_zero hgne)
  simp only [cirBondLogA, sub_self, mul_zero, zero_add, neg_zero, Real.exp_zero, mul_one]
  rw [h2, Real.log_one, mul_zero]

/-- **The explicit-`A` ODE.** `d/dt cirBondLogA κ θ ξ T = κθ·B(T−t)` — the `C' = κθψ`
half of stage 3's calendar-time system, with `C` and `ψ` both explicit. Proof: direct
`HasDerivAt` chain rule on the closed form (the log's derivative cleans to
`−(γ−κ)γ/((γ+κ)E + (γ−κ))` after converting `e^{−γ(T−t)} = 1/E`), then one
`field_simp`/`ring` identity for the value. -/
theorem hasDerivAt_cirBondLogA (κ θ ξ T : ℝ) (hξ : ξ ≠ 0) (t : ℝ) :
    HasDerivAt (cirBondLogA κ θ ξ T) (κ * θ * cirBondB κ θ ξ (T - t)) t := by
  have hγpos : 0 < cirGamma κ ξ := cirGamma_pos κ ξ hξ
  obtain ⟨hκlt, hneg⟩ := cirGamma_abs_lt κ ξ hξ
  have hp1 : 0 < cirGamma κ ξ + κ := by linarith
  have hp2 : 0 < cirGamma κ ξ - κ := by linarith
  have hgne : cirGamma κ ξ ≠ 0 := ne_of_gt hγpos
  have hinv : Real.exp (-(cirGamma κ ξ * (T - t)))
      = 1 / Real.exp (cirGamma κ ξ * (T - t)) := by
    rw [Real.exp_neg, inv_eq_one_div]
  have hEne : Real.exp (cirGamma κ ξ * (T - t)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hp1ne : cirGamma κ ξ + κ ≠ 0 := ne_of_gt hp1
  have hdene : (cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t))
      + (cirGamma κ ξ - κ) ≠ 0 :=
    ne_of_gt (add_pos (mul_pos hp1 (Real.exp_pos _)) hp2)
  have hγsq := cirGamma_sq κ ξ
  have hgc2 : cirGamma κ ξ ^ 2 - κ ^ 2 = 2 * ξ ^ 2 := by rw [hγsq]; ring
  have hgc2ne : cirGamma κ ξ ^ 2 - κ ^ 2 ≠ 0 := by
    rw [hgc2]; exact mul_ne_zero two_ne_zero (pow_ne_zero 2 hξ)
  have hcoefne : (cirGamma κ ξ ^ 2 - κ ^ 2) / 2 ≠ 0 := div_ne_zero hgc2ne two_ne_zero
  have hbondene : (cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * (T - t)) - 1)
      + 2 * cirGamma κ ξ ≠ 0 := by
    have hrw : (cirGamma κ ξ + κ) * (Real.exp (cirGamma κ ξ * (T - t)) - 1)
        + 2 * cirGamma κ ξ
        = (cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ) := by
      ring
    rw [hrw]; exact hdene
  have hUne : (cirGamma κ ξ + κ) + (cirGamma κ ξ - κ)
      * Real.exp (-(cirGamma κ ξ * (T - t))) ≠ 0 :=
    ne_of_gt (add_pos hp1 (mul_pos hp2 (Real.exp_pos _)))
  have hUne2 : (cirGamma κ ξ + κ) + (cirGamma κ ξ - κ)
      / Real.exp (cirGamma κ ξ * (T - t)) ≠ 0 := by
    have h1 : (cirGamma κ ξ + κ) + (cirGamma κ ξ - κ)
        / Real.exp (cirGamma κ ξ * (T - t))
        = ((cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ))
          / Real.exp (cirGamma κ ξ * (T - t)) := by
      field_simp
    rw [h1]
    exact div_ne_zero hdene hEne
  -- chain-rule pieces
  have hts : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hw : HasDerivAt (fun s : ℝ => Real.exp (-(cirGamma κ ξ * (T - s))))
      (Real.exp (-(cirGamma κ ξ * (T - t))) * cirGamma κ ξ) t := by
    have hmul : HasDerivAt (fun s : ℝ => cirGamma κ ξ * (T - s))
        (cirGamma κ ξ * -1) t := hts.const_mul (cirGamma κ ξ)
    have hng : HasDerivAt (fun s : ℝ => -(cirGamma κ ξ * (T - s)))
        (-(cirGamma κ ξ * -1)) t := hmul.neg
    simpa using hng.exp
  have hU : HasDerivAt (fun s : ℝ => (cirGamma κ ξ + κ)
        + (cirGamma κ ξ - κ) * Real.exp (-(cirGamma κ ξ * (T - s))))
      ((cirGamma κ ξ - κ) * (Real.exp (-(cirGamma κ ξ * (T - t))) * cirGamma κ ξ)) t := by
    simpa using (hw.const_mul (cirGamma κ ξ - κ)).const_add (cirGamma κ ξ + κ)
  -- `d/dt log(2γ/U(t))`, via the log-of-quotient helper, cleaned into `E`-form
  -- (convert `e^{−γ(T−t)} = 1/E`)
  have hlogE : HasDerivAt (fun s : ℝ => Real.log (2 * cirGamma κ ξ /
        ((cirGamma κ ξ + κ) + (cirGamma κ ξ - κ) * Real.exp (-(cirGamma κ ξ * (T - s))))))
      (-((cirGamma κ ξ - κ) * cirGamma κ ξ /
        ((cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ)))) t := by
    have hlog := hasDerivAt_log_div_const (a := 2 * cirGamma κ ξ) hU
      (mul_ne_zero two_ne_zero hgne) hUne
    have hconv : -((cirGamma κ ξ - κ)
        * (Real.exp (-(cirGamma κ ξ * (T - t))) * cirGamma κ ξ) /
        ((cirGamma κ ξ + κ) + (cirGamma κ ξ - κ)
          * Real.exp (-(cirGamma κ ξ * (T - t)))))
      = -((cirGamma κ ξ - κ) * cirGamma κ ξ /
        ((cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ))) := by
      rw [hinv]
      field_simp
    simp only [hconv] at hlog
    exact hlog
  -- assemble the two terms of `cirBondLogA`
  have hterm1 : HasDerivAt (fun s : ℝ => -(2 * κ * θ / (cirGamma κ ξ + κ)) * (T - s))
      (-(2 * κ * θ / (cirGamma κ ξ + κ)) * -1) t := by
    simpa using hts.const_mul (-(2 * κ * θ / (cirGamma κ ξ + κ)))
  have hterm2 : HasDerivAt (fun s : ℝ => (2 * κ * θ / ξ ^ 2) * Real.log (2 * cirGamma κ ξ /
        ((cirGamma κ ξ + κ) + (cirGamma κ ξ - κ) * Real.exp (-(cirGamma κ ξ * (T - s))))))
      ((2 * κ * θ / ξ ^ 2) * -((cirGamma κ ξ - κ) * cirGamma κ ξ /
        ((cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ)))) t :=
    hlogE.const_mul (2 * κ * θ / ξ ^ 2)
  have hsum : HasDerivAt (cirBondLogA κ θ ξ T)
      (-(2 * κ * θ / (cirGamma κ ξ + κ)) * -1
        + (2 * κ * θ / ξ ^ 2) * -((cirGamma κ ξ - κ) * cirGamma κ ξ /
          ((cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ)))) t :=
    hasDerivAt_add' hterm1 hterm2
  -- final value identity: `C'(t) = κθ·B(T−t)`
  have hcoef : ξ ^ 2 = (cirGamma κ ξ ^ 2 - κ ^ 2) / 2 := by rw [hγsq]; ring
  have hval :
      (-(2 * κ * θ / (cirGamma κ ξ + κ)) * -1
        + (2 * κ * θ / ξ ^ 2) * -((cirGamma κ ξ - κ) * cirGamma κ ξ /
          ((cirGamma κ ξ + κ) * Real.exp (cirGamma κ ξ * (T - t)) + (cirGamma κ ξ - κ))))
      = κ * θ * cirBondB κ θ ξ (T - t) := by
    rw [hcoef]
    simp only [cirBondB]
    field_simp
    ring
  rw [hval] at hsum
  exact hsum

/-- The **calendar-time flip** of the CIR bond ODE: `ψ(t) = cirBondB κ θ ξ (T−t)` solves
`ψ' = κψ + (ξ²/2)ψ² − 1` — exactly the `hψ` hypothesis of `cirBondProfile_pde`
(chain rule: `ψ'(t) = −B'(T−t)`, the same flip that produced `B' = κB − 1` from
`B' = 1 − κB` in `bondProfile_pde`). -/
theorem hasDerivAt_cirBondCalendarB (κ θ ξ T : ℝ) (hξ : ξ ≠ 0) (s : ℝ) :
    HasDerivAt (fun w => cirBondB κ θ ξ (T - w))
      (κ * cirBondB κ θ ξ (T - s) + ξ ^ 2 / 2 * cirBondB κ θ ξ (T - s) ^ 2 - 1) s := by
  have hts : HasDerivAt (fun w : ℝ => T - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub T
  have hval : (1 - κ * cirBondB κ θ ξ (T - s) - ξ ^ 2 / 2 * cirBondB κ θ ξ (T - s) ^ 2) * -1
      = κ * cirBondB κ θ ξ (T - s) + ξ ^ 2 / 2 * cirBondB κ θ ξ (T - s) ^ 2 - 1 := by ring
  have hcomp : HasDerivAt (fun w : ℝ => cirBondB κ θ ξ (T - w))
      ((1 - κ * cirBondB κ θ ξ (T - s) - ξ ^ 2 / 2 * cirBondB κ θ ξ (T - s) ^ 2) * -1) s :=
    (hasDerivAt_cirBondB κ θ ξ (T - s) hξ).comp s hts
  rw [hval] at hcomp
  exact hcomp

/-- **The affine-form CIR bond assembly (antiderivative-hypothesis version).** For any
`C` integrating `C' = κθ·B(T−·)`, the exponential-affine profile with the explicit
`ψ(t) = cirBondB κ θ ξ (T−t)` satisfies the discounted CIR pricing PDE
`∂_t u + L u = v·u` — `cirBondProfile_pde` instantiated with the explicit closed-form
`B`-factor. -/
theorem cirBondPrice_affine (κ θ ξ : ℝ) (C : ℝ → ℝ) (T : ℝ) (hξ : ξ ≠ 0)
    (hC : ∀ s, HasDerivAt C (κ * θ * cirBondB κ θ ξ (T - s)) s) (t v : ℝ) :
    deriv (fun s => cirBondProfile κ θ ξ C (fun w => cirBondB κ θ ξ (T - w)) T s v) t
      + cirGenerator κ θ ξ
          (cirBondProfile κ θ ξ C (fun w => cirBondB κ θ ξ (T - w)) T t) v
      = v * cirBondProfile κ θ ξ C (fun w => cirBondB κ θ ξ (T - w)) T t v :=
  cirBondProfile_pde κ θ ξ C (fun w => cirBondB κ θ ξ (T - w)) T
    (hasDerivAt_cirBondCalendarB κ θ ξ T hξ) hC t v

/-- The **explicit CIR zero-coupon bond price** (calendar time):
`P(t, v) = e^{A(t) − B(T−t)·v}` with `A = cirBondLogA` and `B = cirBondB` — the CIR
analogue of the Vasicek affine form `P = e^{A − Bv}` (`vasicekBondPrice`). -/
noncomputable def cirBondPrice (κ θ ξ T t v : ℝ) : ℝ :=
  Real.exp (cirBondLogA κ θ ξ T t - cirBondB κ θ ξ (T - t) * v)

/-- Function form of `cirBondProfile` at a fixed `t` (definitional; needed because the
equation lemma only unfolds fully applied terms). -/
theorem cirBondProfile_fun (κ θ ξ : ℝ) (C ψ : ℝ → ℝ) (T t : ℝ) :
    cirBondProfile κ θ ξ C ψ T t = fun w => Real.exp (C t - ψ t * w) := rfl

/-- Function form of `cirBondPrice` at a fixed `(t)` (definitional). -/
theorem cirBondPrice_fun (κ θ ξ T t : ℝ) :
    cirBondPrice κ θ ξ T t
      = fun w => Real.exp (cirBondLogA κ θ ξ T t - cirBondB κ θ ξ (T - t) * w) := rfl

/-- Terminal condition: `P(T, v) = 1` — the zero-coupon payoff (uses `A(T) = 1` and
`B(0) = 0`). -/
theorem cirBondPrice_terminal (κ θ ξ T : ℝ) (hξ : ξ ≠ 0) (v : ℝ) :
    cirBondPrice κ θ ξ T T v = 1 := by
  simp only [cirBondPrice, sub_self, cirBondLogA_at_maturity κ θ ξ T hξ, cirBondB_at_zero,
    zero_mul, Real.exp_zero]

/-- **The CIR pricing-PDE theorem (stage 4 deliverable).** The explicit CIR bond price
`cirBondPrice` satisfies the discounted pricing PDE `∂_t P + L P = v · P` (Feynman–Kac
with discount rate `r = v`), where `L = cirGenerator κ θ ξ`, with terminal condition
`P(T, v) = 1` — the CIR analogue of `vasicekBondPrice_affine`, assembled by
instantiating `cirBondProfile_pde` with the explicit `ψ(t) = cirBondB κ θ ξ (T−t)` and
`C(t) = cirBondLogA κ θ ξ T t`. No `t < T` hypothesis is needed. -/
theorem cirBondPrice_pde (κ θ ξ T : ℝ) (hξ : ξ ≠ 0) (t v : ℝ) :
    deriv (fun s => cirBondPrice κ θ ξ T s v) t
      + cirGenerator κ θ ξ (cirBondPrice κ θ ξ T t) v
      = v * cirBondPrice κ θ ξ T t v := by
  have hpde := cirBondPrice_affine κ θ ξ (cirBondLogA κ θ ξ T) T hξ
    (fun s => hasDerivAt_cirBondLogA κ θ ξ T hξ s) t v
  simp only [cirBondProfile_fun] at hpde
  simp only [cirBondPrice, cirBondPrice_fun]
  exact hpde

#print axioms cirGamma
#print axioms cirGamma_sq
#print axioms cirGamma_pos
#print axioms cirGamma_ne_zero
#print axioms cirGamma_abs_lt
#print axioms cirBondB
#print axioms cirBondB_at_zero
#print axioms hasDerivAt_cirBondB
#print axioms cirBondLogA
#print axioms cirBondLogA_at_maturity
#print axioms hasDerivAt_cirBondLogA
#print axioms hasDerivAt_cirBondCalendarB
#print axioms cirBondPrice_affine
#print axioms cirBondPrice
#print axioms cirBondPrice_terminal
#print axioms cirBondPrice_pde

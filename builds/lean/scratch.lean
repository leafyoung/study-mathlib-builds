import MathFin.BlackScholes.Put
import MathFin.BlackScholes.StrikeConvexity

/-!
# Capstone (lesson 0017): put–call parity + put convexity in strike

My own formalizations. Answer keys (`bs_put_call_parity` in
`MathFin/BlackScholes/Put.lean`, the strike-convexity assembly in
`MathFin/BlackScholes/StrikeConvexity.lean`) were consulted only after each
attempt compiled clean.
-/

open MeasureTheory ProbabilityTheory Real MathFin

/-- **Put–call parity**, my attempt. Under the risk-neutral lognormal
hypothesis, the call and put on the same asset with the same strike and
maturity differ today by exactly spot minus the discounted strike:
a call plus `K·e^{-rT}` in cash buys a put plus the stock. -/
theorem bs_put_call_parity_mine {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    (∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q)
      - (∫ ω, Real.exp (-r * T) * max (K - bsTerminal S_0 r σ T (Z ω)) 0 ∂Q)
      = S_0 - K * Real.exp (-r * T) := by
  rw [bs_call_formula h, bs_put_formula h]
  have h1 := Phi_add_Phi_neg (bsd1 S_0 K r σ T)
  have h2 := Phi_add_Phi_neg (bsd2 S_0 K r σ T)
  linear_combination S_0 * h1 - K * Real.exp (-r * T) * h2

/-- **Convexity of the BS put in the strike**, my attempt. Paying a higher
strike costs more in every state, at an accelerating rate — the put price is
a convex function of `K`. -/
theorem bsP_strike_convexity_mine {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi 0) (fun K ↦ bsP K r σ S τ) := by
  -- Bridge: put = call (convex in K, upstream's `bsV_strike_convexOn`) + affine in K.
  have haff : ConvexOn ℝ (Set.Ioi 0)
      ((fun K : ℝ ↦ Real.exp (-(r * τ)) • K) + fun _ ↦ (-S : ℝ)) :=
    ((convexOn_id (convex_Ioi (0 : ℝ))).smul (Real.exp_nonneg _)).add_const (-S)
  refine ConvexOn.congr ((bsV_strike_convexOn (r := r) hS hσ hτ).add haff) ?_
  intro K _
  show bsV K r σ S τ + (Real.exp (-(r * τ)) • K + -S) = bsP K r σ S τ
  rw [bsP_eq_bsV, smul_eq_mul]
  ring

-- M5: the moment of the course — my theorems must stand on the three standard axioms.
#print axioms bs_put_call_parity_mine
#print axioms bsP_strike_convexity_mine

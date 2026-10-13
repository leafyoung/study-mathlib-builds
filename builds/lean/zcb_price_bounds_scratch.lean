import Mathlib

/-- Zero-coupon bond price `P = exp(-b * r₀)` for non-negative short rate `r₀`
and positive maturity-scaled coefficient `b`: strictly positive and at most 1. -/
theorem zcb_price_bounds (r₀ b : ℝ) (hr₀ : 0 ≤ r₀) (hb : 0 < b) :
    0 < Real.exp (-(b * r₀)) ∧ Real.exp (-(b * r₀)) ≤ 1 := by
  have hmul : 0 ≤ b * r₀ := mul_nonneg hb.le hr₀
  have hneg : -(b * r₀) ≤ 0 := by linarith
  exact ⟨Real.exp_pos _, (Real.exp_le_one_iff).mpr hneg⟩

#print axioms zcb_price_bounds

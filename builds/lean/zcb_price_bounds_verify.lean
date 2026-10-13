import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-- Zero-coupon bond price `P = exp (-(b * r₀))` under a non-negative short rate
`r₀` and a positive maturity-scaled coefficient `b` is strictly positive and at
most `1`. -/
theorem zcb_price_bounds (r₀ b : ℝ) (hr₀ : 0 ≤ r₀) (hb : 0 < b) :
    0 < Real.exp (-(b * r₀)) ∧ Real.exp (-(b * r₀)) ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · -- b * r₀ ≥ 0, hence -(b * r₀) ≤ 0, and exp is monotone with exp 0 = 1
    have hprod : 0 ≤ b * r₀ := mul_nonneg hb.le hr₀
    exact Real.exp_le_one_iff.mpr (by linarith)

#print axioms zcb_price_bounds

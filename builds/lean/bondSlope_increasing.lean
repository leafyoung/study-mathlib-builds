import Mathlib

/-- The bond slope function `τ ↦ (1 - e^(-(κ * τ))) / κ`. -/
noncomputable def bondSlopeFun (κ : ℝ) : ℝ → ℝ := fun τ => (1 - Real.exp (-(κ * τ))) / κ

theorem bondSlope_increasing (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) :
    0 < 1 - Real.exp (-(κ * τ)) ∧
    StrictMonoOn (bondSlopeFun κ) (Set.Ioi 0) := by
  constructor
  · -- Positivity: e^(-(κτ)) < e^0 = 1
    have hexp : Real.exp (-(κ * τ)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by linarith [mul_pos hκ hτ])
    rw [Real.exp_zero] at hexp
    linarith
  · -- Monotonicity: for 0 < a < b, divide out the (positive) denominator κ,
    -- then compare the exponentials.
    intro a ha b hb hab
    have hexp : Real.exp (-(κ * b)) < Real.exp (-(κ * a)) :=
      Real.exp_lt_exp.mpr (by linarith [mul_lt_mul_of_pos_left hab hκ])
    simp only [bondSlopeFun, Set.mem_Ioi] at ha hb ⊢
    rw [div_lt_div_iff_of_pos_right hκ]
    linarith

#print axioms bondSlope_increasing

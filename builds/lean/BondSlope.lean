import Mathlib

noncomputable def bondSlopeFun (κ : ℝ) : ℝ → ℝ := fun τ => (1 - Real.exp (-(κ * τ))) / κ

theorem bondSlope_increasing (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (h : ∀ x, bondSlopeFun κ x = (1 - Real.exp (-(κ * x))) / κ) :
    0 < 1 - Real.exp (-(κ * τ)) ∧
    StrictMonoOn (bondSlopeFun κ) (Set.Ioi 0) := by
  constructor
  · have hpos : 0 < κ * τ := mul_pos hκ hτ
    have hexp : Real.exp (-(κ * τ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at hexp
    linarith
  · intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have hexp : Real.exp (-(κ * b)) < Real.exp (-(κ * a)) := by
      apply Real.exp_lt_exp.mpr
      have : κ * a < κ * b := mul_lt_mul_of_pos_left hab hκ
      linarith
    simp only [h]
    rw [div_lt_div_iff_of_pos_right hκ]
    linarith

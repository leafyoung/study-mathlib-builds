import Mathlib
noncomputable def bondSlopeFun (κ : ℝ) : ℝ → ℝ := fun τ => (1 - Real.exp (-(κ * τ))) / κ
theorem bondSlope_increasing (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) :
    0 < 1 - Real.exp (-(κ * τ)) ∧
    StrictMonoOn (bondSlopeFun κ) (Set.Ioi 0) := by
  have hexp : Real.exp (-(κ * τ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [mul_pos hκ hτ])
  refine ⟨by linarith, ?_⟩
  intro a _ha b _hb hlt
  have hexpab : Real.exp (-(κ * b)) < Real.exp (-(κ * a)) :=
    Real.exp_lt_exp.mpr (by linarith [mul_lt_mul_of_pos_left hlt hκ])
  show (1 - Real.exp (-(κ * a))) / κ < (1 - Real.exp (-(κ * b))) / κ
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  field_simp
  linarith
#print axioms bondSlope_increasing

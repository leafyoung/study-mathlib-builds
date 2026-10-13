import Mathlib

open Set

/-! Version A — `bondSlopeFun` opaque, definition supplied as a hypothesis. -/
theorem bondSlope_increasing (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (bondSlopeFun : ℝ → ℝ → ℝ)
    (hdef : ∀ κ t : ℝ, bondSlopeFun κ t = (1 - Real.exp (-(κ * t))) / κ) :
    0 < 1 - Real.exp (-(κ * τ)) ∧
    StrictMonoOn (bondSlopeFun κ) (Set.Ioi 0) := by
  have hexp : Real.exp (-(κ * τ)) < 1 := by
    have h2 := Real.exp_lt_exp.mpr (show -(κ * τ) < 0 by linarith [mul_pos hκ hτ])
    simpa using h2
  refine ⟨by linarith, ?_⟩
  intro τ₁ _h₁ τ₂ _h₂ h
  rw [hdef κ τ₁, hdef κ τ₂]
  have hexpab : Real.exp (-(κ * τ₂)) < Real.exp (-(κ * τ₁)) :=
    Real.exp_lt_exp.mpr (by linarith [mul_lt_mul_of_pos_left h hκ])
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  field_simp
  linarith

/-! Version B — concrete definition, no hypothesis needed. -/
noncomputable def bondSlopeFun (κ : ℝ) : ℝ → ℝ := fun τ => (1 - Real.exp (-(κ * τ))) / κ

theorem bondSlope_increasing' (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) :
    0 < 1 - Real.exp (-(κ * τ)) ∧
    StrictMonoOn (bondSlopeFun κ) (Set.Ioi 0) := by
  have hexp : Real.exp (-(κ * τ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [mul_pos hκ hτ])
  refine ⟨by linarith, ?_⟩
  intro τ₁ _h₁ τ₂ _h₂ h
  show (1 - Real.exp (-(κ * τ₁))) / κ < (1 - Real.exp (-(κ * τ₂))) / κ
  have hexpab : Real.exp (-(κ * τ₂)) < Real.exp (-(κ * τ₁)) :=
    Real.exp_lt_exp.mpr (by linarith [mul_lt_mul_of_pos_left h hκ])
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  field_simp
  linarith

#print axioms bondSlope_increasing
#print axioms bondSlope_increasing'

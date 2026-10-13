import Mathlib

open Set

theorem bondSlope_increasing (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (bondSlopeFun : ℝ → ℝ → ℝ)
    (hdef : ∀ κ t : ℝ, bondSlopeFun κ t = (1 - Real.exp (-(κ * t))) / κ) :
    0 < 1 - Real.exp (-(κ * τ)) ∧
    StrictMonoOn (bondSlopeFun κ) (Set.Ioi 0) := by
  have hpos : ∀ t : ℝ, 0 < t → 0 < 1 - Real.exp (-(κ * t)) := by
    intro t ht
    have h1 : Real.exp (-(κ * t)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by linarith [mul_pos hκ ht])
    linarith
  refine ⟨hpos τ hτ, ?_⟩
  intro a _ha b _hb hab
  rw [hdef κ a, hdef κ b]
  refine div_lt_div_of_pos_right ?_ hκ
  have hlt : Real.exp (-(κ * b)) < Real.exp (-(κ * a)) :=
    Real.exp_lt_exp.2 (by linarith [mul_lt_mul_of_pos_left hab hκ])
  linarith

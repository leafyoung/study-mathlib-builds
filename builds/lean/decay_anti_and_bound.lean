import Mathlib

theorem decay_anti_and_bound (κ : ℝ) (hκ : 0 < κ) :
    StrictAntiOn (fun τ : ℝ => Real.exp (-(κ * τ))) (Set.Ioi 0) ∧
    ∀ τ ∈ Set.Ioi (0 : ℝ), (1 - Real.exp (-(κ * τ))) / κ < 1 / κ := by
  constructor
  · intro a _ha b _hb hab
    exact Real.exp_lt_exp.mpr (neg_lt_neg (mul_lt_mul_of_pos_left hab hκ))
  · intro τ _hτ
    rw [div_lt_div_iff_of_pos_right hκ]
    linarith [Real.exp_pos (-(κ * τ))]

#print axioms decay_anti_and_bound

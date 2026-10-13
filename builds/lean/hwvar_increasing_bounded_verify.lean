import Mathlib

noncomputable def hwVarFun (σ κ t : ℝ) : ℝ := σ ^ 2 * (1 - Real.exp (-(2 * κ * t))) / (2 * κ)

theorem hwVar_increasing_bounded (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMonoOn (hwVarFun σ κ) (Set.Ioi 0) ∧
    ∀ t ∈ Set.Ioi (0 : ℝ), hwVarFun σ κ t < σ ^ 2 / (2 * κ) := by
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hσ)
  have hc : 0 < σ ^ 2 / (2 * κ) := div_pos hσ2 (by linarith)
  have hEq : ∀ t : ℝ, hwVarFun σ κ t = σ ^ 2 / (2 * κ) * (1 - Real.exp (-(2 * κ * t))) := by
    intro t
    simp only [hwVarFun, div_mul_eq_mul_div]
  constructor
  · intro a _ha b _hb hab
    have hexp : Real.exp (-(2 * κ * b)) < Real.exp (-(2 * κ * a)) := by
      rw [Real.exp_lt_exp]
      have h1 : a * κ < b * κ := mul_lt_mul_of_pos_right hab hκ
      linarith
    rw [hEq a, hEq b]
    exact mul_lt_mul_of_pos_left (by linarith) hc
  · intro t _
    have hE : 0 < Real.exp (-(2 * κ * t)) := Real.exp_pos _
    rw [hEq t]
    have h1 : (1:ℝ) - Real.exp (-(2 * κ * t)) < 1 := by linarith
    have h2 := mul_lt_mul_of_pos_left h1 hc
    linarith

import MathFin.BlackScholes.PutGreeks

/-!
# Greeks sign theorems, from primitives

Track-1 continuation of the lesson-0017 capstone (put-call parity + put-strike
convexity in `scratch.lean`): the Black-Scholes **sign constraints** of lesson
0029, attempted from primitives - the closed-form atoms `Phi`, `bsd1`, `bsd2`,
`Real.exp` and Mathlib's `HasDerivAt` calculus. The sealed answer key is
`MathFin/BlackScholes/GreekSigns.lean`; it is to be opened for diffing only
after the attempts below compile clean.

Import note (grep-verified): the planned `MathFin.BlackScholes.Put` imports
only `Call` -> `StandardNormal` transitively - `bsV` is defined in
`BlackScholes.PDE` and `bsP` / `bsP_eq_bsV` in `BlackScholes.PutGreeks`. This
file therefore imports `PutGreeks`, which transitively carries `Put`, `PDE`
and the Phi-derivative file `Foundations.GaussianCDFDeriv` (`hasDerivAt_Phi`).
The workspace `mathfin/` clone additionally has `Foundations.DerivOfDeriv`
(`hasDerivAt_deriv_of_eventually`), but the pinned dependency of this repo
(rev 784a831) predates that module, so the `deriv`-form gamma below is proved
from Mathlib's `HasDerivAt.deriv` + `HasDerivAt.congr_of_eventuallyEq`
directly.
-/

open MeasureTheory ProbabilityTheory Real MathFin
open scoped NNReal

/-! ### Primitives: derivatives of `d₁`, `d₂` in spot and rate (mine) -/

/-- `∂_S d₁ = 1 / (S σ √τ)`, from the log-derivative chain. -/
lemma hasDerivAt_bsd1_S_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsd1 s K r σ τ) (1 / (S * σ * Real.sqrt τ)) S := by
  have hD : σ * Real.sqrt τ ≠ 0 := mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr hτ).ne'
  have hquot : HasDerivAt (fun s : ℝ ↦ s / K) (1 / K) S := (hasDerivAt_id S).div_const K
  have hlog : HasDerivAt (fun s : ℝ ↦ Real.log (s / K)) (1 / S) S := by
    have h := hquot.log (div_ne_zero hS.ne' hK.ne')
    have hval : (1 : ℝ) / K / (S / K) = 1 / S := by field_simp
    rw [hval] at h
    exact h
  have h := (hlog.add_const ((r + σ ^ 2 / 2) * τ)).div_const (σ * Real.sqrt τ)
  refine h.congr_deriv ?_
  ring

/-- `∂_S d₂ = 1 / (S σ √τ)` - same as `d₁`, since `d₂ = d₁ - σ√τ`. -/
lemma hasDerivAt_bsd2_S_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsd2 s K r σ τ) (1 / (S * σ * Real.sqrt τ)) S :=
  (hasDerivAt_bsd1_S_mine hK hσ hS hτ).sub_const (σ * Real.sqrt τ)

/-- `∂_r d₁ = √τ / σ`. -/
lemma hasDerivAt_bsd1_r_mine {S K σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (r : ℝ) :
    HasDerivAt (fun r' ↦ bsd1 S K r' σ τ) (Real.sqrt τ / σ) r := by
  have hD : σ * Real.sqrt τ ≠ 0 := mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr hτ).ne'
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h0 : HasDerivAt (fun _ : ℝ ↦ Real.log (S / K)) 0 r := hasDerivAt_const _ _
  have h1 : HasDerivAt (fun r' : ℝ ↦ (r' + σ ^ 2 / 2) * τ) (1 * τ) r :=
    ((hasDerivAt_id r).add_const (σ ^ 2 / 2)).mul_const τ
  have h := (h0.add h1).div_const (σ * Real.sqrt τ)
  refine h.congr_deriv ?_
  rw [zero_add, one_mul, div_eq_div_iff hD hσ.ne']
  linear_combination -(σ * hsq)

/-- `∂_r d₂ = √τ / σ` - same as `d₁`. -/
lemma hasDerivAt_bsd2_r_mine {S K σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (r : ℝ) :
    HasDerivAt (fun r' ↦ bsd2 S K r' σ τ) (Real.sqrt τ / σ) r :=
  (hasDerivAt_bsd1_r_mine hσ hτ r).sub_const (σ * Real.sqrt τ)

/-! ### The magic identity -/

/-- **The magic identity** `S ϕ(d₁) = K e^{-rτ} ϕ(d₂)`: the spot-weighted
standard-normal densities at `d₁` and `d₂` agree once discounted. The one
nontrivial algebraic input behind delta and rho - it says the two density
terms cancel in `∂_S V` and `∂_r V`. -/
theorem bs_phi_magic_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    S * gaussianPDFReal 0 1 (bsd1 S K r σ τ)
      = K * Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) := by
  have hSK : 0 < S / K := div_pos hS hK
  have hD : σ * Real.sqrt τ ≠ 0 := mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr hτ).ne'
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hdd : bsd1 S K r σ τ - bsd2 S K r σ τ = σ * Real.sqrt τ := by
    rw [bsd2]; ring
  -- (d₁ + d₂) · σ√τ = 2·(log(S/K) + rτ), from the closed forms
  have hsum : (bsd1 S K r σ τ + bsd2 S K r σ τ) * (σ * Real.sqrt τ)
      = 2 * (Real.log (S / K) + r * τ) := by
    rw [bsd2, bsd1]
    field_simp [hsq]
    rw [hsq]
    ring
  -- the exponential gap: d₁²/2 - d₂²/2 = log(S/K) + rτ
  have hkey : (bsd1 S K r σ τ) ^ 2 / 2 - (bsd2 S K r σ τ) ^ 2 / 2
      = Real.log (S / K) + r * τ := by
    have hsplit : (bsd1 S K r σ τ) ^ 2 / 2 - (bsd2 S K r σ τ) ^ 2 / 2
        = ((bsd1 S K r σ τ) ^ 2 - (bsd2 S K r σ τ) ^ 2) / 2 := by ring
    rw [hsplit, sq_sub_sq, hdd, hsum]
    ring
  -- move the gap into the exponential, then close
  have hcore : S * Real.exp (-(bsd1 S K r σ τ ^ 2 / 2))
      = K * Real.exp (-(r * τ)) * Real.exp (-(bsd2 S K r σ τ ^ 2 / 2)) := by
    have hstep : Real.exp (-(bsd1 S K r σ τ ^ 2 / 2))
        = Real.exp (-(bsd2 S K r σ τ ^ 2 / 2) - (Real.log (S / K) + r * τ)) := by
      congr 1
      linarith
    rw [hstep, Real.exp_sub, Real.exp_neg, Real.exp_add, Real.exp_log hSK, Real.exp_neg]
    field_simp [hS.ne', hK.ne', Real.exp_ne_zero]
  have hpdf : S * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(bsd1 S K r σ τ) ^ 2 / 2))
      = K * Real.exp (-(r * τ))
          * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(bsd2 S K r σ τ) ^ 2 / 2)) := by
    have hbridge : ∀ z : ℝ, Real.exp (-(z ^ 2) / 2) = Real.exp (-(z ^ 2 / 2)) := by
      intro z
      rw [neg_div]
    rw [hbridge, hbridge, mul_left_comm, hcore]
    ring
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact hpdf

/-! ### 1. Delta bounds -/

/-- **Delta is nonnegative**: the call delta `Φ(d₁)` is a probability, hence
`≥ 0` - the call's value increases with the underlying (monotone payoff). -/
theorem bsV_delta_nonneg_mine (S K r σ τ : ℝ) : 0 ≤ Phi (bsd1 S K r σ τ) :=
  Phi_nonneg _

/-- **Delta is at most one**: `Φ(d₁) ≤ 1` - a dollar move of the stock moves
the call by at most a dollar (the call is dominated by the stock). -/
theorem bsV_delta_le_one_mine (S K r σ τ : ℝ) : Phi (bsd1 S K r σ τ) ≤ 1 :=
  Phi_le_one _

/-- **Delta, as a derivative**: `∂_S V = Φ(d₁)` - the magic identity cancels
every density term. -/
theorem hasDerivAt_bsV_S_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S := by
  have hΦ1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S (hasDerivAt_bsd1_S_mine hK hσ hS hτ)
  have hΦ2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S (hasDerivAt_bsd2_S_mine hK hσ hS hτ)
  have hterm1 := (hasDerivAt_id S).mul hΦ1
  have hterm2 := (hasDerivAt_const S (K * Real.exp (-(r * τ)))).mul hΦ2
  refine (hterm1.sub hterm2).congr_deriv ?_
  simp only [Function.comp_apply, id_eq, one_mul, zero_mul, zero_add, ← mul_assoc]
  rw [bs_phi_magic_mine hK hσ hS hτ]
  ring

/-! ### 2. Gamma positive -/

/-- **Gamma, in pdf-quotient form**: the derivative of the delta function
`s ↦ Φ(d₁(s))` in `S` is `ϕ(d₁) / (S σ √τ)`. -/
theorem hasDerivAt_Phi_bsd1_S_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ Phi (bsd1 s K r σ τ))
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ)) S := by
  have h := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S (hasDerivAt_bsd1_S_mine hK hσ hS hτ)
  refine h.congr_deriv ?_
  rw [mul_one_div]

/-- **Gamma is positive**: `ϕ(d₁) / (S σ √τ) > 0` - the kinked call payoff is
convex in the underlying. -/
theorem bsV_gamma_pos_mine {K r σ : ℝ} (hσ : 0 < σ) {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    0 < gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ) :=
  div_pos (gaussianPDFReal_pos 0 1 _ (one_ne_zero : (1 : ℝ≥0) ≠ 0))
    (mul_pos (mul_pos hS hσ) (Real.sqrt_pos.mpr hτ))

/-- Gamma of the call price itself, as a derivative statement:
`deriv (fun s ↦ bsV K r σ s τ)` exists near `S > 0` and its derivative there
is `ϕ(d₁)/(S σ √τ)`. (The pinned MathFin lacks the `DerivOfDeriv` bridge, so
this goes through Mathlib's `HasDerivAt.deriv` and an eventual equality.) -/
theorem hasDerivAt_deriv_bsV_S_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (deriv fun s ↦ bsV K r σ s τ)
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ)) S := by
  have hev : (deriv fun s ↦ bsV K r σ s τ)
      =ᶠ[nhds S] (fun s ↦ Phi (bsd1 s K r σ τ)) := by
    filter_upwards [(eventually_gt_nhds hS)] with s hs
    exact (hasDerivAt_bsV_S_mine (r := r) hK hσ hs hτ).deriv
  exact (hasDerivAt_Phi_bsd1_S_mine hK hσ hS hτ).congr_of_eventuallyEq hev

/-! ### 3. Rho nonneg -/

/-- **Rho, as a derivative**: `∂_r V = K τ e^{-rτ} Φ(d₂)` - again the magic
identity cancels the density terms. -/
theorem hasDerivAt_bsV_r_mine {K σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (r : ℝ) :
    HasDerivAt (fun r' ↦ bsV K r' σ S τ)
      (K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) r := by
  have hΦ1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp r (hasDerivAt_bsd1_r_mine hσ hτ r)
  have hΦ2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp r (hasDerivAt_bsd2_r_mine hσ hτ r)
  have hexp : HasDerivAt (fun r' : ℝ ↦ Real.exp (-(r' * τ)))
      (Real.exp (-(r * τ)) * -τ) r := by
    have h1 : HasDerivAt (fun r' : ℝ ↦ r' * τ) τ r := hasDerivAt_mul_const τ
    exact h1.neg.exp
  have hterm1 := (hasDerivAt_const r S).mul hΦ1
  have hterm2 := (hexp.const_mul K).mul hΦ2
  refine (hterm1.sub hterm2).congr_deriv ?_
  simp only [Function.comp_apply, zero_mul, zero_add, ← mul_assoc]
  rw [bs_phi_magic_mine hK hσ hS hτ]
  ring

/-- **Rho is nonnegative**: `K τ e^{-rτ} Φ(d₂) ≥ 0` from `K, τ ≥ 0` and
`Φ ≥ 0` - the call is long the discount rate (the strike is paid later). -/
theorem bsV_rho_nonneg_mine {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) (r σ S : ℝ) :
    0 ≤ K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) :=
  mul_nonneg (mul_nonneg (mul_nonneg hK hτ) (Real.exp_nonneg _)) (Phi_nonneg _)

/-- **Call decreasing in strike**: `-e^{-rτ} Φ(d₂) ≤ 0` - a more
out-of-the-money call is worth less. -/
theorem bsV_partial_K_nonpos_mine (S K r σ τ : ℝ) :
    -(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) ≤ 0 :=
  neg_nonpos.mpr (mul_nonneg (Real.exp_nonneg _) (Phi_nonneg _))

/-- **Call convex in strike**: `e^{-rτ} ϕ(d₂) / (K σ √τ) ≥ 0` for
`K, σ, τ > 0` - the infinitesimal face of butterfly nonnegativity; via
Breeden-Litzenberger, `e^{-rτ}` times the implied PDF, which is nonnegative
because it *is* a probability density. -/
theorem bsV_partial_KK_nonneg_mine {K σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    (S r : ℝ) :
    0 ≤ Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
          (K * σ * Real.sqrt τ) :=
  div_nonneg (mul_nonneg (Real.exp_nonneg _) (gaussianPDFReal_nonneg _ _ _))
    (mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hτ)).le

/-! ### 4. Put delta -/

/-- **Put delta, as a derivative**: `∂_S P = -Φ(-d₁)` - put-call parity
differentiated in `S`, with `Φ(d₁) - 1 = -Φ(-d₁)`. -/
theorem hasDerivAt_bsP_S_mine {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsP K r σ s τ) (-(Phi (-(bsd1 S K r σ τ)))) S := by
  have hfun : (fun s : ℝ ↦ bsP K r σ s τ)
      = fun s ↦ bsV K r σ s τ - s + K * Real.exp (-(r * τ)) := by
    funext s
    exact bsP_eq_bsV K r σ s τ
  rw [hfun]
  have h1 := hasDerivAt_bsV_S_mine (r := r) hK hσ hS hτ
  have h2 : HasDerivAt (fun s : ℝ ↦ s) 1 S := hasDerivAt_id S
  have h3 : HasDerivAt (fun _ : ℝ ↦ K * Real.exp (-(r * τ))) 0 S := hasDerivAt_const _ _
  refine ((h1.sub h2).add h3).congr_deriv ?_
  rw [Phi_neg]
  ring

/-- **Put delta is nonpositive**: `-Φ(-d₁) ≤ 0` - the put loses when the
stock gains. -/
theorem bsP_delta_nonpos_mine (S K r σ τ : ℝ) : -(Phi (-(bsd1 S K r σ τ))) ≤ 0 :=
  neg_nonpos.mpr (Phi_nonneg _)

/-! ### 5. The model-free butterfly -/

/-- **The butterfly, model-free**: the call payoff `max (S - K) 0` is convex
in the underlying - the max of the affine `S ↦ S - K` and the constant `0`.
No Black-Scholes hypothesis anywhere. -/
theorem call_payoff_convex_mine (K : ℝ) : ConvexOn ℝ Set.univ (fun S : ℝ => max (S - K) 0) :=
  ConvexOn.congr (((convexOn_id convex_univ).add_const (-K)).sup (convexOn_const 0 convex_univ))
    (fun _ _ => rfl)

/-- The butterfly corollary: the **second difference** of the call payoff is
nonnegative - for `x ≤ y ≤ z`, the `K`-butterfly `(z-y)·f(x) + (y-x)·f(z) -
(z-x)·f(y)` pays `≥ 0`, i.e. no static arbitrage. -/
theorem call_second_difference_nonneg_mine (K x y z : ℝ) (hxz : x < z)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    0 ≤ (z - y) * max (x - K) 0 + (y - x) * max (z - K) 0 - (z - x) * max (y - K) 0 := by
  have hxz_ne : z - x ≠ 0 := sub_ne_zero.mpr hxz.ne.symm
  have hconv := call_payoff_convex_mine K
  set a : ℝ := (z - y) / (z - x) with ha
  set b : ℝ := (y - x) / (z - x) with hb
  have hab : a + b = 1 := by
    rw [ha, hb, ← add_div, div_eq_iff hxz_ne]
    ring
  have hcomb := hconv.2 (Set.mem_univ x) (Set.mem_univ z)
    (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith)) hab
  simp only [smul_eq_mul] at hcomb
  have hy : a * x + b * z = y := by
    rw [ha, hb]
    field_simp
    ring
  rw [hy] at hcomb
  have h1 : (z - x) * (a * max (x - K) 0) = (z - y) * max (x - K) 0 := by
    rw [ha]
    field_simp
  have h2 : (z - x) * (b * max (z - K) 0) = (y - x) * max (z - K) 0 := by
    rw [hb]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hcomb (by linarith : (0 : ℝ) ≤ z - x)
  rw [mul_add, h1, h2] at hmul
  linarith

-- The moment of the course: every headline theorem on the three standard axioms.
#print axioms bsV_delta_nonneg_mine
#print axioms bsV_delta_le_one_mine
#print axioms hasDerivAt_bsV_S_mine
#print axioms hasDerivAt_Phi_bsd1_S_mine
#print axioms bsV_gamma_pos_mine
#print axioms hasDerivAt_deriv_bsV_S_mine
#print axioms hasDerivAt_bsV_r_mine
#print axioms bsV_rho_nonneg_mine
#print axioms bsV_partial_K_nonpos_mine
#print axioms bsV_partial_KK_nonneg_mine
#print axioms hasDerivAt_bsP_S_mine
#print axioms bsP_delta_nonpos_mine
#print axioms call_payoff_convex_mine
#print axioms call_second_difference_nonneg_mine

import Mathlib
import MathFin.Foundations.FeynmanKacHeatEquation

/-!
# The constant-coefficient forward (Fokker-Planck) equation — stage 1

Pure calculus on the Gaussian density: the *forward* (adjoint) half of the generator
story, for the constant-coefficient diffusion `x₀ + μ·t + σ·B_t`. This is stage 1 of
the build that unblocks lessons 0054/0058/0060 and, downstream, the Dupire numerator
of lesson 0021 (general FK with drift is stage 2; the Gyöngy/Dupire scaling is stage 3).

Substrate: `MathFin/Foundations/FeynmanKacHeatEquation.lean` — its public heat kernel
`K(v, y) = (2πv)^{-1/2} · e^{-y²/(2v)}` (so `K(v, ·)` is the `N(0, v)` density; Mathlib's
`gaussianPDFReal` takes the *variance* as its second argument) and its public
curve-derivative lemma `hasDerivAt_heatKernel_comp`. The kernel's `y`/`t`/`yy` derivative
lemmas in that file are `private`, so the pdf-PDE facts are re-derived here through the
public curve lemma — no duplication of the private calculus.

## Main results

* `heatKernel_heat` — the heat-kernel pdf PDE in `deriv` form: `∂_t K = ½ ∂²_y K`.
* `pden` / `pdenx` / `pdenxx` — the density of `x₀ + μ·t + σ·B_t` and its first two
  spatial derivatives, with `hasDerivAt_pden_t` / `hasDerivAt_pden_x` / `hasDerivAt_pdenx_x`.
* `forward_eq_constant_drift` — `∂_t p = -μ ∂_x p + (σ²/2) ∂²_x p` for `t > 0`
  (Vasicek/Hull-White-shaped transport + heat), proved **directly**;
  `forward_eq_driftless` is its `μ = 0` corollary.
* `pden_zero_drift_eq_gaussianPDFReal` — bridge to Mathlib's `gaussianPDFReal`.
* `forward_eq_convolution` — the migration lemma: the same forward equation for the
  convolved density `u(t, x) = ∫_{[a,b]} g(y)·p(t, x−y) dy` (continuous bounded `g`),
  by differentiating under the integral with an explicit constant domination.
  This is the Dupire-relevant seed.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real
open MathFin.FeynmanKacHeatEquation

namespace ForwardEqScratch

/-! ## Shifted heat-kernel derivatives

`hasDerivAt_heatKernel_comp` differentiates `s ↦ K(v s, z − w s)` in `s` with the kernel
*argument* `z − w s` moving through the centre. The two lemmas below give the
argument-derivatives of the mean-shifted kernel `y ↦ K(v, y − m)`. -/

/-- First derivative in the argument of the mean-shifted heat kernel:
`∂_y K(v, y − m) = -((y − m)/v) · K(v, y − m)` for `v > 0`. -/
lemma hasDerivAt_heatKernel_shift {v m y : ℝ} (_hv : 0 < v) :
    HasDerivAt (fun y' ↦ heatKernel v (y' - m))
      (-(y - m) / v * heatKernel v (y - m)) y := by
  have hsub : HasDerivAt (fun y' : ℝ ↦ y' - m) 1 y :=
    (hasDerivAt_id y).sub_const m
  -- the raw derivative, in exactly the shape the `HasDerivAt` combinators produce
  have hraw := (((hsub.mul hsub).neg.div_const (2 * v)).exp).const_mul
    ((Real.sqrt (2 * Real.pi * v))⁻¹)
  -- transport: unfold `heatKernel` and match the exponent / value forms by `ring`
  have hsq : ∀ r : ℝ, -((r - m) * (r - m)) / (2 * v) = -(r - m) ^ 2 / (2 * v) := fun r => by ring
  have hfun : (fun y' ↦ heatKernel v (y' - m)) = fun y' : ℝ ↦ (Real.sqrt (2 * Real.pi * v))⁻¹
      * Real.exp (-((y' - m) * (y' - m)) / (2 * v)) := by
    funext y'
    rw [heatKernel, hsq y']
  have hval : -(y - m) / v * heatKernel v (y - m)
      = (Real.sqrt (2 * Real.pi * v))⁻¹ * (Real.exp (-((y - m) * (y - m)) / (2 * v))
        * (-((1 * (y - m) + (y - m) * 1 : ℝ)) / (2 * v))) := by
    rw [heatKernel, hsq y]
    ring
  rw [hfun, hval]
  exact hraw

/-- Second derivative in the argument of the mean-shifted heat kernel:
`∂²_y K(v, y − m) = K(v, y − m) · ((y − m)² − v)/v²` for `v > 0`. -/
lemma hasDerivAt_heatKernel_shift2 {v m y : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y' ↦ -(y' - m) / v * heatKernel v (y' - m))
      (heatKernel v (y - m) * ((y - m) ^ 2 - v) / v ^ 2) y := by
  have hsub : HasDerivAt (fun y' : ℝ ↦ y' - m) 1 y :=
    (hasDerivAt_id y).sub_const m
  have hfb := hasDerivAt_heatKernel_shift (v := v) (m := m) (y := y) hv
  -- the raw product-rule derivative, in the shape the combinators produce
  have hcm : HasDerivAt (fun y' : ℝ ↦ -(1 / v) * ((y' - m) * heatKernel v (y' - m)))
      (-(1 / v) * (1 * heatKernel v (y - m)
        + (y - m) * (-(y - m) / v * heatKernel v (y - m)))) y :=
    (hsub.mul hfb).const_mul (-(1 / v))
  -- transport: function form (ring on the shifted-kernel atom) and value form
  have hfun : (fun y' ↦ -(y' - m) / v * heatKernel v (y' - m))
      = fun y' : ℝ ↦ -(1 / v) * ((y' - m) * heatKernel v (y' - m)) := by
    funext y'
    ring
  have hval : heatKernel v (y - m) * ((y - m) ^ 2 - v) / v ^ 2
      = -(1 / v) * (1 * heatKernel v (y - m)
        + (y - m) * (-(y - m) / v * heatKernel v (y - m))) := by
    have hvne : v ≠ 0 := hv.ne'
    field_simp
    ring
  rw [hfun, hval]
  exact hcm

/-- Unshifted specialisations, in the exact forms the deliverables need. -/
lemma hasDerivAt_heatKernel_shift0 {v y : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y' ↦ heatKernel v y') (-(y / v) * heatKernel v y) y := by
  have h := hasDerivAt_heatKernel_shift (v := v) (m := 0) (y := y) hv
  have he : (fun y' ↦ heatKernel v y') = (fun y' ↦ heatKernel v (y' - 0)) := by
    funext z; rw [sub_zero]
  have hval : -(y / v) * heatKernel v y = -(y - 0) / v * heatKernel v (y - 0) := by
    rw [sub_zero]; ring
  rw [he, hval]
  exact h

lemma hasDerivAt_heatKernel_shift2_0 {v y : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y' ↦ -(y' / v) * heatKernel v y')
      (heatKernel v y * (y ^ 2 - v) / v ^ 2) y := by
  have h := hasDerivAt_heatKernel_shift2 (v := v) (m := 0) (y := y) hv
  have he : (fun y' ↦ -(y' / v) * heatKernel v y')
      = (fun y' ↦ -(y' - 0) / v * heatKernel v (y' - 0)) := by
    funext z; rw [sub_zero]; ring
  have hval : heatKernel v y * (y ^ 2 - v) / v ^ 2
      = heatKernel v (y - 0) * ((y - 0) ^ 2 - v) / v ^ 2 := by
    rw [sub_zero]
  rw [he, hval]
  exact h

/-! ## Deliverable 1 — the heat-kernel pdf PDE

`∂_t K = ½ ∂²_y K` for the Gaussian density in its (variance-)time variable. The
corresponding lemmas in `FeynmanKacHeatEquation.lean` (`hasDerivAt_heatKernel_t`,
`hasDerivAt_heatKernel_y_y`, `heatKernel_t_eq_half_y_y`) are `private`, so this is
re-derived through the public `hasDerivAt_heatKernel_comp` and the two shift lemmas. -/

/-- **The Gaussian density is a heat kernel**: for `t > 0`,
`∂_t K(t, y) = (1/2) · ∂²_y K(t, y)`, where `K(t, y) = (2πt)^{-1/2} e^{-y²/(2t)}` is the
`N(0, t)` density (`gaussianPDFReal y (t.toNNReal)` in Mathlib's variance convention). -/
theorem heatKernel_heat (t y : ℝ) (ht : 0 < t) :
    deriv (fun s ↦ heatKernel s y) t
      = (1 / 2) * deriv (deriv (fun y' : ℝ ↦ heatKernel t y')) y := by
  -- ∂_s K(s, y): the curve lemma with fixed centre 0
  have hT : HasDerivAt (fun s ↦ heatKernel s y)
      (heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)) t := by
    have hcomp := hasDerivAt_heatKernel_comp (v := fun s : ℝ ↦ s) (w := fun _ : ℝ ↦ (0:ℝ))
      (hasDerivAt_id t) (hasDerivAt_const t (0:ℝ)) ht y
    simpa using hcomp
  -- first y-derivative at every point
  have hx : ∀ x : ℝ, HasDerivAt (fun y' ↦ heatKernel t y') (-(x / t) * heatKernel t x) x :=
    fun x ↦ hasDerivAt_heatKernel_shift0 (v := t) ht
  -- second y-derivative in exact `deriv ∘ deriv` form
  have hxx : deriv (deriv (fun y' ↦ heatKernel t y')) y
      = heatKernel t y * (y ^ 2 - t) / t ^ 2 := by
    have hfun : (fun x : ℝ ↦ deriv (fun y' ↦ heatKernel t y') x)
        = (fun x : ℝ ↦ -(x / t) * heatKernel t x) := funext fun x ↦ (hx x).deriv
    have h2 : HasDerivAt (fun x : ℝ ↦ deriv (fun y' ↦ heatKernel t y') x)
        (heatKernel t y * (y ^ 2 - t) / t ^ 2) y := by
      rw [hfun]
      exact hasDerivAt_heatKernel_shift2_0 (v := t) ht
    exact h2.deriv
  rw [hT.deriv, hxx]
  ring

/-! ## The density of `x₀ + μ·t + σ·B_t` and its forward equation -/

/-- Density at time `t` of the process `x₀ + μ·t + σ·B_t`: the Gaussian with mean
`x₀ + μ·t` and variance `σ²·t`, written through the heat kernel
`pden μ σ x₀ t x = K(σ²·t, x − x₀ − μ·t)`. -/
noncomputable def pden (μ σ x₀ t x : ℝ) : ℝ := heatKernel (σ ^ 2 * t) (x - (x₀ + μ * t))

/-- Spatial derivative of `pden`: `∂_x p = -((x − x₀ − μ·t)/(σ²·t)) · p`
(meaningful for `t > 0`, `σ ≠ 0`; all statements gate on `0 < t`, `0 < σ`). -/
noncomputable def pdenx (μ σ x₀ t x : ℝ) : ℝ :=
  -(x - (x₀ + μ * t)) / (σ ^ 2 * t) * pden μ σ x₀ t x

/-- Second spatial derivative of `pden`:
`∂²_x p = p · ((x − x₀ − μ·t)² − σ²·t)/(σ²·t)²`. -/
noncomputable def pdenxx (μ σ x₀ t x : ℝ) : ℝ :=
  pden μ σ x₀ t x * ((x - (x₀ + μ * t)) ^ 2 - σ ^ 2 * t) / (σ ^ 2 * t) ^ 2

/-- Time derivative of `pden`: `∂_t p = -μ · ∂_x p + (σ²/2) · ∂²_x p` at `t > 0`.
Chain rule through the public curve lemma `hasDerivAt_heatKernel_comp` with
`v s = σ²·s` (speed `σ²`) and `w s = x₀ + μ·s` (speed `μ`). -/
lemma hasDerivAt_pden_t {μ σ x₀ t x : ℝ} (ht : 0 < t) (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ pden μ σ x₀ s x)
      (-μ * pdenx μ σ x₀ t x + (σ ^ 2 / 2) * pdenxx μ σ x₀ t x) t := by
  have hv : HasDerivAt (fun s : ℝ ↦ σ ^ 2 * s) (σ ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (σ ^ 2)
  have hw : HasDerivAt (fun s : ℝ ↦ x₀ + μ * s) μ t := by
    simpa using ((hasDerivAt_id t).const_mul μ).const_add x₀
  have hcomp := hasDerivAt_heatKernel_comp (v := fun s ↦ σ ^ 2 * s)
    (w := fun s ↦ x₀ + μ * s) hv hw (by positivity) x
  have hval : σ ^ 2 * (pden μ σ x₀ t x
          * ((x - (x₀ + μ * t)) ^ 2 - σ ^ 2 * t) / (2 * (σ ^ 2 * t) ^ 2))
      + μ * ((x - (x₀ + μ * t)) / (σ ^ 2 * t) * pden μ σ x₀ t x)
      = -μ * pdenx μ σ x₀ t x + (σ ^ 2 / 2) * pdenxx μ σ x₀ t x := by
    simp only [pdenx, pdenxx, pden]; ring
  rw [← hval]
  exact hcomp

/-- Spatial derivative of `pden` as a `HasDerivAt`. -/
lemma hasDerivAt_pden_x {μ σ x₀ t : ℝ} (x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    HasDerivAt (fun x' ↦ pden μ σ x₀ t x') (pdenx μ σ x₀ t x) x := by
  have hv : 0 < σ ^ 2 * t := by positivity
  exact hasDerivAt_heatKernel_shift (v := σ ^ 2 * t) (m := x₀ + μ * t) (y := x) hv

/-- Second spatial derivative of `pden` as a `HasDerivAt`: the derivative of
`x' ↦ ∂_x p(t, x')` is `x' ↦ ∂²_x p(t, x')` — product rule on
`-((x' − m)/v) · K(v, x' − m)`. -/
lemma hasDerivAt_pdenx_x {μ σ x₀ t : ℝ} (x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    HasDerivAt (fun x' ↦ pdenx μ σ x₀ t x') (pdenxx μ σ x₀ t x) x := by
  have hv : 0 < σ ^ 2 * t := by positivity
  have hf : HasDerivAt (fun x' : ℝ ↦ x' - (x₀ + μ * t)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (x₀ + μ * t)
  have hK := hasDerivAt_heatKernel_shift (v := σ ^ 2 * t) (m := x₀ + μ * t) (y := x) hv
  have hcm := (hf.mul hK).const_mul (-(1 / (σ ^ 2 * t)))
  have hfeq : (fun x' ↦ pdenx μ σ x₀ t x')
      = (fun x' : ℝ ↦ -(1 / (σ ^ 2 * t))
          * ((x' - (x₀ + μ * t)) * heatKernel (σ ^ 2 * t) (x' - (x₀ + μ * t)))) := by
    funext x'
    simp only [pdenx, pden]
    ring
  have hval : -(1 / (σ ^ 2 * t)) * (1 * heatKernel (σ ^ 2 * t) (x - (x₀ + μ * t))
        + (x - (x₀ + μ * t)) * (-(x - (x₀ + μ * t)) / (σ ^ 2 * t)
            * heatKernel (σ ^ 2 * t) (x - (x₀ + μ * t))))
      = pdenxx μ σ x₀ t x := by
    simp only [pdenxx, pden]
    field_simp
    ring
  rw [hfeq, ← hval]
  exact hcm

/-- **Deliverable 3 — the constant-drift forward equation** (proved directly):
for the density `p` of `x₀ + μ·t + σ·B_t`, `∂_t p = -μ ∂_x p + (σ²/2) ∂²_x p` on `t > 0`
— transport + heat, the Vasicek/Hull-White-shaped adjoint equation. -/
theorem forward_eq_constant_drift (μ σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    deriv (fun s ↦ pden μ σ x₀ s x) t
      = -μ * deriv (fun x' ↦ pden μ σ x₀ t x') x
        + (σ ^ 2 / 2) * deriv (deriv (fun x' ↦ pden μ σ x₀ t x')) x := by
  -- the second spatial derivative in exact `deriv ∘ deriv` form
  have hfun : (fun x' ↦ deriv (fun y ↦ pden μ σ x₀ t y) x')
      = (fun x' ↦ pdenx μ σ x₀ t x') :=
    funext fun x' ↦ (hasDerivAt_pden_x x' ht hσ).deriv
  have h2 : HasDerivAt (fun x' ↦ deriv (fun y ↦ pden μ σ x₀ t y) x')
      (pdenxx μ σ x₀ t x) x := by
    rw [hfun]
    exact hasDerivAt_pdenx_x x ht hσ
  have hdd : deriv (deriv (fun x' ↦ pden μ σ x₀ t x')) x = pdenxx μ σ x₀ t x :=
    h2.deriv
  rw [(hasDerivAt_pden_t ht hσ).deriv, (hasDerivAt_pden_x x ht hσ).deriv, hdd]

/-- **Deliverable 2 — the driftless forward equation** (`μ = 0` corollary of
`forward_eq_constant_drift`): `∂_t p = (σ²/2) · ∂²_x p` for the density of `x₀ + σ·B_t`. -/
theorem forward_eq_driftless (σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    deriv (fun s ↦ pden 0 σ x₀ s x) t
      = (σ ^ 2 / 2) * deriv (deriv (fun x' ↦ pden 0 σ x₀ t x')) x := by
  have h := forward_eq_constant_drift 0 σ x₀ t x ht hσ
  simpa using h

/-- Bridge to Mathlib's Gaussian pdf: the driftless density is exactly
`gaussianPDFReal x₀ (σ²·t)` — Mathlib's `gaussianPDFReal` second argument is the
**variance**, so `N(x₀, σ²·t)` reads `gaussianPDFReal x₀ (σ^2 * t).toNNReal`. -/
lemma pden_zero_drift_eq_gaussianPDFReal (σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    pden 0 σ x₀ t x = gaussianPDFReal x₀ (σ ^ 2 * t).toNNReal x := by
  rw [pden, gaussianPDFReal_def]
  have hcoe : ((σ ^ 2 * t).toNNReal : ℝ) = σ ^ 2 * t := Real.coe_toNNReal _ (by positivity)
  simp only [hcoe, heatKernel, zero_mul, add_zero]

/-! ## Deliverable 4 — the migration lemma: convolved densities

`u(t, x) = ∫_{[a,b]} g(y) · p(t, x − y) dy` with `g` continuous and bounded: the
forward equation migrates through the integral by dominated convergence, with an
*explicit constant* dominating function. -/

/-- The convolved density: `u(t, x) = ∫ y in [a, b], g(y) · p(t, x − y)`. -/
noncomputable def convDen (μ σ x₀ : ℝ) (g : ℝ → ℝ) (a b t x : ℝ) : ℝ :=
  ∫ y in Set.Icc a b, g y * pden μ σ x₀ t (x - y) ∂volume

/-! ### Continuity of the integrand families -/

private lemma continuous_pden_y (μ σ x₀ s x : ℝ) :
    Continuous (fun y ↦ pden μ σ x₀ s (x - y)) :=
  (continuous_heatKernel (σ ^ 2 * s)).comp (by fun_prop)

private lemma continuous_pdenx_y (μ σ x₀ s x : ℝ) :
    Continuous (fun y ↦ pdenx μ σ x₀ s (x - y)) := by
  simp only [pdenx, pden, heatKernel]
  fun_prop

private lemma continuous_pdenxx_y (μ σ x₀ s x : ℝ) :
    Continuous (fun y ↦ pdenxx μ σ x₀ s (x - y)) := by
  simp only [pdenxx, pden, heatKernel]
  fun_prop

/-! ### The explicit domination constant

On the compact parameter rectangle `s ∈ [t/2, 3t/2]`, `z ∈ [x−1−b, x+1−a]`, all three of
`|p|, |p_x|, |p_xx|` are bounded by the single explicit constant
`C₀ · (1 + W/v₀ + (W² + 2σ²t) · (2/(σ²t))²)` where
`C₀ = (2π·σ²t/2)^{-1/2}`, `v₀ = σ²t/2`, `W = |x| + 1 + |a| + |b| + |x₀| + |μ|·(3t/2)`:
Gaussian decay (`exp ≤ 1`, `1/√v` monotone in `v ≥ v₀`) times polynomial factors. -/

private lemma neg_le_abs_self' (r : ℝ) : -r ≤ |r| := by
  rcases lt_or_ge r 0 with h | h
  · rw [abs_of_neg h]
  · rw [abs_of_nonneg h]; linarith

set_option maxHeartbeats 1000000 in
private lemma exists_pden_bound (μ σ x₀ t a b x : ℝ) (ht : 0 < t) (hσ : 0 < σ) (_hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃s z : ℝ⦄, t / 2 ≤ s → s ≤ 3 * t / 2 →
      x - 1 - b ≤ z → z ≤ x + 1 - a →
      |pden μ σ x₀ s z| ≤ C ∧ |pdenx μ σ x₀ s z| ≤ C ∧ |pdenxx μ σ x₀ s z| ≤ C := by
  set v0 : ℝ := σ ^ 2 * t / 2 with hv0def
  have hv0 : 0 < v0 := by rw [hv0def]; positivity
  set W : ℝ := |x| + 1 + |a| + |b| + |x₀| + |μ| * (3 * t / 2) with hWdef
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hC0p : 0 < (Real.sqrt (2 * Real.pi * v0))⁻¹ :=
    inv_pos.2 (Real.sqrt_pos.mpr (by positivity))
  set C0p : ℝ := (Real.sqrt (2 * Real.pi * v0))⁻¹ with hC0def
  have hWv0 : 0 ≤ W / v0 := div_nonneg hW0 hv0.le
  have hBIG : 0 ≤ (W ^ 2 + 2 * σ ^ 2 * t) * (2 / (σ ^ 2 * t)) ^ 2 :=
    mul_nonneg (add_nonneg (sq_nonneg W) (by positivity)) (sq_nonneg _)
  set S : ℝ := 1 + W / v0 + (W ^ 2 + 2 * σ ^ 2 * t) * (2 / (σ ^ 2 * t)) ^ 2 with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  refine ⟨C0p * S, mul_nonneg hC0p.le (by linarith), ?_⟩
  intro s z hs1 hs2 hz1 hz2
  have hs0 : 0 < s := by linarith
  have hvge : v0 ≤ σ ^ 2 * s := by
    rw [hv0def]
    nlinarith [hs1, sq_nonneg σ]
  have hvle : σ ^ 2 * s ≤ 2 * σ ^ 2 * t := by
    calc σ ^ 2 * s ≤ σ ^ 2 * (2 * t) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg σ)
      _ = 2 * σ ^ 2 * t := by ring
  have hzabs : |z| ≤ |x| + 1 + |a| + |b| := by
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self x, le_abs_self a, le_abs_self b,
        neg_le_abs_self' x, neg_le_abs_self' a, neg_le_abs_self' b]
  have hms : |μ| * |s| ≤ |μ| * (3 * t / 2) :=
    mul_le_mul_of_nonneg_left (show |s| ≤ 3 * t / 2 by rw [abs_of_pos hs0]; linarith)
      (abs_nonneg μ)
  have hwabs : |z - (x₀ + μ * s)| ≤ W := by
    have h1 : |z - (x₀ + μ * s)| ≤ |z| + |x₀| + |μ| * |s| := by
      have e1 : |z - (x₀ + μ * s)| ≤ |z| + |x₀ + μ * s| := abs_sub _ _
      have e2 : |x₀ + μ * s| ≤ |x₀| + |μ| * |s| := by
        calc |x₀ + μ * s| ≤ |x₀| + |μ * s| := abs_add_le _ _
          _ = |x₀| + |μ| * |s| := by rw [abs_mul]
      linarith [e1, e2]
    linarith [h1, hzabs, hms]
  have hpnn : 0 ≤ pden μ σ x₀ s z := heatKernel_nonneg (by positivity) _
  have hp : |pden μ σ x₀ s z| ≤ C0p := by
    rw [abs_of_nonneg hpnn, pden, heatKernel]
    have hexp1 : Real.exp (-(z - (x₀ + μ * s)) ^ 2 / (2 * (σ ^ 2 * s))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      exact div_nonneg (sq_nonneg _) (by positivity)
    have hsqrt : (Real.sqrt (2 * Real.pi * v0) : ℝ) ≤ Real.sqrt (2 * Real.pi * (σ ^ 2 * s)) :=
      Real.sqrt_le_sqrt (by nlinarith [hvge, Real.pi_pos])
    calc (Real.sqrt (2 * Real.pi * (σ ^ 2 * s)))⁻¹
          * Real.exp (-(z - (x₀ + μ * s)) ^ 2 / (2 * (σ ^ 2 * s)))
        ≤ (Real.sqrt (2 * Real.pi * (σ ^ 2 * s)))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = (Real.sqrt (2 * Real.pi * (σ ^ 2 * s)))⁻¹ := by rw [mul_one]
      _ ≤ C0p := by
          rw [hC0def]
          exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) hsqrt
  have hple : pden μ σ x₀ s z ≤ C0p := by
    rw [← abs_of_nonneg hpnn]; exact hp
  have hpx : |pdenx μ σ x₀ s z| ≤ (W / v0) * C0p := by
    have h1 : |pdenx μ σ x₀ s z|
        = |z - (x₀ + μ * s)| / (σ ^ 2 * s) * pden μ σ x₀ s z := by
      rw [pdenx, abs_mul, abs_div, abs_neg,
        abs_of_pos (show (0:ℝ) < σ ^ 2 * s by positivity), abs_of_nonneg hpnn]
    rw [h1]
    calc |z - (x₀ + μ * s)| / (σ ^ 2 * s) * pden μ σ x₀ s z
        ≤ (W / v0) * pden μ σ x₀ s z := by
          refine mul_le_mul_of_nonneg_right ?_ hpnn
          rw [div_le_div_iff₀ (by positivity) hv0]
          nlinarith [hwabs, hvge, hW0, abs_nonneg (z - (x₀ + μ * s))]
      _ ≤ (W / v0) * C0p := mul_le_mul_of_nonneg_left hple hWv0
  have hpxx : |pdenxx μ σ x₀ s z|
      ≤ C0p * ((W ^ 2 + 2 * σ ^ 2 * t) * (2 / (σ ^ 2 * t)) ^ 2) := by
    have hw2 : (z - (x₀ + μ * s)) ^ 2 ≤ W ^ 2 := by
      have hwle := abs_le.mp hwabs
      nlinarith [hwle.1, hwle.2]
    have hab : |(z - (x₀ + μ * s)) ^ 2 - σ ^ 2 * s| ≤ W ^ 2 + 2 * σ ^ 2 * t := by
      rw [abs_le]
      constructor <;> linarith [hvle, hw2, hvge, sq_nonneg (z - (x₀ + μ * s)), sq_nonneg W]
    have hvge' : σ ^ 2 * t / 2 ≤ σ ^ 2 * s := by rw [← hv0def]; exact hvge
    have h2inv : (2 / (σ ^ 2 * t)) ^ 2 = ((σ ^ 2 * t / 2) ^ 2)⁻¹ := by
      field_simp
    have hpos2 : (0:ℝ) < (σ ^ 2 * t / 2) ^ 2 := by positivity
    have hle2 : (σ ^ 2 * t / 2) ^ 2 ≤ (σ ^ 2 * s) ^ 2 := by nlinarith [hvge']
    have hinv : ((σ ^ 2 * s) ^ 2)⁻¹ ≤ ((σ ^ 2 * t / 2) ^ 2)⁻¹ := inv_anti₀ hpos2 hle2
    have h1 : |pdenxx μ σ x₀ s z|
        = pden μ σ x₀ s z
          * (|(z - (x₀ + μ * s)) ^ 2 - σ ^ 2 * s| / (σ ^ 2 * s) ^ 2) := by
      rw [pdenxx, abs_div, abs_mul,
        abs_of_pos (show (0:ℝ) < (σ ^ 2 * s) ^ 2 by positivity), abs_of_nonneg hpnn,
        mul_div_assoc]
    rw [h1]
    calc pden μ σ x₀ s z * (|(z - (x₀ + μ * s)) ^ 2 - σ ^ 2 * s| / (σ ^ 2 * s) ^ 2)
        ≤ C0p * (|(z - (x₀ + μ * s)) ^ 2 - σ ^ 2 * s| / (σ ^ 2 * s) ^ 2) :=
          mul_le_mul_of_nonneg_right hple (by positivity)
      _ ≤ C0p * ((W ^ 2 + 2 * σ ^ 2 * t) * (2 / (σ ^ 2 * t)) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (by
              rw [div_eq_mul_inv, h2inv]
              calc |(z - (x₀ + μ * s)) ^ 2 - σ ^ 2 * s| * ((σ ^ 2 * s) ^ 2)⁻¹
                  ≤ (W ^ 2 + 2 * σ ^ 2 * t) * ((σ ^ 2 * s) ^ 2)⁻¹ :=
                    mul_le_mul_of_nonneg_right hab (by positivity)
                _ ≤ (W ^ 2 + 2 * σ ^ 2 * t) * ((σ ^ 2 * t / 2) ^ 2)⁻¹ :=
                    mul_le_mul_of_nonneg_left hinv (by positivity))
            hC0p.le
  have hleWS : W / v0 ≤ S := by linarith
  have hlePS : (W ^ 2 + 2 * σ ^ 2 * t) * (2 / (σ ^ 2 * t)) ^ 2 ≤ S := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h : C0p * 1 ≤ C0p * S := mul_le_mul_of_nonneg_left hS1 hC0p.le
    rw [mul_one] at h
    exact hp.trans h
  · calc |pdenx μ σ x₀ s z| ≤ (W / v0) * C0p := hpx
      _ ≤ S * C0p := mul_le_mul_of_nonneg_right hleWS hC0p.le
      _ = C0p * S := mul_comm _ _
  · calc |pdenxx μ σ x₀ s z|
        ≤ C0p * ((W ^ 2 + 2 * σ ^ 2 * t) * (2 / (σ ^ 2 * t)) ^ 2) := hpxx
      _ ≤ C0p * S := mul_le_mul_of_nonneg_left hlePS hC0p.le

/-! ### Differentiating under the integral -/

/-- Shared integrability: `g` bounded continuous, `F` continuous in `y` after the shift
and bounded on `[x−b, x−a]` ⟹ `y ↦ g y · F (x − y)` is integrable on `[a, b]`. -/
private lemma integrable_base (_μ _σ _x₀ : ℝ) {g : ℝ → ℝ} (a b _t x : ℝ) (_hab : a ≤ b)
    (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) {Cf : ℝ} (_hCf : 0 ≤ Cf)
    {F : ℝ → ℝ} (hFc : Continuous (fun y ↦ F (x - y)))
    (hFb : ∀ z, x - b ≤ z → z ≤ x - a → |F z| ≤ Cf) :
    Integrable (fun y ↦ g y * F (x - y)) (volume.restrict (Set.Icc a b)) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  refine (integrable_const (Cg * Cf) (μ := volume.restrict (Set.Icc a b))).mono'
    ((hg.mul hFc).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy
  rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
  show |g y * F (x - y)| ≤ Cg * Cf
  rw [abs_mul]
  calc |g y| * |F (x - y)| ≤ Cg * |F (x - y)| :=
      mul_le_mul_of_nonneg_right (hgC y) (abs_nonneg _)
    _ ≤ Cg * Cf := mul_le_mul_of_nonneg_left
        (hFb (x - y) (by linarith) (by linarith)) hCg0

/-- **Differentiating the convolution in `t`** (the forward-equation seed): for `g`
continuous and bounded, `s ↦ ∫_{[a,b]} g(y)·p(s, x−y) dy` is differentiable at `t > 0`
with `d/dt = ∫_{[a,b]} g(y)·(-μ ∂_x p + (σ²/2) ∂²_x p)(t, x−y) dy`. Domination: the
explicit constant of `exists_pden_bound` on `s ∈ (t/2, 3t/2)`, `z ∈ [x−1−b, x+1−a]`. -/
private lemma hasDerivAt_convDen_t (μ σ x₀ : ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (ht : 0 < t)
    (hσ : 0 < σ) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    HasDerivAt (fun s ↦ convDen μ σ x₀ g a b s x)
      (∫ y in Set.Icc a b, g y * (-μ * pdenx μ σ x₀ t (x - y)
          + (σ ^ 2 / 2) * pdenxx μ σ x₀ t (x - y)) ∂volume) t := by
  obtain ⟨C, hC0, hC⟩ := exists_pden_bound μ σ x₀ t a b x ht hσ hab
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  have hzb : ∀ y ∈ Set.Icc a b, x - 1 - b ≤ x - y ∧ x - y ≤ x + 1 - a := by
    intro y hy
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    exact ⟨by linarith, by linarith⟩
  have hsball : ∀ s ∈ Metric.ball t (t / 2), t / 2 ≤ s ∧ s ≤ 3 * t / 2 := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith, by linarith⟩
  have hint := integrable_base μ σ x₀ a b t x hab hg hgC hC0
    (F := pden μ σ x₀ t) (continuous_pden_y μ σ x₀ t x)
    (fun z hz1 hz2 =>
      (hC (show t / 2 ≤ t by linarith) (show t ≤ 3 * t / 2 by linarith)
        (show x - 1 - b ≤ z by linarith) (show z ≤ x + 1 - a by linarith)).1)
  have hF'c : Continuous (fun y ↦ g y * (-μ * pdenx μ σ x₀ t (x - y)
      + (σ ^ 2 / 2) * pdenxx μ σ x₀ t (x - y))) :=
    hg.mul (((continuous_pdenx_y μ σ x₀ t x).const_mul (-(μ:ℝ))).add
      ((continuous_pdenxx_y μ σ x₀ t x).const_mul (σ ^ 2 / 2)))
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ s ∈ Metric.ball t (t / 2),
      ‖g y * (-μ * pdenx μ σ x₀ s (x - y)
          + (σ ^ 2 / 2) * pdenxx μ σ x₀ s (x - y))‖
        ≤ Cg * ((1 + |μ| + σ ^ 2) * C) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy s hs
    obtain ⟨hs1, hs2⟩ := hsball s hs
    obtain ⟨_, hb2, hb3⟩ := hC hs1 hs2 (hzb y hy).1 (hzb y hy).2
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |-μ * pdenx μ σ x₀ s (x - y) + (σ ^ 2 / 2) * pdenxx μ σ x₀ s (x - y)|
        ≤ |g y| * (|-μ * pdenx μ σ x₀ s (x - y)|
            + |(σ ^ 2 / 2) * pdenxx μ σ x₀ s (x - y)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ |g y| * (|μ| * |pdenx μ σ x₀ s (x - y)|
            + (σ ^ 2 / 2) * |pdenxx μ σ x₀ s (x - y)|) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ σ ^ 2 / 2 by positivity),
            abs_neg]
      _ ≤ Cg * (|μ| * |pdenx μ σ x₀ s (x - y)|
            + (σ ^ 2 / 2) * |pdenxx μ σ x₀ s (x - y)|) :=
          mul_le_mul_of_nonneg_right (hgC y) (by positivity)
      _ ≤ Cg * ((1 + |μ| + σ ^ 2) * C) := by
          refine mul_le_mul_of_nonneg_left ?_ hCg0
          have hμ : |μ| * |pdenx μ σ x₀ s (x - y)| ≤ |μ| * C :=
            mul_le_mul_of_nonneg_left hb2 (abs_nonneg μ)
          have hsig : (σ ^ 2 / 2) * |pdenxx μ σ x₀ s (x - y)| ≤ (σ ^ 2 / 2) * C :=
            mul_le_mul_of_nonneg_left hb3 (by positivity)
          have hexp : (|μ| + σ ^ 2 / 2) * C = |μ| * C + (σ ^ 2 / 2) * C := by ring
          have hstep : |μ| * |pdenx μ σ x₀ s (x - y)|
                + (σ ^ 2 / 2) * |pdenxx μ σ x₀ s (x - y)|
              ≤ |μ| * C + (σ ^ 2 / 2) * C := add_le_add hμ hsig
          have hstep2 : (|μ| + σ ^ 2 / 2) * C ≤ (1 + |μ| + σ ^ 2) * C :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg μ, sq_nonneg σ]) hC0
          rw [hexp] at hstep2
          exact hstep.trans hstep2
  have hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun r ↦ g y * pden μ σ x₀ r (x - y))
        (g y * (-μ * pdenx μ σ x₀ s (x - y)
            + (σ ^ 2 / 2) * pdenxx μ σ x₀ s (x - y))) s :=
    Filter.Eventually.of_forall fun y s hs => by
      have hs0 : 0 < s := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
        linarith
      exact (hasDerivAt_pden_t (t := s) (x := x - y) hs0 hσ).const_mul (g y)
  obtain ⟨_, hdct⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball t (t / 2))
      (x₀ := t) (μ := volume.restrict (Set.Icc a b))
      (F := fun s y ↦ g y * pden μ σ x₀ s (x - y))
      (F' := fun s y ↦ g y * (-μ * pdenx μ σ x₀ s (x - y)
          + (σ ^ 2 / 2) * pdenxx μ σ x₀ s (x - y)))
      (bound := fun _ ↦ Cg * ((1 + |μ| + σ ^ 2) * C))
      (Metric.ball_mem_nhds t (by positivity))
      (Filter.Eventually.of_forall fun s =>
        (hg.mul (continuous_pden_y μ σ x₀ s x)).aestronglyMeasurable
          (μ := volume.restrict (Set.Icc a b)))
      hint (hF'c.aestronglyMeasurable (μ := volume.restrict (Set.Icc a b))) hbound
      (integrable_const (Cg * ((1 + |μ| + σ ^ 2) * C))) hdiff
  exact hdct

/-- **Differentiating the convolution in `x`**: for `g` continuous and bounded,
`x' ↦ ∫_{[a,b]} g(y)·p(t, x'−y) dy` is differentiable at every `x` with
`d/dx = ∫_{[a,b]} g(y)·∂_x p(t, x−y) dy`. -/
private lemma hasDerivAt_convDen_x (μ σ x₀ : ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (ht : 0 < t)
    (hσ : 0 < σ) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    Integrable (fun y ↦ g y * pdenx μ σ x₀ t (x - y)) (volume.restrict (Set.Icc a b)) ∧
    HasDerivAt (fun x' ↦ convDen μ σ x₀ g a b t x')
      (∫ y in Set.Icc a b, g y * pdenx μ σ x₀ t (x - y) ∂volume) x := by
  obtain ⟨C, hC0, hC⟩ := exists_pden_bound μ σ x₀ t a b x ht hσ hab
  have hCge : C ≤ (1 + |μ| + σ ^ 2) * C := by
    have h1 : (1:ℝ) ≤ 1 + |μ| + σ ^ 2 := by linarith [abs_nonneg μ, sq_nonneg σ]
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * (1 + |μ| + σ ^ 2) := mul_le_mul_of_nonneg_left h1 hC0
      _ = (1 + |μ| + σ ^ 2) * C := mul_comm _ _
  have hint := integrable_base μ σ x₀ a b t x hab hg hgC hC0
    (F := pden μ σ x₀ t) (continuous_pden_y μ σ x₀ t x)
    (fun z hz1 hz2 =>
      (hC (show t / 2 ≤ t by linarith) (show t ≤ 3 * t / 2 by linarith)
        (show x - 1 - b ≤ z by linarith) (show z ≤ x + 1 - a by linarith)).1)
  have hzb : ∀ y ∈ Set.Icc a b, ∀ x' ∈ Metric.ball x 1,
      x - 1 - b ≤ x' - y ∧ x' - y ≤ x + 1 - a := by
    intro y hy x' hx'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    exact ⟨by linarith, by linarith⟩
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      ‖g y * pdenx μ σ x₀ t (x' - y)‖ ≤ Cg * ((1 + |μ| + σ ^ 2) * C) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy x' hx'
    obtain ⟨_, hb2, _⟩ := hC (show t / 2 ≤ t by linarith) (show t ≤ 3 * t / 2 by linarith)
      (hzb y hy x' hx').1 (hzb y hy x' hx').2
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |pdenx μ σ x₀ t (x' - y)| ≤ Cg * |pdenx μ σ x₀ t (x' - y)| :=
        mul_le_mul_of_nonneg_right (hgC y) (abs_nonneg _)
      _ ≤ Cg * ((1 + |μ| + σ ^ 2) * C) :=
        mul_le_mul_of_nonneg_left (hb2.trans hCge) (le_trans (abs_nonneg _) (hgC 0))
  have hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      HasDerivAt (fun r ↦ g y * pden μ σ x₀ t (r - y))
        (g y * pdenx μ σ x₀ t (x' - y)) x' :=
    Filter.Eventually.of_forall fun y x' hx' => by
      have hc : HasDerivAt (fun r : ℝ ↦ r - y) 1 x' := (hasDerivAt_id x').sub_const y
      simpa using (HasDerivAt.scomp_of_eq x'
        (hasDerivAt_pden_x (μ := μ) (σ := σ) (x₀ := x₀) (x' - y) ht hσ) hc rfl).const_mul (g y)
  obtain ⟨hintx, hdct⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball x 1)
      (x₀ := x) (μ := volume.restrict (Set.Icc a b))
      (F := fun x' y ↦ g y * pden μ σ x₀ t (x' - y))
      (F' := fun x' y ↦ g y * pdenx μ σ x₀ t (x' - y))
      (bound := fun _ ↦ Cg * ((1 + |μ| + σ ^ 2) * C))
      (Metric.ball_mem_nhds x (by norm_num))
      (Filter.Eventually.of_forall fun x' =>
        (hg.mul (continuous_pden_y μ σ x₀ t x')).aestronglyMeasurable
          (μ := volume.restrict (Set.Icc a b)))
      hint
      ((hg.mul (continuous_pdenx_y μ σ x₀ t x)).aestronglyMeasurable
        (μ := volume.restrict (Set.Icc a b)))
      hbound (integrable_const (Cg * ((1 + |μ| + σ ^ 2) * C))) hdiff
  exact ⟨hintx, hdct⟩

/-- **Differentiating the convolution twice in `x`**: for `g` continuous and bounded,
the derivative function `x' ↦ ∂_x u(t, x')` is itself differentiable at every `x` with
`d/dx = ∫_{[a,b]} g(y)·∂²_x p(t, x−y) dy`. -/
private lemma hasDerivAt_convDen_xx_core (μ σ x₀ : ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (ht : 0 < t)
    (hσ : 0 < σ) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    Integrable (fun y ↦ g y * pdenxx μ σ x₀ t (x - y)) (volume.restrict (Set.Icc a b)) ∧
    HasDerivAt (fun x' ↦ ∫ y in Set.Icc a b, g y * pdenx μ σ x₀ t (x' - y) ∂volume)
      (∫ y in Set.Icc a b, g y * pdenxx μ σ x₀ t (x - y) ∂volume) x := by
  obtain ⟨C, hC0, hC⟩ := exists_pden_bound μ σ x₀ t a b x ht hσ hab
  have hCge : C ≤ (1 + |μ| + σ ^ 2) * C := by
    have h1 : (1:ℝ) ≤ 1 + |μ| + σ ^ 2 := by linarith [abs_nonneg μ, sq_nonneg σ]
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * (1 + |μ| + σ ^ 2) := mul_le_mul_of_nonneg_left h1 hC0
      _ = (1 + |μ| + σ ^ 2) * C := mul_comm _ _
  have hint := integrable_base μ σ x₀ a b t x hab hg hgC hC0
    (F := pdenx μ σ x₀ t) (continuous_pdenx_y μ σ x₀ t x)
    (fun z hz1 hz2 =>
      (hC (show t / 2 ≤ t by linarith) (show t ≤ 3 * t / 2 by linarith)
        (show x - 1 - b ≤ z by linarith) (show z ≤ x + 1 - a by linarith)).2.1)
  have hzb : ∀ y ∈ Set.Icc a b, ∀ x' ∈ Metric.ball x 1,
      x - 1 - b ≤ x' - y ∧ x' - y ≤ x + 1 - a := by
    intro y hy x' hx'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    exact ⟨by linarith, by linarith⟩
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      ‖g y * pdenxx μ σ x₀ t (x' - y)‖ ≤ Cg * ((1 + |μ| + σ ^ 2) * C) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy x' hx'
    obtain ⟨_, _, hb3⟩ := hC (show t / 2 ≤ t by linarith) (show t ≤ 3 * t / 2 by linarith)
      (hzb y hy x' hx').1 (hzb y hy x' hx').2
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |pdenxx μ σ x₀ t (x' - y)| ≤ Cg * |pdenxx μ σ x₀ t (x' - y)| :=
        mul_le_mul_of_nonneg_right (hgC y) (abs_nonneg _)
      _ ≤ Cg * ((1 + |μ| + σ ^ 2) * C) :=
        mul_le_mul_of_nonneg_left (hb3.trans hCge) (le_trans (abs_nonneg _) (hgC 0))
  have hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      HasDerivAt (fun r ↦ g y * pdenx μ σ x₀ t (r - y))
        (g y * pdenxx μ σ x₀ t (x' - y)) x' :=
    Filter.Eventually.of_forall fun y x' hx' => by
      have hc : HasDerivAt (fun r : ℝ ↦ r - y) 1 x' := (hasDerivAt_id x').sub_const y
      simpa using (HasDerivAt.scomp_of_eq x'
        (hasDerivAt_pdenx_x (μ := μ) (σ := σ) (x₀ := x₀) (x' - y) ht hσ) hc rfl).const_mul (g y)
  obtain ⟨hintx, hdct⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball x 1)
      (x₀ := x) (μ := volume.restrict (Set.Icc a b))
      (F := fun x' y ↦ g y * pdenx μ σ x₀ t (x' - y))
      (F' := fun x' y ↦ g y * pdenxx μ σ x₀ t (x' - y))
      (bound := fun _ ↦ Cg * ((1 + |μ| + σ ^ 2) * C))
      (Metric.ball_mem_nhds x (by norm_num))
      (Filter.Eventually.of_forall fun x' =>
        (hg.mul (continuous_pdenx_y μ σ x₀ t x')).aestronglyMeasurable
          (μ := volume.restrict (Set.Icc a b)))
      hint
      ((hg.mul (continuous_pdenxx_y μ σ x₀ t x)).aestronglyMeasurable
        (μ := volume.restrict (Set.Icc a b)))
      hbound (integrable_const (Cg * ((1 + |μ| + σ ^ 2) * C))) hdiff
  exact ⟨hintx, hdct⟩

/-- The second convolution derivative in exact `deriv ∘ deriv` form. -/
private lemma hasDerivAt_convDen_xx (μ σ x₀ : ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (ht : 0 < t)
    (hσ : 0 < σ) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    HasDerivAt (fun x' ↦ deriv (fun z ↦ convDen μ σ x₀ g a b t z) x')
      (∫ y in Set.Icc a b, g y * pdenxx μ σ x₀ t (x - y) ∂volume) x := by
  have heq : (fun x' ↦ deriv (fun z ↦ convDen μ σ x₀ g a b t z) x')
      = (fun x' ↦ ∫ y in Set.Icc a b, g y * pdenx μ σ x₀ t (x' - y) ∂volume) := by
    funext x'
    exact (hasDerivAt_convDen_x μ σ x₀ a b t x' ht hσ hab hg hgC).2.deriv
  rw [heq]
  exact (hasDerivAt_convDen_xx_core μ σ x₀ a b t x ht hσ hab hg hgC).2

/-- **Deliverable 4 — the migration lemma**: the constant-drift forward equation
migrates through convolution against a compactly-supported continuous bounded `g`:
`∂_t u = -μ ∂_x u + (σ²/2) ∂²_x u` for `u(t, x) = ∫_{[a,b]} g(y)·p(t, x−y) dy`, `t > 0`.
Pointwise from `hasDerivAt_convDen_t/_x/_xx_core` + dominated convergence with the
explicit constant domination of `exists_pden_bound`. This is the seed that scales to
the Gyöngy/Dupire forward equations (stage 2/3 of the lesson 0021 build). -/
theorem forward_eq_convolution (μ σ x₀ : ℝ) (g : ℝ → ℝ) (a b t x : ℝ) (ht : 0 < t)
    (hσ : 0 < σ) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    deriv (fun s ↦ convDen μ σ x₀ g a b s x) t
      = -μ * deriv (fun x' ↦ convDen μ σ x₀ g a b t x') x
        + (σ ^ 2 / 2) * deriv (deriv (fun x' ↦ convDen μ σ x₀ g a b t x')) x := by
  have hintx := (hasDerivAt_convDen_x μ σ x₀ a b t x ht hσ hab hg hgC).1
  have hX := (hasDerivAt_convDen_x μ σ x₀ a b t x ht hσ hab hg hgC).2
  have hintxx := (hasDerivAt_convDen_xx_core μ σ x₀ a b t x ht hσ hab hg hgC).1
  have hXX := (hasDerivAt_convDen_xx_core μ σ x₀ a b t x ht hσ hab hg hgC).2
  have hT := hasDerivAt_convDen_t μ σ x₀ a b t x ht hσ hab hg hgC
  -- the two spatial derivatives in exact `deriv` / `deriv ∘ deriv` form
  have hX' : deriv (fun x' ↦ convDen μ σ x₀ g a b t x') x
      = ∫ y in Set.Icc a b, g y * pdenx μ σ x₀ t (x - y) ∂volume := hX.deriv
  have hXX' : deriv (deriv (fun x' ↦ convDen μ σ x₀ g a b t x')) x
      = ∫ y in Set.Icc a b, g y * pdenxx μ σ x₀ t (x - y) ∂volume :=
    HasDerivAt.deriv (hasDerivAt_convDen_xx μ σ x₀ a b t x ht hσ hab hg hgC)
  rw [hT.deriv, hX', hXX']
  -- linearity of the integral closes the equation
  have hintx' : Integrable (fun y : ℝ ↦ -μ * (g y * pdenx μ σ x₀ t (x - y)))
      (volume.restrict (Set.Icc a b)) := hintx.const_mul (-μ)
  have hintxx' : Integrable (fun y : ℝ ↦ (σ ^ 2 / 2) * (g y * pdenxx μ σ x₀ t (x - y)))
      (volume.restrict (Set.Icc a b)) := hintxx.const_mul (σ ^ 2 / 2)
  have hpt : ∀ y : ℝ, g y * (-μ * pdenx μ σ x₀ t (x - y)
        + (σ ^ 2 / 2) * pdenxx μ σ x₀ t (x - y))
      = -μ * (g y * pdenx μ σ x₀ t (x - y))
        + (σ ^ 2 / 2) * (g y * pdenxx μ σ x₀ t (x - y)) := fun y => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hintx' hintxx',
    ← integral_const_mul, ← integral_const_mul]

/-! ## Stage 2 — the variable-coefficient forward equation

The density `p(t, x) = K(v t, x − m t)` of the diffusion `dX_t = μ(t) dt + σ(t) dW_t`
with *deterministic* coefficients (mean curve `m`, variance curve `v`, `m' = μ`,
`v' = σ²`, `v > 0`): `∂_t p = −μ ∂_x p + (σ²/2) ∂²_x p`. The chain rule through
`m'(t) = μ(t)` and `v'(t) = σ(t)²` is the whole proof — the continuous analogue of
stage 1's constant-drift case (where `m' = μ`, `v' = σ²` are constants). This is the
Gyöngy/Dupire half for `t`-dependent coefficients; the full Dupire form (coefficients
depending on `(t, x)`, via Gyöngy's conditional-expectation coefficients) is stage 3. -/

open Set

/-- Gaussian density with time-dependent mean and variance:
`pdenGen m v t x = K(v t, x − m t)` — the density at time `t` of the diffusion with
mean curve `m` and variance curve `v`. -/
noncomputable def pdenGen (m v : ℝ → ℝ) (t x : ℝ) : ℝ := heatKernel (v t) (x - m t)

/-- Spatial derivative of `pdenGen`: `∂_x p = -((x − m t)/(v t)) · p`
(meaningful for `v t > 0`; all statements gate on `0 < v t`). -/
noncomputable def pdenGenx (m v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  -(x - m t) / v t * pdenGen m v t x

/-- Second spatial derivative of `pdenGen`:
`∂²_x p = p · ((x − m t)² − v t)/(v t)²`. -/
noncomputable def pdenGenxx (m v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  pdenGen m v t x * ((x - m t) ^ 2 - v t) / (v t) ^ 2

/-! ### The three derivative identities -/

/-- Spatial derivative of `pdenGen` as a `HasDerivAt`. -/
lemma hasDerivAt_pdenGen_x {m v : ℝ → ℝ} {t : ℝ} (x : ℝ) (hvt : 0 < v t) :
    HasDerivAt (fun x' ↦ pdenGen m v t x') (pdenGenx m v t x) x :=
  hasDerivAt_heatKernel_shift (v := v t) (m := m t) (y := x) hvt

/-- Second spatial derivative of `pdenGen` as a `HasDerivAt`: the derivative of
`x' ↦ ∂_x p(t, x')` is `x' ↦ ∂²_x p(t, x')` — exactly the `shift2` lemma's shape. -/
lemma hasDerivAt_pdenGenx_x {m v : ℝ → ℝ} {t : ℝ} (x : ℝ) (hvt : 0 < v t) :
    HasDerivAt (fun x' ↦ pdenGenx m v t x') (pdenGenxx m v t x) x :=
  hasDerivAt_heatKernel_shift2 (v := v t) (m := m t) (y := x) hvt

/-- Time derivative of `pdenGen`: chain rule through the public curve lemma
`hasDerivAt_heatKernel_comp` with both curves moving (`v s`, `m s`), then the algebraic
heart: `-μ' · ∂_x p + (σsq/2) · ∂²_x p` equals the comp-shaped coefficient
`σsq · p·((x−m t)² − v t)/(2 (v t)²) + μ' · ((x − m t)/(v t)) · p` — verified symbolically
(sympy) and closed by `ring`. -/
lemma hasDerivAt_pdenGen_t {m v : ℝ → ℝ} {t x μ' σsq : ℝ}
    (hm : HasDerivAt m μ' t) (hv : HasDerivAt v σsq t) (hvt : 0 < v t) :
    HasDerivAt (fun s ↦ pdenGen m v s x)
      (-μ' * pdenGenx m v t x + (σsq / 2) * pdenGenxx m v t x) t := by
  have hcomp := hasDerivAt_heatKernel_comp (v := v) (w := m) hv hm hvt x
  have hval : σsq * (pdenGen m v t x * ((x - m t) ^ 2 - v t) / (2 * (v t) ^ 2))
      + μ' * ((x - m t) / v t * pdenGen m v t x)
      = -μ' * pdenGenx m v t x + (σsq / 2) * pdenGenxx m v t x := by
    simp only [pdenGenx, pdenGenxx, pdenGen]
    ring
  rw [← hval]
  exact hcomp

/-! ### Deliverable 1 — the variable-coefficient forward equation -/

/-- **The variable-coefficient forward equation**: for the density `p(t, x) = K(v t, x − m t)`
of `dX_t = μ(t) dt + σ(t) dW_t` (deterministic coefficients, `m' = μ`, `v' = σ²`,
`v t > 0`), `∂_t p = −μ(t) ∂_x p + (σ(t)²/2) ∂²_x p` at `t`. The proof composes the three
derivative identities and closes by `ring` — no Itô calculus. -/
theorem forward_eq_timeDependent (m v μ σ : ℝ → ℝ) (t x : ℝ)
    (hm : HasDerivAt m (μ t) t) (hv : HasDerivAt v (σ t ^ 2) t) (hvt : 0 < v t) :
    deriv (fun s ↦ pdenGen m v s x) t
      = -μ t * deriv (fun x' ↦ pdenGen m v t x') x
        + (σ t ^ 2 / 2) * deriv (deriv (fun x' ↦ pdenGen m v t x')) x := by
  have hfun : (fun x' ↦ deriv (fun y ↦ pdenGen m v t y) x')
      = (fun x' ↦ pdenGenx m v t x') := funext fun x' ↦ (hasDerivAt_pdenGen_x x' hvt).deriv
  have h2 : HasDerivAt (fun x' ↦ deriv (fun y ↦ pdenGen m v t y) x')
      (pdenGenxx m v t x) x := by
    rw [hfun]
    exact hasDerivAt_pdenGenx_x x hvt
  have hdd : deriv (deriv (fun x' ↦ pdenGen m v t x')) x = pdenGenxx m v t x := h2.deriv
  rw [(hasDerivAt_pdenGen_t hm hv hvt).deriv, (hasDerivAt_pdenGen_x x hvt).deriv, hdd]

/-- **Deliverable 3 — the connection to stage 1**: for constant `μ, σ` the mean/variance
curves `m s = x₀ + μ·s`, `v s = σ²·s` are exactly `pden μ σ x₀`'s parameters, so
`forward_eq_timeDependent` is *definitionally* `forward_eq_constant_drift` — the proof is
the stage-1 theorem itself, accepted up to unfolding of `pdenGen`/`pden` (definitional
match; no separate algebra needed). -/
theorem forward_eq_timeDependent_constant (μ σ x₀ t x : ℝ) (ht : 0 < t) (hσ : 0 < σ) :
    deriv (fun s ↦ pdenGen (fun s ↦ x₀ + μ * s) (fun s ↦ σ ^ 2 * s) s x) t
      = -μ * deriv (fun x' ↦ pdenGen (fun s ↦ x₀ + μ * s) (fun s ↦ σ ^ 2 * s) t x') x
        + (σ ^ 2 / 2) *
          deriv (deriv (fun x' ↦ pdenGen (fun s ↦ x₀ + μ * s) (fun s ↦ σ ^ 2 * s) t x')) x :=
  forward_eq_constant_drift μ σ x₀ t x ht hσ

/-! ### Deliverable 2 — the migration lemma for variable coefficients

`u(t, x) = ∫_{[a,b]} g(y) · p(t, x−y) dy` with the time-dependent density `pdenGen`:
the variable-coefficient forward equation migrates through the integral by dominated
convergence, with the domination generalized to the compact time-range
`s ∈ [t/2, 3t/2]`: Gaussian decay (`v s ≥ v_min > 0` from compactness + `hvs`) times
polynomial factors in `W = |x| + 1 + |a| + |b| + max|m|`. -/

/-- The convolved density with time-dependent coefficients:
`u(t, x) = ∫ y in [a, b], g(y) · p(t, x − y)`. -/
noncomputable def convDenGen (m v : ℝ → ℝ) (g : ℝ → ℝ) (a b t x : ℝ) : ℝ :=
  ∫ y in Set.Icc a b, g y * pdenGen m v t (x - y) ∂volume

/-! #### Continuity of the integrand families -/

private lemma continuous_pdenGen_z (m v : ℝ → ℝ) (s : ℝ) :
    Continuous (fun z ↦ pdenGen m v s z) :=
  (continuous_heatKernel (v s)).comp (by fun_prop)

private lemma continuous_pdenGenx_z (m v : ℝ → ℝ) (s : ℝ) :
    Continuous (fun z ↦ pdenGenx m v s z) := by
  simp only [pdenGenx, pdenGen, heatKernel]
  fun_prop

private lemma continuous_pdenGenxx_z (m v : ℝ → ℝ) (s : ℝ) :
    Continuous (fun z ↦ pdenGenxx m v s z) := by
  simp only [pdenGenxx, pdenGen, heatKernel]
  fun_prop

private lemma continuous_pdenGen_y (m v : ℝ → ℝ) (s x : ℝ) :
    Continuous (fun y ↦ pdenGen m v s (x - y)) :=
  (continuous_pdenGen_z m v s).comp (by fun_prop)

private lemma continuous_pdenGenx_y (m v : ℝ → ℝ) (s x : ℝ) :
    Continuous (fun y ↦ pdenGenx m v s (x - y)) :=
  (continuous_pdenGenx_z m v s).comp (by fun_prop)

private lemma continuous_pdenGenxx_y (m v : ℝ → ℝ) (s x : ℝ) :
    Continuous (fun y ↦ pdenGenxx m v s (x - y)) :=
  (continuous_pdenGenxx_z m v s).comp (by fun_prop)

/-! #### Two generic domination helpers -/

/-- A function continuous on a compact interval is bounded there (in absolute value). -/
private lemma exists_cont_bound {f : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hc : ContinuousOn f (Icc l u)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, l ≤ z → z ≤ u → |f z| ≤ C := by
  have hne : (Icc l u).Nonempty := ⟨l, Set.mem_Icc.mpr ⟨le_refl l, hlu⟩⟩
  obtain ⟨z0, hz0, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc.abs
  refine ⟨|f z0|, abs_nonneg _, fun z hz1 hz2 => ?_⟩
  exact isMaxOn_iff.mp hmax z (Set.mem_Icc.mpr ⟨hz1, hz2⟩)

-- The explicit domination constant for the variable-coefficient density, uniform on the
-- compact time range `s ∈ [t/2, 3t/2]` and the spatial range `z ∈ [x−1−b, x+1−a]`:
-- `C = C₀ · (1 + W/v_min + (W² + v_max)/v_min²)` with `C₀ = (2π·v_min)^{-1/2}`,
-- `v_min = min v`, `v_max = max v` on the time range, `W = |x| + 1 + |a| + |b| + max|m|`.
-- Gaussian decay (`exp ≤ 1`, `1/√v` monotone in `v ≥ v_min`) times polynomial factors.
set_option maxHeartbeats 1000000 in
private lemma exists_pdenGen_bound (m v : ℝ → ℝ) (a b t x : ℝ) (ht : 0 < t)
    (hmc : ContinuousOn m (Icc (t / 2) (3 * t / 2)))
    (hvc : ContinuousOn v (Icc (t / 2) (3 * t / 2)))
    (hvs : ∀ s ∈ Icc (t / 2) (3 * t / 2), 0 < v s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃s z : ℝ⦄, t / 2 ≤ s → s ≤ 3 * t / 2 →
      x - 1 - b ≤ z → z ≤ x + 1 - a →
      |pdenGen m v s z| ≤ C ∧ |pdenGenx m v s z| ≤ C ∧ |pdenGenxx m v s z| ≤ C := by
  have hIcc : (Icc (t / 2) (3 * t / 2)).Nonempty :=
    ⟨t / 2, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hlu : t / 2 ≤ 3 * t / 2 := by linarith
  obtain ⟨smin, hsmin, hmin⟩ := isCompact_Icc.exists_isMinOn hIcc hvc
  obtain ⟨smax, hsmax, hmax⟩ := isCompact_Icc.exists_isMaxOn hIcc hvc
  have hsmin' : t / 2 ≤ smin ∧ smin ≤ 3 * t / 2 := Set.mem_Icc.mp hsmin
  have hsmax' : t / 2 ≤ smax ∧ smax ≤ 3 * t / 2 := Set.mem_Icc.mp hsmax
  set vmin : ℝ := v smin with hvmin
  have hvmin0 : 0 < vmin := hvs smin hsmin'
  have hvge : ∀ s ∈ Icc (t / 2) (3 * t / 2), vmin ≤ v s := fun s hs =>
    isMinOn_iff.mp hmin s hs
  have hvle : ∀ s ∈ Icc (t / 2) (3 * t / 2), v s ≤ v smax := fun s hs =>
    isMaxOn_iff.mp hmax s hs
  obtain ⟨Mm, hMm0, hMm⟩ := exists_cont_bound (hlu := hlu) hmc
  have hMm' : ∀ s ∈ Icc (t / 2) (3 * t / 2), |m s| ≤ Mm := fun s hs =>
    hMm s (Set.mem_Icc.mp hs).1 (Set.mem_Icc.mp hs).2
  set W : ℝ := |x| + 1 + |a| + |b| + Mm with hWdef
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hWv0 : 0 ≤ W / vmin := div_nonneg hW0 hvmin0.le
  have hvsmax0 : 0 ≤ v smax := le_trans hvmin0.le (hvge smax hsmax')
  have hQ0 : 0 ≤ (W ^ 2 + v smax) / vmin ^ 2 :=
    div_nonneg (add_nonneg (sq_nonneg W) hvsmax0) (by positivity)
  have hC0p : 0 < (Real.sqrt (2 * Real.pi * vmin))⁻¹ :=
    inv_pos.2 (Real.sqrt_pos.mpr (by positivity))
  set C0p : ℝ := (Real.sqrt (2 * Real.pi * vmin))⁻¹ with hC0def
  have hWv : 0 ≤ W / vmin := div_nonneg hW0 hvmin0.le
  set S : ℝ := 1 + W / vmin + (W ^ 2 + v smax) / vmin ^ 2 with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  refine ⟨C0p * S, mul_nonneg hC0p.le (by positivity), ?_⟩
  intro s z hs1 hs2 hz1 hz2
  have hsIcc : s ∈ Icc (t / 2) (3 * t / 2) := ⟨hs1, hs2⟩
  have hs0 : 0 < v s := hvs s hsIcc
  have hvsl : vmin ≤ v s := hvge s hsIcc
  have hvsh : v s ≤ v smax := hvle s hsIcc
  have hzabs : |z| ≤ |x| + 1 + |a| + |b| := by
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self x, le_abs_self a, le_abs_self b,
        neg_le_abs_self' x, neg_le_abs_self' a, neg_le_abs_self' b]
  have hms : |m s| ≤ Mm := hMm' s ⟨hs1, hs2⟩
  have hwabs : |z - m s| ≤ W := by
    have h1 : |z - m s| ≤ |z| + |m s| := by
      have h := abs_add_le z (-(m s))
      rw [show (z + -(m s)) = (z - m s) from by ring, abs_neg] at h
      exact h
    linarith [h1, hzabs]
  have hpnn : 0 ≤ pdenGen m v s z := heatKernel_nonneg hs0 _
  have hp : |pdenGen m v s z| ≤ C0p := by
    rw [abs_of_nonneg hpnn, pdenGen, heatKernel]
    have hexp1 : Real.exp (-(z - m s) ^ 2 / (2 * v s)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      exact div_nonneg (sq_nonneg _) (by positivity)
    have hsqrt : (Real.sqrt (2 * Real.pi * vmin) : ℝ) ≤ Real.sqrt (2 * Real.pi * v s) :=
      Real.sqrt_le_sqrt (by nlinarith [hvsl, Real.pi_pos])
    calc (Real.sqrt (2 * Real.pi * v s))⁻¹
          * Real.exp (-(z - m s) ^ 2 / (2 * v s))
        ≤ (Real.sqrt (2 * Real.pi * v s))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = (Real.sqrt (2 * Real.pi * v s))⁻¹ := by rw [mul_one]
      _ ≤ C0p := by
          rw [hC0def]
          exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) hsqrt
  have hp' : pdenGen m v s z ≤ C0p := by
    rw [← abs_of_nonneg hpnn]
    exact hp
  have hpx : |pdenGenx m v s z| ≤ (W / vmin) * C0p := by
    have h1 : |pdenGenx m v s z| = |z - m s| / v s * pdenGen m v s z := by
      rw [pdenGenx, abs_mul, abs_div, abs_neg,
        abs_of_pos hs0, abs_of_nonneg hpnn]
    rw [h1]
    calc |z - m s| / v s * pdenGen m v s z
        ≤ (W / vmin) * pdenGen m v s z := by
          refine mul_le_mul_of_nonneg_right ?_ hpnn
          rw [div_le_div_iff₀ hs0 hvmin0]
          have step1 : |z - m s| * vmin ≤ W * vmin :=
            mul_le_mul_of_nonneg_right hwabs hvmin0.le
          have step2 : W * vmin ≤ W * v s := mul_le_mul_of_nonneg_left hvsl hW0
          exact step1.trans step2
      _ ≤ (W / vmin) * C0p := mul_le_mul_of_nonneg_left hp' hWv
  have hpxx : |pdenGenxx m v s z| ≤ C0p * ((W ^ 2 + v smax) / vmin ^ 2) := by
    have hw2 : (z - m s) ^ 2 ≤ W ^ 2 := by
      have hwle := abs_le.mp hwabs
      nlinarith [hwle.1, hwle.2]
    have hab : |(z - m s) ^ 2 - v s| ≤ W ^ 2 + v smax := by
      rw [abs_le]
      constructor <;> linarith [hw2, hvsl, hvsh, hvmin0.le, sq_nonneg (z - m s)]
    have hvmin2pos : (0:ℝ) < vmin ^ 2 := by positivity
    have hle2 : vmin ^ 2 ≤ (v s) ^ 2 := by nlinarith [hvsl, hvmin0.le]
    have hinv : ((v s) ^ 2)⁻¹ ≤ (vmin ^ 2)⁻¹ := inv_anti₀ hvmin2pos hle2
    have h1 : |pdenGenxx m v s z|
        = pdenGen m v s z * (|(z - m s) ^ 2 - v s| / (v s) ^ 2) := by
      rw [pdenGenxx, abs_div, abs_mul,
        abs_of_pos (show (0:ℝ) < (v s) ^ 2 by positivity), abs_of_nonneg hpnn,
        mul_div_assoc]
    rw [h1]
    calc pdenGen m v s z * (|(z - m s) ^ 2 - v s| / (v s) ^ 2)
        ≤ C0p * (|(z - m s) ^ 2 - v s| / (v s) ^ 2) :=
          mul_le_mul_of_nonneg_right hp' (by positivity)
      _ ≤ C0p * ((W ^ 2 + v smax) * ((v s) ^ 2)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0p.le
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 (sq_nonneg (v s)))
      _ ≤ C0p * ((W ^ 2 + v smax) * (vmin ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinv (add_nonneg (sq_nonneg W) hvsmax0)) hC0p.le
      _ = C0p * ((W ^ 2 + v smax) / vmin ^ 2) := by rw [div_eq_mul_inv]
  have hleWS : W / vmin ≤ S := by linarith
  have hlePS : (W ^ 2 + v smax) / vmin ^ 2 ≤ S := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h : C0p * 1 ≤ C0p * S := mul_le_mul_of_nonneg_left hS1 hC0p.le
    rw [mul_one] at h
    exact hp.trans h
  · calc |pdenGenx m v s z| ≤ (W / vmin) * C0p := hpx
      _ ≤ S * C0p := mul_le_mul_of_nonneg_right hleWS hC0p.le
      _ = C0p * S := mul_comm _ _
  · calc |pdenGenxx m v s z| ≤ C0p * ((W ^ 2 + v smax) / vmin ^ 2) := hpxx
      _ ≤ C0p * S := mul_le_mul_of_nonneg_left hlePS hC0p.le

/-! #### Differentiating the convolution under the integral -/

/-- **Differentiating the convolution in `t`** (variable coefficients): for `g` continuous
and bounded, `s ↦ ∫_{[a,b]} g(y)·p(s, x−y) dy` is differentiable at `t > 0` with
`d/dt = ∫_{[a,b]} g(y)·(−μ(t) ∂_x p + (σ(t)²/2) ∂²_x p)(t, x−y) dy`. Domination: the
explicit constant of `exists_pdenGen_bound` on `s ∈ (t/2, 3t/2)`, `z ∈ [x−1−b, x+1−a]`,
times bounds on `|μ|`, `|σ|` on the compact time range. -/
private lemma hasDerivAt_convDenGen_t (m v μ σ : ℝ → ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (ht : 0 < t)
    (hm : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt m (μ s) s)
    (hv : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt v (σ s ^ 2) s)
    (hmc : ContinuousOn m (Icc (t / 2) (3 * t / 2)))
    (hμc : ContinuousOn μ (Icc (t / 2) (3 * t / 2)))
    (hσc : ContinuousOn σ (Icc (t / 2) (3 * t / 2)))
    (hvc : ContinuousOn v (Icc (t / 2) (3 * t / 2)))
    (hvs : ∀ s ∈ Icc (t / 2) (3 * t / 2), 0 < v s)
    (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    HasDerivAt (fun s ↦ convDenGen m v g a b s x)
      (∫ y in Set.Icc a b, g y * (-μ t * pdenGenx m v t (x - y)
          + (σ t ^ 2 / 2) * pdenGenxx m v t (x - y)) ∂volume) t := by
  have hIcc : (Icc (t / 2) (3 * t / 2)).Nonempty :=
    ⟨t / 2, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hlu : t / 2 ≤ 3 * t / 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := exists_pdenGen_bound m v a b t x ht hmc hvc hvs
  obtain ⟨Mμ, _, hMμ⟩ := exists_cont_bound (hlu := hlu) hμc
  obtain ⟨Bσ, _, hBσ⟩ := exists_cont_bound (hlu := hlu) hσc
  have hMμ' : ∀ s ∈ Icc (t / 2) (3 * t / 2), |μ s| ≤ Mμ := fun s hs =>
    hMμ s (Set.mem_Icc.mp hs).1 (Set.mem_Icc.mp hs).2
  have hBσ' : ∀ s ∈ Icc (t / 2) (3 * t / 2), |σ s| ≤ Bσ := fun s hs =>
    hBσ s (Set.mem_Icc.mp hs).1 (Set.mem_Icc.mp hs).2
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  have hsigle : ∀ s ∈ Icc (t / 2) (3 * t / 2), (σ s) ^ 2 ≤ Bσ ^ 2 := by
    intro s hs
    have h1 := abs_le.mp (hBσ' s hs)
    nlinarith [h1.1, h1.2]
  have hzb : ∀ y ∈ Set.Icc a b, x - 1 - b ≤ x - y ∧ x - y ≤ x + 1 - a := by
    intro y hy
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    exact ⟨by linarith, by linarith⟩
  have hsball : ∀ s ∈ Metric.ball t (t / 2), t / 2 ≤ s ∧ s ≤ 3 * t / 2 := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith, by linarith⟩
  have hint := integrable_base 0 0 0 a b t x hab hg hgC hC0
    (F := pdenGen m v t) (continuous_pdenGen_y m v t x)
    (fun z hz1 hz2 =>
      (hC (show t / 2 ≤ t by linarith) (show t ≤ 3 * t / 2 by linarith)
        (show x - 1 - b ≤ z by linarith) (show z ≤ x + 1 - a by linarith)).1)
  have hF'c : Continuous (fun y ↦ g y * (-μ t * pdenGenx m v t (x - y)
      + (σ t ^ 2 / 2) * pdenGenxx m v t (x - y))) :=
    hg.mul (((continuous_pdenGenx_y m v t x).const_mul (-(μ t:ℝ))).add
      ((continuous_pdenGenxx_y m v t x).const_mul (σ t ^ 2 / 2)))
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ s ∈ Metric.ball t (t / 2),
      ‖g y * (-μ s * pdenGenx m v s (x - y)
          + (σ s ^ 2 / 2) * pdenGenxx m v s (x - y))‖
        ≤ Cg * ((1 + Mμ + Bσ ^ 2) * C) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy s hs
    obtain ⟨hs1, hs2⟩ := hsball s hs
    have hsIcc : s ∈ Icc (t / 2) (3 * t / 2) := ⟨hs1, hs2⟩
    obtain ⟨_, hb2, hb3⟩ := hC hs1 hs2 (hzb y hy).1 (hzb y hy).2
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |-μ s * pdenGenx m v s (x - y)
            + (σ s ^ 2 / 2) * pdenGenxx m v s (x - y)|
        ≤ |g y| * (|-μ s * pdenGenx m v s (x - y)|
            + |(σ s ^ 2 / 2) * pdenGenxx m v s (x - y)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ |g y| * (|μ s| * |pdenGenx m v s (x - y)|
            + (σ s ^ 2 / 2) * |pdenGenxx m v s (x - y)|) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ σ s ^ 2 / 2 by positivity),
            abs_neg]
      _ ≤ Cg * (|μ s| * |pdenGenx m v s (x - y)|
            + (σ s ^ 2 / 2) * |pdenGenxx m v s (x - y)|) :=
          mul_le_mul_of_nonneg_right (hgC y) (by positivity)
      _ ≤ Cg * (Mμ * |pdenGenx m v s (x - y)|
            + (σ s ^ 2 / 2) * |pdenGenxx m v s (x - y)|) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_right (hMμ' s hsIcc) (abs_nonneg _))
              le_rfl) hCg0
      _ ≤ Cg * (Mμ * C + (σ s ^ 2 / 2) * C) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hb2
                (le_trans (abs_nonneg (μ s)) (hMμ' s hsIcc)))
              (mul_le_mul_of_nonneg_left hb3 (by positivity))) hCg0
      _ ≤ Cg * ((1 + Mμ + Bσ ^ 2) * C) := by
          refine mul_le_mul_of_nonneg_left ?_ hCg0
          have h1 : (σ s) ^ 2 ≤ Bσ ^ 2 := hsigle s hsIcc
          have h2a : Mμ ≤ 1 + Mμ := by linarith
          have h2 : Mμ * C ≤ (1 + Mμ) * C := mul_le_mul_of_nonneg_right h2a hC0
          have h3a : (σ s) ^ 2 / 2 ≤ Bσ ^ 2 := by linarith [h1, sq_nonneg Bσ]
          have h3 : (σ s) ^ 2 / 2 * C ≤ Bσ ^ 2 * C :=
            mul_le_mul_of_nonneg_right h3a hC0
          calc Mμ * C + (σ s) ^ 2 / 2 * C ≤ (1 + Mμ) * C + Bσ ^ 2 * C := add_le_add h2 h3
            _ = (1 + Mμ + Bσ ^ 2) * C := by ring
  have hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun r ↦ g y * pdenGen m v r (x - y))
        (g y * (-μ s * pdenGenx m v s (x - y)
            + (σ s ^ 2 / 2) * pdenGenxx m v s (x - y))) s :=
    Filter.Eventually.of_forall fun y s hs => by
      have hsIcc : s ∈ Icc (t / 2) (3 * t / 2) := (hsball s hs)
      exact (hasDerivAt_pdenGen_t (hm s hsIcc) (hv s hsIcc) (hvs s hsIcc)).const_mul (g y)
  obtain ⟨_, hdct⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball t (t / 2))
      (x₀ := t) (μ := volume.restrict (Set.Icc a b))
      (F := fun s y ↦ g y * pdenGen m v s (x - y))
      (F' := fun s y ↦ g y * (-μ s * pdenGenx m v s (x - y)
          + (σ s ^ 2 / 2) * pdenGenxx m v s (x - y)))
      (bound := fun _ ↦ Cg * ((1 + Mμ + Bσ ^ 2) * C))
      (Metric.ball_mem_nhds t (by positivity))
      (Filter.Eventually.of_forall fun s =>
        (hg.mul (continuous_pdenGen_y m v s x)).aestronglyMeasurable
          (μ := volume.restrict (Set.Icc a b)))
      hint (hF'c.aestronglyMeasurable (μ := volume.restrict (Set.Icc a b))) hbound
      (integrable_const (Cg * ((1 + Mμ + Bσ ^ 2) * C))) hdiff
  exact hdct

/-- **Differentiating the convolution in `x`** (variable coefficients): for `g` continuous
and bounded, `x' ↦ ∫_{[a,b]} g(y)·p(t, x'−y) dy` is differentiable at every `x` with
`d/dx = ∫_{[a,b]} g(y)·∂_x p(t, x−y) dy`. Domination: continuity of the `t`-frozen
integrand families on the compact spatial range `[x−1−b, x+1−a]`. -/
private lemma hasDerivAt_convDenGen_x (m v : ℝ → ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (hvt : 0 < v t)
    (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    Integrable (fun y ↦ g y * pdenGenx m v t (x - y)) (volume.restrict (Set.Icc a b)) ∧
    HasDerivAt (fun x' ↦ convDenGen m v g a b t x')
      (∫ y in Set.Icc a b, g y * pdenGenx m v t (x - y) ∂volume) x := by
  have hlu : x - 1 - b ≤ x + 1 - a := by linarith
  obtain ⟨C1, hC10, hC1⟩ := exists_cont_bound (hlu := hlu)
    ((continuous_pdenGen_z m v t).continuousOn)
  obtain ⟨C2, hC20, hC2⟩ := exists_cont_bound (hlu := hlu)
    ((continuous_pdenGenx_z m v t).continuousOn)
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  have hint := integrable_base 0 0 0 a b t x hab hg hgC hC10
    (F := pdenGen m v t) (continuous_pdenGen_y m v t x)
    (fun z hz1 hz2 => hC1 z (by linarith) (by linarith))
  have hzb : ∀ y ∈ Set.Icc a b, ∀ x' ∈ Metric.ball x 1,
      x - 1 - b ≤ x' - y ∧ x' - y ≤ x + 1 - a := by
    intro y hy x' hx'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    exact ⟨by linarith, by linarith⟩
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      ‖g y * pdenGenx m v t (x' - y)‖ ≤ Cg * C2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy x' hx'
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |pdenGenx m v t (x' - y)| ≤ Cg * |pdenGenx m v t (x' - y)| :=
        mul_le_mul_of_nonneg_right (hgC y) (abs_nonneg _)
      _ ≤ Cg * C2 := mul_le_mul_of_nonneg_left
          (hC2 (x' - y) (hzb y hy x' hx').1 (hzb y hy x' hx').2) hCg0
  have hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      HasDerivAt (fun r ↦ g y * pdenGen m v t (r - y))
        (g y * pdenGenx m v t (x' - y)) x' :=
    Filter.Eventually.of_forall fun y x' hx' => by
      have hc : HasDerivAt (fun r : ℝ ↦ r - y) 1 x' := (hasDerivAt_id x').sub_const y
      simpa using (HasDerivAt.scomp_of_eq x'
        (hasDerivAt_pdenGen_x (m := m) (v := v) (x' - y) hvt) hc rfl).const_mul (g y)
  obtain ⟨hintx, hdct⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball x 1)
      (x₀ := x) (μ := volume.restrict (Set.Icc a b))
      (F := fun x' y ↦ g y * pdenGen m v t (x' - y))
      (F' := fun x' y ↦ g y * pdenGenx m v t (x' - y))
      (bound := fun _ ↦ Cg * C2)
      (Metric.ball_mem_nhds x (by norm_num))
      (Filter.Eventually.of_forall fun x' =>
        (hg.mul (continuous_pdenGen_y m v t x')).aestronglyMeasurable
          (μ := volume.restrict (Set.Icc a b)))
      hint
      ((hg.mul (continuous_pdenGenx_y m v t x)).aestronglyMeasurable
        (μ := volume.restrict (Set.Icc a b)))
      hbound (integrable_const (Cg * C2)) hdiff
  exact ⟨hintx, hdct⟩

/-- **Differentiating the convolution twice in `x`** (variable coefficients): the derivative
function `x' ↦ ∂_x u(t, x')` is itself differentiable at every `x` with
`d/dx = ∫_{[a,b]} g(y)·∂²_x p(t, x−y) dy`. -/
private lemma hasDerivAt_convDenGen_xx_core (m v : ℝ → ℝ) {g : ℝ → ℝ} (a b t x : ℝ)
    (hvt : 0 < v t) (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    Integrable (fun y ↦ g y * pdenGenxx m v t (x - y)) (volume.restrict (Set.Icc a b)) ∧
    HasDerivAt (fun x' ↦ ∫ y in Set.Icc a b, g y * pdenGenx m v t (x' - y) ∂volume)
      (∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume) x := by
  have hlu : x - 1 - b ≤ x + 1 - a := by linarith
  obtain ⟨C1, hC10, hC1⟩ := exists_cont_bound (hlu := hlu)
    ((continuous_pdenGenx_z m v t).continuousOn)
  obtain ⟨C3, hC30, hC3⟩ := exists_cont_bound (hlu := hlu)
    ((continuous_pdenGenxx_z m v t).continuousOn)
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  have hint := integrable_base 0 0 0 a b t x hab hg hgC hC10
    (F := pdenGenx m v t) (continuous_pdenGenx_y m v t x)
    (fun z hz1 hz2 => hC1 z (by linarith) (by linarith))
  have hzb : ∀ y ∈ Set.Icc a b, ∀ x' ∈ Metric.ball x 1,
      x - 1 - b ≤ x' - y ∧ x' - y ≤ x + 1 - a := by
    intro y hy x' hx'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    exact ⟨by linarith, by linarith⟩
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      ‖g y * pdenGenxx m v t (x' - y)‖ ≤ Cg * C3 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy x' hx'
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |pdenGenxx m v t (x' - y)| ≤ Cg * |pdenGenxx m v t (x' - y)| :=
        mul_le_mul_of_nonneg_right (hgC y) (abs_nonneg _)
      _ ≤ Cg * C3 := mul_le_mul_of_nonneg_left
          (hC3 (x' - y) (hzb y hy x' hx').1 (hzb y hy x' hx').2) hCg0
  have hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), ∀ x' ∈ Metric.ball x 1,
      HasDerivAt (fun r ↦ g y * pdenGenx m v t (r - y))
        (g y * pdenGenxx m v t (x' - y)) x' :=
    Filter.Eventually.of_forall fun y x' hx' => by
      have hc : HasDerivAt (fun r : ℝ ↦ r - y) 1 x' := (hasDerivAt_id x').sub_const y
      simpa using (HasDerivAt.scomp_of_eq x'
        (hasDerivAt_pdenGenx_x (m := m) (v := v) (x' - y) hvt) hc rfl).const_mul (g y)
  obtain ⟨hintx, hdct⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball x 1)
      (x₀ := x) (μ := volume.restrict (Set.Icc a b))
      (F := fun x' y ↦ g y * pdenGenx m v t (x' - y))
      (F' := fun x' y ↦ g y * pdenGenxx m v t (x' - y))
      (bound := fun _ ↦ Cg * C3)
      (Metric.ball_mem_nhds x (by norm_num))
      (Filter.Eventually.of_forall fun x' =>
        (hg.mul (continuous_pdenGenx_y m v t x')).aestronglyMeasurable
          (μ := volume.restrict (Set.Icc a b)))
      hint
      ((hg.mul (continuous_pdenGenxx_y m v t x)).aestronglyMeasurable
        (μ := volume.restrict (Set.Icc a b)))
      hbound (integrable_const (Cg * C3)) hdiff
  exact ⟨hintx, hdct⟩

/-- The second convolution derivative in exact `deriv ∘ deriv` form (variable
coefficients). -/
private lemma hasDerivAt_convDenGen_xx (m v : ℝ → ℝ) {g : ℝ → ℝ} (a b t x : ℝ) (hvt : 0 < v t)
    (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    HasDerivAt (fun x' ↦ deriv (fun z ↦ convDenGen m v g a b t z) x')
      (∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume) x := by
  have heq : (fun x' ↦ deriv (fun z ↦ convDenGen m v g a b t z) x')
      = (fun x' ↦ ∫ y in Set.Icc a b, g y * pdenGenx m v t (x' - y) ∂volume) := by
    funext x'
    exact (hasDerivAt_convDenGen_x m v a b t x' hvt hab hg hgC).2.deriv
  rw [heq]
  exact (hasDerivAt_convDenGen_xx_core m v a b t x hvt hab hg hgC).2

/-- **Deliverable 2 — the variable-coefficient migration lemma** (the Dupire assembly
seed): the variable-coefficient forward equation migrates through convolution against a
compactly-supported continuous bounded `g`:
`∂_t u = −μ(t) ∂_x u + (σ(t)²/2) ∂²_x u` for `u(t, x) = ∫_{[a,b]} g(y)·p(t, x−y) dy`,
`t > 0`, with `p(t, x) = K(v t, x − m t)`, `m' = μ`, `v' = σ²`. Pointwise from
`hasDerivAt_convDenGen_t/_x/_xx_core` + dominated convergence with the explicit
compact-time-range domination of `exists_pdenGen_bound`. This is the seed that scales to
the full Dupire forward equation (stage 3: `(t, x)`-dependent coefficients via Gyöngy's
conditional-expectation coefficients, per `GyongyScratch.lean`'s
`driftCoeff`/`diffCoeffSq` pattern). -/
theorem forward_eq_convolution_timeDependent (m v μ σ : ℝ → ℝ) (g : ℝ → ℝ) (a b t x : ℝ)
    (ht : 0 < t)
    (hm : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt m (μ s) s)
    (hv : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt v (σ s ^ 2) s)
    (hmc : ContinuousOn m (Icc (t / 2) (3 * t / 2)))
    (hμc : ContinuousOn μ (Icc (t / 2) (3 * t / 2)))
    (hσc : ContinuousOn σ (Icc (t / 2) (3 * t / 2)))
    (hvc : ContinuousOn v (Icc (t / 2) (3 * t / 2)))
    (hvs : ∀ s ∈ Icc (t / 2) (3 * t / 2), 0 < v s)
    (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    deriv (fun s ↦ convDenGen m v g a b s x) t
      = -μ t * deriv (fun x' ↦ convDenGen m v g a b t x') x
        + (σ t ^ 2 / 2) * deriv (deriv (fun x' ↦ convDenGen m v g a b t x')) x := by
  have hvt : 0 < v t := hvs t ⟨by linarith, by linarith⟩
  have hintx := (hasDerivAt_convDenGen_x m v a b t x hvt hab hg hgC).1
  have hX := (hasDerivAt_convDenGen_x m v a b t x hvt hab hg hgC).2
  have hintxx := (hasDerivAt_convDenGen_xx_core m v a b t x hvt hab hg hgC).1
  have hXX := (hasDerivAt_convDenGen_xx_core m v a b t x hvt hab hg hgC).2
  have hT := hasDerivAt_convDenGen_t m v μ σ a b t x ht hm hv hmc hμc hσc hvc hvs hab hg hgC
  -- the two spatial derivatives in exact `deriv` / `deriv ∘ deriv` form
  have hX' : deriv (fun x' ↦ convDenGen m v g a b t x') x
      = ∫ y in Set.Icc a b, g y * pdenGenx m v t (x - y) ∂volume := hX.deriv
  have hXX' : deriv (deriv (fun x' ↦ convDenGen m v g a b t x')) x
      = ∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume :=
    HasDerivAt.deriv (hasDerivAt_convDenGen_xx m v a b t x hvt hab hg hgC)
  rw [hT.deriv, hX', hXX']
  -- linearity of the integral closes the equation
  have hintx' : Integrable (fun y : ℝ ↦ -μ t * (g y * pdenGenx m v t (x - y)))
      (volume.restrict (Set.Icc a b)) := hintx.const_mul (-μ t)
  have hintxx' : Integrable (fun y : ℝ ↦ (σ t ^ 2 / 2) * (g y * pdenGenxx m v t (x - y)))
      (volume.restrict (Set.Icc a b)) := hintxx.const_mul (σ t ^ 2 / 2)
  have hpt : ∀ y : ℝ, g y * (-μ t * pdenGenx m v t (x - y)
        + (σ t ^ 2 / 2) * pdenGenxx m v t (x - y))
      = -μ t * (g y * pdenGenx m v t (x - y))
        + (σ t ^ 2 / 2) * (g y * pdenGenxx m v t (x - y)) := fun y => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hintx' hintxx',
    ← integral_const_mul, ← integral_const_mul]

/-! ## Stage 3 — the flux (divergence) form of the forward equation

Bagaria ch9 §9.4 eq. 9.2 (lesson 0021's PDE, lesson 0054's "flux-form PDE with
coefficients inside the derivatives"): the forward equation with the coefficients
*inside* the spatial derivatives, `∂_t p = −∂_x(μ·p) + ½ ∂²_x(σ²·p)` — the `½` stays
outside, the coefficients go inside. For the `t`-only coefficient primitives
`m, v : ℝ → ℝ` of stage 2 (`∂_x` of a `t`-only coefficient is `0`) this is
algebraically equivalent to stage 2's non-flux form — the constant-coefficient product
rule moves `μ t` / `σ t ^ 2` back out of `∂_x` / `∂²_x` — and that equivalence is the
proof: stage 2's chain plus `HasDerivAt.const_mul`. Genuinely `(t, x)`-dependent
coefficients have no density carrier in the substrate (item-10 E-pass memo, Route C:
the only proved densities are Gaussian, and hypothesis-carried versions were rejected
as vacuous), so this stage lands the *statement form* of eq. 9.2 that a later
genuine-`(t, x)` build (via Gyöngy conditional-expectation coefficients) generalizes. -/

/-- **The flux-form forward equation** (stage 3): for the density `p(t, x) = K(v t, x − m t)`
of `dX_t = μ(t) dt + σ(t) dW_t` (deterministic coefficients, `m' = μ`, `v' = σ²`,
`v t > 0`), `∂_t p = −∂_x(μ(t)·p) + ½ ∂²_x(σ(t)²·p)` at `t` — the coefficients sit
*inside* the spatial derivatives, eq. 9.2's divergence form. The proof is stage 2's
`forward_eq_timeDependent` (coefficients outside) plus the constant-coefficient product
rule, since `μ t` and `σ t ^ 2` are constants in `x`. -/
theorem forward_eq_timeDependent_flux (m v μ σ : ℝ → ℝ) (t x : ℝ)
    (hm : HasDerivAt m (μ t) t) (hv : HasDerivAt v (σ t ^ 2) t) (hvt : 0 < v t) :
    deriv (fun s ↦ pdenGen m v s x) t
      = -deriv (fun x' ↦ μ t * pdenGen m v t x') x
        + (1 / 2) * deriv (deriv (fun x' ↦ σ t ^ 2 * pdenGen m v t x')) x := by
  -- stage 2, non-flux form (coefficients outside the x-derivatives)
  have h2 := forward_eq_timeDependent m v μ σ t x hm hv hvt
  -- first-order flux identification: the t-only coefficient μ t escapes ∂_x
  have hF1 : deriv (fun x' ↦ μ t * pdenGen m v t x') x = μ t * pdenGenx m v t x :=
    (hasDerivAt_pdenGen_x x hvt).const_mul (μ t) |>.deriv
  -- second-order flux identification: σ t ^ 2 escapes ∂²_x (product rule, twice)
  have hfun : ∀ z : ℝ, deriv (fun y ↦ σ t ^ 2 * pdenGen m v t y) z
      = σ t ^ 2 * pdenGenx m v t z :=
    fun z ↦ ((hasDerivAt_pdenGen_x z hvt).const_mul (σ t ^ 2)).deriv
  have hderiv : HasDerivAt (fun z ↦ deriv (fun y ↦ σ t ^ 2 * pdenGen m v t y) z)
      (σ t ^ 2 * pdenGenxx m v t x) x := by
    rw [funext hfun]
    exact (hasDerivAt_pdenGenx_x x hvt).const_mul (σ t ^ 2)
  have hF2 : deriv (deriv (fun x' ↦ σ t ^ 2 * pdenGen m v t x')) x
      = σ t ^ 2 * pdenGenxx m v t x := hderiv.deriv
  -- the un-fluxed second spatial derivative in exact `deriv ∘ deriv` form
  have hdd : deriv (deriv (fun x' ↦ pdenGen m v t x')) x = pdenGenxx m v t x := by
    have hfun2 : (fun z ↦ deriv (fun y ↦ pdenGen m v t y) z) = (fun z ↦ pdenGenx m v t z) :=
      funext fun z ↦ (hasDerivAt_pdenGen_x z hvt).deriv
    have h2' : HasDerivAt (fun z ↦ deriv (fun y ↦ pdenGen m v t y) z)
        (pdenGenxx m v t x) x := by
      rw [hfun2]
      exact hasDerivAt_pdenGenx_x x hvt
    exact h2'.deriv
  rw [h2, hF1, hF2, (hasDerivAt_pdenGen_x x hvt).deriv, hdd]
  ring

/-- **The flux-form migration lemma** (stage 3, the Dupire assembly seed): the flux-form
forward equation migrates through convolution against a compactly-supported continuous
bounded `g`: `∂_t u = −∂_x(μ(t)·u) + ½ ∂²_x(σ(t)²·u)` for
`u(t, x) = ∫_{[a,b]} g(y)·p(t, x−y) dy`, `t > 0`, with `p(t, x) = K(v t, x − m t)`,
`m' = μ`, `v' = σ²` — eq. 9.2's divergence form, coefficients inside the spatial
derivatives. Hypotheses are exactly `forward_eq_convolution_timeDependent`'s (stage 2);
the new content is purely the conclusion's divergence form, proved by re-running stage
2's private migration engine (`hasDerivAt_convDenGen_t/_x/_xx`) and transporting across
the constant-coefficient product rule. -/
theorem forward_eq_convolution_timeDependent_flux (m v μ σ : ℝ → ℝ) (g : ℝ → ℝ)
    (a b t x : ℝ) (ht : 0 < t)
    (hm : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt m (μ s) s)
    (hv : ∀ s ∈ Icc (t / 2) (3 * t / 2), HasDerivAt v (σ s ^ 2) s)
    (hmc : ContinuousOn m (Icc (t / 2) (3 * t / 2)))
    (hμc : ContinuousOn μ (Icc (t / 2) (3 * t / 2)))
    (hσc : ContinuousOn σ (Icc (t / 2) (3 * t / 2)))
    (hvc : ContinuousOn v (Icc (t / 2) (3 * t / 2)))
    (hvs : ∀ s ∈ Icc (t / 2) (3 * t / 2), 0 < v s)
    (hab : a ≤ b) (hg : Continuous g) {Cg : ℝ} (hgC : ∀ y, |g y| ≤ Cg) :
    deriv (fun s ↦ convDenGen m v g a b s x) t
      = -deriv (fun x' ↦ μ t * convDenGen m v g a b t x') x
        + (1 / 2) * deriv (deriv (fun x' ↦ σ t ^ 2 * convDenGen m v g a b t x')) x := by
  have hvt : 0 < v t := hvs t ⟨by linarith, by linarith⟩
  have hintx := (hasDerivAt_convDenGen_x m v a b t x hvt hab hg hgC).1
  have hintxx := (hasDerivAt_convDenGen_xx_core m v a b t x hvt hab hg hgC).1
  have hX := (hasDerivAt_convDenGen_x m v a b t x hvt hab hg hgC).2
  have hT := hasDerivAt_convDenGen_t m v μ σ a b t x ht hm hv hmc hμc hσc hvc hvs hab hg hgC
  -- the un-fluxed second spatial derivative in exact `deriv ∘ deriv` form
  have hXX' : deriv (deriv (fun x' ↦ convDenGen m v g a b t x')) x
      = ∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume :=
    HasDerivAt.deriv (hasDerivAt_convDenGen_xx m v a b t x hvt hab hg hgC)
  -- first-order flux identification: the t-only coefficient μ t escapes ∂_x
  have hF1 : deriv (fun x' ↦ μ t * convDenGen m v g a b t x') x
      = μ t * ∫ y in Set.Icc a b, g y * pdenGenx m v t (x - y) ∂volume :=
    (hX.const_mul (μ t)).deriv
  -- second-order flux identification: σ t ^ 2 escapes ∂²_x (product rule, twice)
  have hfun : ∀ z : ℝ, deriv (fun y ↦ σ t ^ 2 * convDenGen m v g a b t y) z
      = σ t ^ 2 * deriv (fun y ↦ convDenGen m v g a b t y) z := by
    intro z
    have hz := (hasDerivAt_convDenGen_x m v a b t z hvt hab hg hgC).2
    rw [(hz.const_mul (σ t ^ 2)).deriv, hz.deriv]
  have hderiv : HasDerivAt (fun z ↦ deriv (fun y ↦ σ t ^ 2 * convDenGen m v g a b t y) z)
      (σ t ^ 2 * ∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume) x := by
    rw [funext hfun]
    exact (hasDerivAt_convDenGen_xx m v a b t x hvt hab hg hgC).const_mul (σ t ^ 2)
  have hF2 : deriv (deriv (fun x' ↦ σ t ^ 2 * convDenGen m v g a b t x')) x
      = σ t ^ 2 * deriv (deriv (fun x' ↦ convDenGen m v g a b t x')) x := by
    rw [hXX']
    exact hderiv.deriv
  -- normalize the flux RHS into stage 2's (ring-equal) pulled-out form, so the
  -- integral-linearity closing chain is exactly stage 2's
  have hR : -(μ t * ∫ y in Set.Icc a b, g y * pdenGenx m v t (x - y) ∂volume)
        + (1 / 2) * (σ t ^ 2 * ∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume)
      = -μ t * ∫ y in Set.Icc a b, g y * pdenGenx m v t (x - y) ∂volume
        + (σ t ^ 2 / 2) * ∫ y in Set.Icc a b, g y * pdenGenxx m v t (x - y) ∂volume := by
    ring
  rw [hT.deriv, hF1, hF2, hXX', hR]
  -- linearity of the integral closes the equation
  have hintx' : Integrable (fun y : ℝ ↦ -μ t * (g y * pdenGenx m v t (x - y)))
      (volume.restrict (Set.Icc a b)) := hintx.const_mul (-μ t)
  have hintxx' : Integrable (fun y : ℝ ↦ (σ t ^ 2 / 2) * (g y * pdenGenxx m v t (x - y)))
      (volume.restrict (Set.Icc a b)) := hintxx.const_mul (σ t ^ 2 / 2)
  have hpt : ∀ y : ℝ, g y * (-μ t * pdenGenx m v t (x - y)
        + (σ t ^ 2 / 2) * pdenGenxx m v t (x - y))
      = -μ t * (g y * pdenGenx m v t (x - y))
        + (σ t ^ 2 / 2) * (g y * pdenGenxx m v t (x - y)) := fun y => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hintx' hintxx',
    ← integral_const_mul, ← integral_const_mul]

-- Axiom audit: every theorem in this file rests on `propext`, `Classical.choice`,
-- `Quot.sound` only.
#print axioms heatKernel_heat
#print axioms hasDerivAt_pden_t
#print axioms hasDerivAt_pden_x
#print axioms hasDerivAt_pdenx_x
#print axioms forward_eq_constant_drift
#print axioms forward_eq_driftless
#print axioms pden_zero_drift_eq_gaussianPDFReal
#print axioms hasDerivAt_convDen_t
#print axioms hasDerivAt_convDen_x
#print axioms hasDerivAt_convDen_xx_core
#print axioms hasDerivAt_convDen_xx
#print axioms forward_eq_convolution
#print axioms hasDerivAt_pdenGen_x
#print axioms hasDerivAt_pdenGenx_x
#print axioms hasDerivAt_pdenGen_t
#print axioms forward_eq_timeDependent
#print axioms forward_eq_timeDependent_constant
#print axioms hasDerivAt_convDenGen_t
#print axioms hasDerivAt_convDenGen_x
#print axioms hasDerivAt_convDenGen_xx_core
#print axioms hasDerivAt_convDenGen_xx
#print axioms forward_eq_convolution_timeDependent
#print axioms forward_eq_timeDependent_flux
#print axioms forward_eq_convolution_timeDependent_flux

end ForwardEqScratch

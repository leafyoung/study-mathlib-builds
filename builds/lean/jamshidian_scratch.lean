import Mathlib
import MathFin.FixedIncome.InterestRateSwap
import MathFin.Futures.Black76
import MathFin.BlackScholes.Put
import MathFin.FixedIncome.VasicekBondPrice

/-!
# Jamshidian's swaption decomposition (lesson 0034, Bagaria ch. 8 Theorem 8.7)

The swaption is an option on a coupon bond, and in a one-factor model the option
on the coupon bond is *exactly* — pointwise in the state, not merely in
expectation — a portfolio of options on single zeros (Jamshidian 1989). Bagaria's
Theorem 8.7 is a two-line monotone-case proof; this file formalizes it and hangs
the pricing layer on the stack's proved Black-76 leaves.

Structure (the layers of lesson 0034's build plan):

* **The Bond–Swap reduction** (model-free): at expiry the floating leg is worth
  par, so the receiver swap struck at `K` is the coupon bond minus par,
  `∑ i, c i * P i - 1` with `c i = δ*K` off the last period and `c n = 1 + δ*K`
  on it — i.e. the negative of MathFin's `payerSwapValue 1 (P n) K (annuity δ P s)`
  (`receiverSwapValue_eq_couponBond`), so at the par state `K` *is* the par swap
  rate by `payerSwapValue_eq_zero_iff` (`parSwapRate_eq_of_parState`).
* **The monotone machinery**: the coupon bond is strictly decreasing in the state
  (positive weights, each bond strictly decreasing) and continuous, so a par state
  exists (IVT, `exists_parState`) and is unique (strict monotonicity,
  `unique_parState`).
* **The decomposition (the headline)**: for *any* state `xpar` where the coupon
  bond equals the strike, `(∑ c i * P i x - 1)⁺ = ∑ c i * (P i x - P i xpar)⁺`
  for every `x` — the two-case monotone split, no measure theory
  (`jamshidian_decomposition`). The payer version is the algebraic shadow via
  `max (-a) 0 = max a 0 - a` (`jamshidian_decomposition_put`).
* **The HW single-state instance**: the affine state-form bond
  `P_τ(x) = A · exp(−B_τ x)` with `B_τ = vasicekBondB κ τ > 0` (κ, τ > 0) is
  strictly decreasing in `x` — the affine shape of `hwBondPrice_affine`
  (hw_scratch.lean, lessons 0020/0033) read as a function of the short-rate state
  `x = r_T`. The par state exists concretely in this family
  (`exists_parState_hwStateBond`), by an explicit two-point IVT argument (below
  `xlo` the dominant single coupon exceeds 1; above `xhi` the whole sum is below
  1).
* **The pricing corollary (Black-76 leaves)**: under a measure `Q` (the
  `T`-forward-measure seat), if each terminal bond factor has the Black lognormal
  representation `P i ∘ x = bsTerminal (F i) 0 (σ i) T ∘ Z` a.s. — packaged per
  strip as `BSCallHyp Q (F i) (P i xpar) 0 (σ i) T Z` — then the receiver
  swaption's `Q`-price is the coupon-weighted sum of Black-76 bond-option
  formulas with strikes `P i xpar` (`receiverSwaption_black76`), and the payer
  swaption the corresponding put sum (`payerSwaption_black76`). The hypothesis is
  exactly what the Gaussian forward-measure change of numeraire delivers in HW;
  constructing that measure change is the (honestly stated) remaining bridge.

Hypotheses are the honest out — none were needed beyond the stated ones; the
`#print axioms` audit at the end shows the standard three only.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real MathFin

/-! ### Part 1: the Bond–Swap reduction (model-free) -/

/-- **The coupon-bond value at state `x`**: `∑ i ∈ s, c i * P i x` — coupons `c`,
zero-coupon prices `P` as functions of the single state. -/
def couponBondValue {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ) (s : Finset ι)
    (x : ℝ) : ℝ :=
  ∑ i ∈ s, c i * P i x

/-- **The Bond–Swap reduction** (Bagaria ch. 8.5): at expiry the floating leg is
worth par, so the *receiver* swap struck at `K` (enter receive-fixed) is the
coupon bond minus par. With uniform daycount `δ`, schedule `s ∋ n` (the last
period), and discount factors `P i` at the payment dates, the coupon schedule is
`c i = δ*K` off `n` and `c n = 1 + δ*K`; the value is the negative of MathFin's
`payerSwapValue 1 (P n) K (annuity δ P s)`. -/
theorem receiverSwapValue_eq_couponBond {ι : Type*} [DecidableEq ι] (K δ : ℝ)
    (P : ι → ℝ) (n : ι) (s : Finset ι) (hn : n ∈ s) :
    (∑ i ∈ s, (δ * K + if i = n then 1 else 0) * P i) - 1
      = -(payerSwapValue 1 (P n) K (annuity δ P s)) := by
  have hsplit : ∀ i ∈ s, (δ * K + if i = n then 1 else 0) * P i
      = δ * K * P i + (if i = n then 1 else 0) * P i := fun i _ ↦ by ring
  have hsum : ∑ i ∈ s, (δ * K + if i = n then 1 else 0) * P i
      = δ * K * ∑ i ∈ s, P i + P n := by
    rw [Finset.sum_congr rfl (fun i hi ↦ hsplit i hi), Finset.sum_add_distrib]
    have hif : ∑ i ∈ s, (if i = n then 1 else 0) * P i = P n := by
      simp [hn]
    rw [hif, ← Finset.mul_sum]
  simp only [payerSwapValue, annuity]
  rw [hsum]
  ring

/-- **The par-rate identification at the par state** (the lesson-0031 connection):
at a state `xpar` where the coupon bond equals par, the strike `K` is exactly the
par swap rate — `payerSwapValue_eq_zero_iff` applied through the reduction. -/
theorem parSwapRate_eq_of_parState {ι : Type*} [DecidableEq ι] (K δ : ℝ)
    (P : ι → ℝ → ℝ) (n : ι) (s : Finset ι) (hn : n ∈ s) (xpar : ℝ)
    (hδ : 0 < δ) (hP : ∀ i ∈ s, 0 < P i xpar) (hs : s.Nonempty)
    (hstar : ∑ i ∈ s, (δ * K + if i = n then 1 else 0) * P i xpar = 1) :
    parSwapRate 1 (P n xpar) (annuity δ (fun i ↦ P i xpar) s) = K := by
  have hpv : payerSwapValue 1 (P n xpar) K (annuity δ (fun i ↦ P i xpar) s) = 0 := by
    have hred := receiverSwapValue_eq_couponBond K δ (fun i ↦ P i xpar) n s hn
    rw [hstar] at hred
    linarith [hred]
  have hA : annuity δ (fun i ↦ P i xpar) s ≠ 0 :=
    (annuity_pos hδ (fun i hi ↦ hP i hi) hs).ne'
  exact ((payerSwapValue_eq_zero_iff 1 (P n xpar) K hA).mp hpv).symm

/-! ### Part 2: the monotone machinery (strict decrease, continuity, IVT, uniqueness) -/

/-- **The coupon bond is strictly decreasing in the state**: positive coupons and
strictly decreasing bonds make the positive combination strictly decreasing. -/
theorem couponBondValue_strictAnti {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ)
    (s : Finset ι) (hc : ∀ i ∈ s, 0 < c i) (hP : ∀ i ∈ s, StrictAnti (P i))
    (hs : s.Nonempty) : StrictAnti (couponBondValue c P s) := by
  intro x y hxy
  simp only [couponBondValue]
  have hpos : (0 : ℝ) < ∑ i ∈ s, c i * (P i x - P i y) :=
    Finset.sum_pos (fun i hi ↦ mul_pos (hc i hi) (sub_pos.mpr (hP i hi hxy))) hs
  rw [Finset.sum_congr rfl (fun i hi ↦ mul_sub (c i) (P i x) (P i y)),
    Finset.sum_sub_distrib] at hpos
  linarith

/-- The coupon bond is continuous in the state when each bond is. -/
theorem couponBondValue_continuous {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ)
    (s : Finset ι) (hP : ∀ i ∈ s, Continuous (P i)) :
    Continuous (couponBondValue c P s) := by
  unfold couponBondValue
  exact continuous_finsetSum s (fun i hi ↦ continuous_const.mul (hP i hi))

/-- **Existence of a par state** (the analysis input of Theorem 8.7): a continuous
coupon bond above the strike at `xlo` and below at `xhi` hits the strike in
between — the intermediate value theorem on the unordered interval. -/
theorem exists_parState {B : ℝ → ℝ} (hcont : Continuous B) {xlo xhi : ℝ}
    (habove : 1 < B xlo) (hbelow : B xhi < 1) : ∃ x, B x = 1 := by
  rcases le_total xlo xhi with h | h
  · have himg := intermediate_value_Icc' h hcont.continuousOn
    have h1 : (1 : ℝ) ∈ Set.Icc (B xhi) (B xlo) := ⟨hbelow.le, habove.le⟩
    obtain ⟨x, _, hBx⟩ := himg h1
    exact ⟨x, hBx⟩
  · have himg := intermediate_value_Icc h hcont.continuousOn
    have h1 : (1 : ℝ) ∈ Set.Icc (B xhi) (B xlo) := ⟨hbelow.le, habove.le⟩
    obtain ⟨x, _, hBx⟩ := himg h1
    exact ⟨x, hBx⟩

/-- **Uniqueness of the par state**: strict monotonicity of the coupon bond.
This is what makes `x*` *a point* — the one-factor hypothesis at work (with two
factors the exercise boundary is a curve, and no single set of strikes serves). -/
theorem unique_parState {B : ℝ → ℝ} (hanti : StrictAnti B) {x₁ x₂ : ℝ}
    (h₁ : B x₁ = 1) (h₂ : B x₂ = 1) : x₁ = x₂ := by
  rcases lt_trichotomy x₁ x₂ with h | h | h
  · exact absurd (h₂ ▸ h₁ ▸ hanti h) (by linarith)
  · exact h
  · exact absurd (h₁ ▸ h₂ ▸ hanti h) (by linarith)

/-- Existence + uniqueness of the par state, bundled (`∃!`). -/
theorem exists_unique_parState {B : ℝ → ℝ} (hcont : Continuous B)
    (hanti : StrictAnti B) {xlo xhi : ℝ} (habove : 1 < B xlo) (hbelow : B xhi < 1) :
    ∃! x, B x = 1 := by
  obtain ⟨w, hw⟩ := exists_parState hcont habove hbelow
  exact ⟨w, hw, fun y hy ↦ unique_parState hanti hy hw⟩

/-! ### Part 3: the decomposition (the headline) -/

/-- **Jamshidian's decomposition** (Bagaria ch. 8, Theorem 8.7): if every bond is
strictly decreasing in the single state and the coupon bond equals the strike at
`xpar`, then *for every state* `x`,

    (coupon bond at x − strike)⁺ = ∑ i, c i * (bond i at x − bond i at xpar)⁺.

The proof is the two-case monotone split: below `xpar` every bracket is positive
and the sum collapses (`∑ c i P i x − ∑ c i P i xpar`), above `xpar` every
bracket is negative and both sides vanish. No expectation is taken — the two
sides agree at every state. Uniqueness of `xpar` is not needed for the identity. -/
theorem jamshidian_decomposition {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ)
    (s : Finset ι) (hc : ∀ i ∈ s, 0 < c i) (hP : ∀ i ∈ s, StrictAnti (P i))
    (x xpar : ℝ) (hstar : couponBondValue c P s xpar = 1) :
    max (couponBondValue c P s x - 1) 0 = ∑ i ∈ s, c i * max (P i x - P i xpar) 0 := by
  have hs : s.Nonempty := by
    by_contra hns
    have h0 : couponBondValue c P s xpar = 0 := by
      simp only [couponBondValue, Finset.not_nonempty_iff_eq_empty.mp hns,
        Finset.sum_empty]
    rw [hstar] at h0
    exact one_ne_zero h0
  rcases lt_trichotomy x xpar with hx | hx | hx
  · -- x < xpar: every bracket positive, the sum collapses to the left side
    have hbr : ∀ i ∈ s, 0 < P i x - P i xpar := fun i hi ↦ sub_pos.mpr (hP i hi hx)
    have hBx : 1 < couponBondValue c P s x := by
      have hanti := couponBondValue_strictAnti c P s hc hP hs hx
      rw [hstar] at hanti
      linarith
    have hsum : (∑ i ∈ s, c i * max (P i x - P i xpar) 0)
        = couponBondValue c P s x - 1 := by
      have h1 : ∀ i ∈ s, c i * max (P i x - P i xpar) 0
          = c i * P i x - c i * P i xpar := fun i hi ↦ by
        rw [max_eq_left (hbr i hi).le, mul_sub]
      calc ∑ i ∈ s, c i * max (P i x - P i xpar) 0
          = ∑ i ∈ s, (c i * P i x - c i * P i xpar) :=
            Finset.sum_congr rfl (fun i hi ↦ h1 i hi)
        _ = ∑ i ∈ s, c i * P i x - ∑ i ∈ s, c i * P i xpar :=
            Finset.sum_sub_distrib (fun i ↦ c i * P i x) (fun i ↦ c i * P i xpar)
        _ = couponBondValue c P s x - 1 := by
            rw [show (∑ i ∈ s, c i * P i xpar) = 1 from hstar,
              show (∑ i ∈ s, c i * P i x) = couponBondValue c P s x from rfl]
    rw [max_eq_left (sub_pos.mpr hBx).le, hsum]
  · -- x = xpar: both sides zero
    subst hx
    have hrhs : ∑ i ∈ s, c i * max (P i x - P i x) 0 = 0 :=
      Finset.sum_eq_zero (fun i _ ↦ by simp)
    rw [hstar, hrhs]
    simp
  · -- xpar < x: every bracket negative, both sides zero
    have hbr : ∀ i ∈ s, max (P i x - P i xpar) 0 = 0 := fun i hi ↦
      max_eq_right (sub_nonpos.mpr (le_of_lt (hP i hi hx)))
    have hBx : couponBondValue c P s x < 1 := by
      have hanti := couponBondValue_strictAnti c P s hc hP hs hx
      rw [hstar] at hanti
      linarith
    rw [max_eq_right (sub_nonpos.mpr hBx.le), Finset.sum_eq_zero (fun i hi ↦ by
      rw [hbr i hi, mul_zero])]

/-- **The payer version** (Theorem 8.7's put direction, lesson 0034 exercise 3):
`(strike − coupon bond)⁺ = ∑ c i * (P i xpar − P i x)⁺` — same par state,
strikes unchanged, brackets flipped. Algebraic shadow of the call identity via
the pointwise `max (-a) 0 = max a 0 - a`. -/
theorem jamshidian_decomposition_put {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ)
    (s : Finset ι) (hc : ∀ i ∈ s, 0 < c i) (hP : ∀ i ∈ s, StrictAnti (P i))
    (x xpar : ℝ) (hstar : couponBondValue c P s xpar = 1) :
    max (1 - couponBondValue c P s x) 0 = ∑ i ∈ s, c i * max (P i xpar - P i x) 0 := by
  have key : ∀ a : ℝ, max (-a) 0 = max a 0 - a := by
    intro a
    rcases le_or_gt 0 a with ha | ha
    · rw [max_eq_right (neg_nonpos.mpr ha), max_eq_left ha, sub_self]
    · rw [max_eq_left (neg_nonneg.mpr ha.le), max_eq_right ha.le, zero_sub]
  have hpar : ∑ i ∈ s, c i * (P i x - P i xpar) = couponBondValue c P s x - 1 := by
    calc ∑ i ∈ s, c i * (P i x - P i xpar)
        = ∑ i ∈ s, (c i * P i x - c i * P i xpar) :=
          Finset.sum_congr rfl (fun i hi ↦ mul_sub (c i) (P i x) (P i xpar))
      _ = ∑ i ∈ s, c i * P i x - ∑ i ∈ s, c i * P i xpar :=
          Finset.sum_sub_distrib (fun i ↦ c i * P i x) (fun i ↦ c i * P i xpar)
      _ = couponBondValue c P s x - 1 := by
          rw [show (∑ i ∈ s, c i * P i xpar) = 1 from hstar,
            show (∑ i ∈ s, c i * P i x) = couponBondValue c P s x from rfl]
  have hsplit : (∑ i ∈ s, c i * max (P i xpar - P i x) 0)
      = ∑ i ∈ s, c i * max (P i x - P i xpar) 0 - (couponBondValue c P s x - 1) := by
    have hstep : ∑ i ∈ s, c i * max (P i xpar - P i x) 0
        = ∑ i ∈ s, (c i * max (P i x - P i xpar) 0 - c i * (P i x - P i xpar)) := by
      refine Finset.sum_congr rfl (fun i hi ↦ ?_)
      rw [show (P i xpar - P i x) = -(P i x - P i xpar) from by ring,
        key (P i x - P i xpar)]
      ring
    rw [hstep, Finset.sum_sub_distrib, hpar]
  rw [show (1 - couponBondValue c P s x) = -(couponBondValue c P s x - 1) from by ring,
    key, hsplit, jamshidian_decomposition c P s hc hP x xpar hstar]

/-! ### Part 4: the HW single-state instance (the affine state-form bond) -/

/-- Positivity of the Vasicek `B` coefficient: `B_τ = (1 − e^{−κτ})/κ > 0` for
κ > 0 and tenor τ > 0 — the sign that makes the affine bond strictly decreasing
in the state. -/
theorem vasicekBondB_pos {κ : ℝ} (hκ : 0 < κ) {τ : ℝ} (hτ : 0 < τ) :
    0 < vasicekBondB κ τ := by
  rw [vasicekBondB]
  exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [mul_pos hκ hτ]))) hκ

/-- **The affine state-form bond**: `P_τ(x) = A · exp(−B_τ · x)` with
`B_τ = vasicekBondB κ τ`. This is the affine term-structure shape proved in
hw_scratch.lean (`hwBondPrice_affine`: `P(0,T) = A(T)·exp(−B(T)·r₀)` with
`A(T) = hwBondA θ σ κ T`, `B(T) = vasicekBondB κ T` re-used verbatim) read as a
function of the single state `x` — at expiry `T`, `x = r_T` and `τ = τᵢ − T` the
tenor. The one-factor hypothesis of Theorem 8.7 is exactly this shape. -/
noncomputable def hwStateBond (κ A τ x : ℝ) : ℝ :=
  A * Real.exp (-(vasicekBondB κ τ * x))

/-- The state-form bond is strictly decreasing in the state: `A > 0`, `B_τ > 0`. -/
theorem hwStateBond_strictAnti {κ A τ : ℝ} (hA : 0 < A) (hκ : 0 < κ) (hτ : 0 < τ) :
    StrictAnti (hwStateBond κ A τ) := by
  have hB : 0 < vasicekBondB κ τ := vasicekBondB_pos hκ hτ
  intro x y hxy
  simp only [hwStateBond]
  refine mul_lt_mul_of_pos_left ?_ hA
  rw [Real.exp_lt_exp]
  have hmul : vasicekBondB κ τ * x < vasicekBondB κ τ * y :=
    mul_lt_mul_of_pos_left hxy hB
  linarith

/-- The state-form bond is continuous in the state. -/
theorem hwStateBond_continuous (κ A τ : ℝ) : Continuous (hwStateBond κ A τ) := by
  unfold hwStateBond
  fun_prop

/-- Helper (above the strike): below `xlo = (log(c j A j) − 1)/B_j` the single
dominant coupon already exceeds par, so the whole sum does. -/
private theorem couponBondValue_hwStateBond_gt_one {ι : Type*} (c A τ : ι → ℝ)
    (s : Finset ι) {κ : ℝ} (hκ : 0 < κ) (hc : ∀ i ∈ s, 0 < c i) (hA : ∀ i ∈ s, 0 < A i)
    (hτ : ∀ i ∈ s, 0 < τ i) (_hs : s.Nonempty) (j : ι) (hj : j ∈ s) :
    ∃ x, 1 < couponBondValue c (fun i ↦ hwStateBond κ (A i) (τ i)) s x := by
  set P : ι → ℝ → ℝ := fun i ↦ hwStateBond κ (A i) (τ i) with hPdef
  have hBj : 0 < c j * A j := mul_pos (hc j hj) (hA j hj)
  set xlo : ℝ := (Real.log (c j * A j) - 1) / vasicekBondB κ (τ j) with hxlo
  have hBne : vasicekBondB κ (τ j) ≠ 0 := (vasicekBondB_pos hκ (hτ j hj)).ne'
  have hnegexp : xlo * vasicekBondB κ (τ j) = Real.log (c j * A j) - 1 := by
    rw [hxlo]
    field_simp [hBne]
  have hterm : c j * P j xlo = Real.exp 1 := by
    simp only [hPdef, hwStateBond]
    have hneg : -(vasicekBondB κ (τ j) * xlo) = 1 - Real.log (c j * A j) := by
      rw [mul_comm (vasicekBondB κ (τ j)) xlo, hnegexp]
      ring
    rw [hneg, Real.exp_sub, Real.exp_log hBj]
    have hne : c j * A j ≠ 0 := ne_of_gt hBj
    field_simp
    exact div_self hne
  refine ⟨xlo, ?_⟩
  refine lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) ?_
  rw [← hterm]
  exact Finset.single_le_sum (f := fun i ↦ c i * P i xlo)
    (fun i hi ↦ mul_nonneg (hc i hi).le (mul_nonneg (hA i hi).le (Real.exp_pos _).le)) hj

/-- Helper (below the strike): above `xhi = (log S + 1)/b + 1` (`S = ∑ c i A i`,
`b` the smallest Vasicek coefficient over the finite tenor image) the whole sum
is dominated by `S · e^{−b xhi} < 1`. -/
private theorem couponBondValue_hwStateBond_lt_one {ι : Type*} (c A τ : ι → ℝ)
    (s : Finset ι) {κ : ℝ} (hκ : 0 < κ) (hc : ∀ i ∈ s, 0 < c i) (hA : ∀ i ∈ s, 0 < A i)
    (hτ : ∀ i ∈ s, 0 < τ i) (hs : s.Nonempty) (j : ι) (hj : j ∈ s) :
    ∃ x, couponBondValue c (fun i ↦ hwStateBond κ (A i) (τ i)) s x < 1 := by
  set P : ι → ℝ → ℝ := fun i ↦ hwStateBond κ (A i) (τ i) with hPdef
  set t : Finset ℝ := s.image τ with htim
  have ht : t.Nonempty := s.image_nonempty.mpr hs
  set τ0 : ℝ := t.min' ht with hτ0def
  have hτ0_pos : 0 < τ0 := by
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp (t.min'_mem ht)
    rw [hτ0def, hEq.symm]
    exact hτ i hi
  have hτ0_le : ∀ i ∈ s, τ0 ≤ τ i := fun i hi ↦
    t.min'_le _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hb : 0 < vasicekBondB κ τ0 := vasicekBondB_pos hκ hτ0_pos
  set S : ℝ := ∑ i ∈ s, c i * A i with hSdef
  have hSpos : 0 < S := by
    rw [hSdef]
    exact Finset.sum_pos' (fun i hi ↦ mul_nonneg (hc i hi).le (hA i hi).le)
      ⟨j, hj, mul_pos (hc j hj) (hA j hj)⟩
  have hB0 : couponBondValue c P s 0 = S := by
    simp only [couponBondValue, hPdef, hwStateBond, mul_zero, neg_zero,
      Real.exp_zero, mul_one, hSdef]
  by_cases hS1 : S < 1
  · exact ⟨0, by rw [hB0]; exact hS1⟩
  · set xhi : ℝ := (Real.log S + 1) / vasicekBondB κ τ0 + 1 with hxhi
    have hSge : (1 : ℝ) ≤ S := le_of_not_gt hS1
    have hnum : 0 < Real.log S + 1 := by linarith [Real.log_nonneg hSge]
    have hxhipos : 0 ≤ xhi :=
      le_trans (div_pos hnum hb).le (le_add_of_nonneg_right zero_le_one)
    have hbx : vasicekBondB κ τ0 * xhi = Real.log S + 1 + vasicekBondB κ τ0 := by
      rw [hxhi]; field_simp
    have hBge : ∀ i ∈ s, vasicekBondB κ τ0 ≤ vasicekBondB κ (τ i) := by
      intro i hi
      rw [vasicekBondB, vasicekBondB, div_le_div_iff_of_pos_right hκ]
      refine sub_le_sub_left ?_ 1
      rw [Real.exp_le_exp]
      have hκτ : κ * τ0 ≤ κ * τ i := mul_le_mul_of_nonneg_left (hτ0_le i hi) hκ.le
      linarith
    have hinner : ∀ i ∈ s, A i * Real.exp (-(vasicekBondB κ (τ i) * xhi))
        ≤ A i * Real.exp (-(vasicekBondB κ τ0 * xhi)) := by
      intro i hi
      refine mul_le_mul_of_nonneg_left ?_ (hA i hi).le
      rw [Real.exp_le_exp]
      have hstep : vasicekBondB κ τ0 * xhi ≤ vasicekBondB κ (τ i) * xhi :=
        mul_le_mul_of_nonneg_right (hBge i hi) hxhipos
      linarith
    have hbound : ∀ i ∈ s, c i * P i xhi
        ≤ c i * A i * Real.exp (-(vasicekBondB κ τ0 * xhi)) := by
      intro i hi
      calc c i * P i xhi
          = c i * (A i * Real.exp (-(vasicekBondB κ (τ i) * xhi))) := rfl
        _ ≤ c i * (A i * Real.exp (-(vasicekBondB κ τ0 * xhi))) :=
            mul_le_mul_of_nonneg_left (hinner i hi) (hc i hi).le
        _ = c i * A i * Real.exp (-(vasicekBondB κ τ0 * xhi)) := by ring
    have hkey : S * Real.exp (-(vasicekBondB κ τ0 * xhi)) < 1 := by
      have hbexp : Real.exp (-(vasicekBondB κ τ0 * xhi))
          ≤ Real.exp (-(Real.log S + 1)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hbx]; linarith
      have hsplit : Real.exp (-(Real.log S + 1)) = S⁻¹ * Real.exp (-1 : ℝ) := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log S), Real.exp_log hSpos]
      have h1 : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      calc S * Real.exp (-(vasicekBondB κ τ0 * xhi))
          ≤ S * Real.exp (-(Real.log S + 1)) :=
            mul_le_mul_of_nonneg_left hbexp hSpos.le
        _ = S * (S⁻¹ * Real.exp (-1 : ℝ)) := by rw [hsplit]
        _ = (S * S⁻¹) * Real.exp (-1 : ℝ) := by ring
        _ = Real.exp (-1 : ℝ) := by rw [mul_inv_cancel₀ hSpos.ne']; ring
        _ < 1 := h1
    refine ⟨xhi, ?_⟩
    calc couponBondValue c P s xhi
        ≤ ∑ i ∈ s, c i * A i * Real.exp (-(vasicekBondB κ τ0 * xhi)) :=
          Finset.sum_le_sum hbound
      _ = S * Real.exp (-(vasicekBondB κ τ0 * xhi)) := by
          rw [hSdef, ← Finset.sum_mul]
      _ < 1 := hkey

/-- **Existence of the par state in the affine family** (the IVT step made
concrete): for positive coupons, positive affine coefficients, and positive
tenors, the coupon bond `∑ c i * A i * exp(−B_i x)` — strictly decreasing,
continuous, above 1 at `xlo = (log(c j A j) − 1)/B_j` (the single dominant
coupon already exceeds par) and below 1 at `xhi = (log S + 1)/b + 1` (the whole
sum is dominated by `S · e^{−b x}`, `S = ∑ c i A i`, `b` the smallest
coefficient) — crosses the strike. -/
theorem exists_parState_hwStateBond {ι : Type*} (c A τ : ι → ℝ) (s : Finset ι)
    {κ : ℝ} (hκ : 0 < κ) (hc : ∀ i ∈ s, 0 < c i) (hA : ∀ i ∈ s, 0 < A i)
    (hτ : ∀ i ∈ s, 0 < τ i) (hs : s.Nonempty) :
    ∃ x, couponBondValue c (fun i ↦ hwStateBond κ (A i) (τ i)) s x = 1 := by
  have hPcont : ∀ i ∈ s, Continuous (hwStateBond κ (A i) (τ i)) :=
    fun i _ ↦ hwStateBond_continuous κ _ _
  have hcont : Continuous (couponBondValue c (fun i ↦ hwStateBond κ (A i) (τ i)) s) :=
    couponBondValue_continuous c _ s hPcont
  obtain ⟨j, hj⟩ := hs
  obtain ⟨xlo, hxlo⟩ :=
    couponBondValue_hwStateBond_gt_one c A τ s hκ hc hA hτ ⟨j, hj⟩ j hj
  obtain ⟨xhi, hxhi⟩ :=
    couponBondValue_hwStateBond_lt_one c A τ s hκ hc hA hτ ⟨j, hj⟩ j hj
  exact exists_parState hcont hxlo hxhi

/-- **The receiver swaption on the affine state-form bonds** — Theorem 8.7
instantiated: with coupons `δ*K` off the last period and `1 + δ*K` on it, the
receiver swaption payoff at state `x` is the portfolio of bond calls struck at
the `x*`-values, pointwise. -/
theorem receiverSwaption_hwStateBond_decomposition {ι : Type*} [DecidableEq ι]
    (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) (A τ : ι → ℝ) (s : Finset ι) (n : ι)
    (_hn : n ∈ s) {κ : ℝ} (hκ : 0 < κ) (hA : ∀ i ∈ s, 0 < A i) (hτ : ∀ i ∈ s, 0 < τ i)
    (x xpar : ℝ)
    (hstar : couponBondValue (fun i ↦ δ * K + if i = n then 1 else 0)
      (fun i ↦ hwStateBond κ (A i) (τ i)) s xpar = 1) :
    max (couponBondValue (fun i ↦ δ * K + if i = n then 1 else 0)
        (fun i ↦ hwStateBond κ (A i) (τ i)) s x - 1) 0
      = ∑ i ∈ s, (δ * K + if i = n then 1 else 0) *
          max (hwStateBond κ (A i) (τ i) x - hwStateBond κ (A i) (τ i) xpar) 0 :=
  jamshidian_decomposition _ _ _
    (fun i hi ↦ by
      by_cases h : i = n
      · rw [if_pos h]; exact add_pos (mul_pos hδ hK) one_pos
      · rw [if_neg h, add_zero]; exact mul_pos hδ hK)
    (fun i hi ↦ hwStateBond_strictAnti (hA i hi) hκ (hτ i hi)) x xpar hstar

/-! ### Part 5: the pricing corollary (the Black-76 leaves) -/

/-- Integrability of the Black-76 call payoff leaf: bounded above by the terminal
bond, which is an exponential moment of the Gaussian driver
(`integrable_exp_mul_of_hasLaw`). -/
theorem integrable_blackLeaf {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {F K σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q F K 0 σ T Z) :
    Integrable (fun ω ↦ max (bsTerminal F 0 σ T (Z ω) - K) 0) Q := by
  obtain ⟨hF, hK, hσ, hT, hZ⟩ := h
  have hZm : AEMeasurable Z Q := hZ.aemeasurable
  have hfm : Measurable (fun z : ℝ ↦
      max (F * Real.exp ((0 - σ ^ 2 / 2) * T + σ * Real.sqrt T * z) - K) 0) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (fun ω ↦ max (bsTerminal F 0 σ T (Z ω) - K) 0) Q := by
    have heq : (fun ω ↦ max (bsTerminal F 0 σ T (Z ω) - K) 0)
        = (fun z : ℝ ↦ max (F * Real.exp ((0 - σ ^ 2 / 2) * T + σ * Real.sqrt T * z) - K) 0)
            ∘ Z := by
      funext ω; unfold bsTerminal; rfl
    rw [heq]
    exact (hfm.comp_aemeasurable hZm).aestronglyMeasurable
  have hint : Integrable (fun ω ↦ bsTerminal F 0 σ T (Z ω)) Q := by
    have hshape : ∀ ω, bsTerminal F 0 σ T (Z ω)
        = (F * Real.exp ((0 - σ ^ 2 / 2) * T)) * Real.exp (σ * Real.sqrt T * Z ω) := by
      intro ω; unfold bsTerminal; rw [Real.exp_add]; ring
    exact (((integrable_exp_mul_of_hasLaw hZ (σ * Real.sqrt T)).const_mul
      (F * Real.exp ((0 - σ ^ 2 / 2) * T)))).congr
      (Filter.Eventually.of_forall (fun ω ↦ (hshape ω).symm))
  have hbound : ∀ ω, ‖max (bsTerminal F 0 σ T (Z ω) - K) 0‖
      ≤ ‖bsTerminal F 0 σ T (Z ω)‖ := by
    intro ω
    have hpos : 0 < bsTerminal F 0 σ T (Z ω) := mul_pos hF (Real.exp_pos _)
    rcases le_or_gt (bsTerminal F 0 σ T (Z ω)) K with hle | hlt
    · rw [max_eq_right (sub_nonpos.mpr hle), norm_zero]; exact norm_nonneg _
    · rw [max_eq_left (sub_nonneg.mpr hlt.le), Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hlt.le), Real.norm_eq_abs, abs_of_pos hpos]
      linarith
  exact Integrable.mono hint hmeas (Filter.Eventually.of_forall hbound)

/-- Integrability of the Black-76 put payoff leaf: bounded by the strike. -/
theorem integrable_blackLeaf_put {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {F K σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q F K 0 σ T Z) :
    Integrable (fun ω ↦ max (K - bsTerminal F 0 σ T (Z ω)) 0) Q := by
  obtain ⟨hF, hK, hσ, hT, hZ⟩ := h
  have hZm : AEMeasurable Z Q := hZ.aemeasurable
  have hfm : Measurable (fun z : ℝ ↦
      max (K - F * Real.exp ((0 - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)) 0) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (fun ω ↦ max (K - bsTerminal F 0 σ T (Z ω)) 0) Q := by
    have heq : (fun ω ↦ max (K - bsTerminal F 0 σ T (Z ω)) 0)
        = (fun z : ℝ ↦ max (K - F * Real.exp ((0 - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)) 0)
            ∘ Z := by
      funext ω; unfold bsTerminal; rfl
    rw [heq]
    exact (hfm.comp_aemeasurable hZm).aestronglyMeasurable
  have hbound : ∀ ω, ‖max (K - bsTerminal F 0 σ T (Z ω)) 0‖ ≤ ‖(K : ℝ)‖ := by
    intro ω
    have hb : 0 ≤ bsTerminal F 0 σ T (Z ω) := le_of_lt (mul_pos hF (Real.exp_pos _))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ max (K - _) 0),
      Real.norm_eq_abs, abs_of_nonneg hK.le]
    exact max_le (sub_le_self K hb) hK.le
  exact Integrable.mono (integrable_const K) hmeas (Filter.Eventually.of_forall hbound)

/-- **The Jamshidian–Black receiver swaption price** (the pricing corollary):
under `Q` — the `T`-forward measure seat — with each terminal bond factor in the
Black lognormal representation `P i ∘ x = bsTerminal (F i) 0 (σ i) T ∘ Z` a.s.
(packaged as `BSCallHyp Q (F i) (P i xpar) 0 (σ i) T Z` per strip; `F i` the
bond's `Q`-forward, `σ i` its Black vol), the receiver swaption's `Q`-price is
the coupon-weighted sum of Black-76 bond-option formulas struck at the par-state
values `P i xpar`:

    E_Q[(∑ c i P i (x ω) − 1)⁺] = ∑ c i (F i Φ(d₁ᵢ) − P i xpar Φ(d₂ᵢ)).

Route: the pointwise decomposition (`jamshidian_decomposition`, no expectation
needed) + linearity + `black_futures_formula` at `r = 0` per leaf. The hypothesis
is what the Gaussian forward-measure change of numeraire delivers in HW;
constructing `Q` and the representation from the model measure is the remaining
bridge (honestly stated, not yet built). -/
theorem receiverSwaption_black76 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Z x : Ω → ℝ}
    {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ) (σ F : ι → ℝ) (T : ℝ) (s : Finset ι)
    (xpar : ℝ) (hc : ∀ i ∈ s, 0 < c i) (hP : ∀ i ∈ s, StrictAnti (P i))
    (hstar : couponBondValue c P s xpar = 1)
    (h : ∀ i ∈ s, BSCallHyp Q (F i) (P i xpar) 0 (σ i) T Z)
    (hrepr : ∀ i ∈ s, ∀ᵐ ω ∂Q, P i (x ω) = bsTerminal (F i) 0 (σ i) T (Z ω)) :
    ∫ ω, max (∑ i ∈ s, c i * P i (x ω) - 1) 0 ∂Q
      = ∑ i ∈ s, c i *
          (F i * Phi (bsd1 (F i) (P i xpar) 0 (σ i) T)
            - P i xpar * Phi (bsd2 (F i) (P i xpar) 0 (σ i) T)) := by
  -- pointwise decomposition at the random state x ω (valid for every ω)
  have hpoint : ∀ᵐ ω ∂Q, max (∑ i ∈ s, c i * P i (x ω) - 1) 0
      = ∑ i ∈ s, c i * max (P i (x ω) - P i xpar) 0 :=
    Filter.Eventually.of_forall (fun ω ↦
      jamshidian_decomposition c P s hc hP (x ω) xpar hstar)
  -- per-strip integrability through the representation
  have hint : ∀ i ∈ s, Integrable (fun ω ↦ c i * max (P i (x ω) - P i xpar) 0) Q := by
    intro i hi
    refine ((integrable_blackLeaf (h i hi)).const_mul (c i)).congr ?_
    filter_upwards [hrepr i hi] with ω hw
    rw [hw]
  rw [integral_congr_ae hpoint, integral_finsetSum s hint]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [integral_const_mul]
  have hcongr : (fun ω ↦ max (P i (x ω) - P i xpar) 0)
      =ᵐ[Q] (fun ω ↦ max (bsTerminal (F i) 0 (σ i) T (Z ω) - P i xpar) 0) := by
    filter_upwards [hrepr i hi] with ω hw
    rw [hw]
  rw [integral_congr_ae hcongr]
  have hleaf := black_futures_formula (h i hi) 0
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at hleaf
  rw [hleaf]

/-- **The payer version**: by the put decomposition (`jamshidian_decomposition_put`)
and `bs_put_formula` at `r = 0` per leaf — strikes `P i xpar` unchanged. -/
theorem payerSwaption_black76 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Z x : Ω → ℝ}
    {ι : Type*} (c : ι → ℝ) (P : ι → ℝ → ℝ) (σ F : ι → ℝ) (T : ℝ) (s : Finset ι)
    (xpar : ℝ) (hc : ∀ i ∈ s, 0 < c i) (hP : ∀ i ∈ s, StrictAnti (P i))
    (hstar : couponBondValue c P s xpar = 1)
    (h : ∀ i ∈ s, BSCallHyp Q (F i) (P i xpar) 0 (σ i) T Z)
    (hrepr : ∀ i ∈ s, ∀ᵐ ω ∂Q, P i (x ω) = bsTerminal (F i) 0 (σ i) T (Z ω)) :
    ∫ ω, max (1 - ∑ i ∈ s, c i * P i (x ω)) 0 ∂Q
      = ∑ i ∈ s, c i *
          (P i xpar * Phi (-(bsd2 (F i) (P i xpar) 0 (σ i) T))
            - F i * Phi (-(bsd1 (F i) (P i xpar) 0 (σ i) T))) := by
  have hpoint : ∀ᵐ ω ∂Q, max (1 - ∑ i ∈ s, c i * P i (x ω)) 0
      = ∑ i ∈ s, c i * max (P i xpar - P i (x ω)) 0 :=
    Filter.Eventually.of_forall (fun ω ↦
      jamshidian_decomposition_put c P s hc hP (x ω) xpar hstar)
  have hint : ∀ i ∈ s, Integrable (fun ω ↦ c i * max (P i xpar - P i (x ω)) 0) Q := by
    intro i hi
    refine ((integrable_blackLeaf_put (h i hi)).const_mul (c i)).congr ?_
    filter_upwards [hrepr i hi] with ω hw
    rw [hw]
  rw [integral_congr_ae hpoint, integral_finsetSum s hint]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [integral_const_mul]
  have hcongr : (fun ω ↦ max (P i xpar - P i (x ω)) 0)
      =ᵐ[Q] (fun ω ↦ max (P i xpar - bsTerminal (F i) 0 (σ i) T (Z ω)) 0) := by
    filter_upwards [hrepr i hi] with ω hw
    rw [hw]
  rw [integral_congr_ae hcongr]
  have hleaf := bs_put_formula (h i hi)
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, mul_one] at hleaf
  rw [hleaf]

/-! ### Audit -/

#print axioms receiverSwapValue_eq_couponBond
#print axioms parSwapRate_eq_of_parState
#print axioms couponBondValue_strictAnti
#print axioms couponBondValue_continuous
#print axioms exists_parState
#print axioms unique_parState
#print axioms exists_unique_parState
#print axioms jamshidian_decomposition
#print axioms jamshidian_decomposition_put
#print axioms vasicekBondB_pos
#print axioms hwStateBond_strictAnti
#print axioms hwStateBond_continuous
#print axioms exists_parState_hwStateBond
#print axioms receiverSwaption_hwStateBond_decomposition
#print axioms integrable_blackLeaf
#print axioms integrable_blackLeaf_put
#print axioms receiverSwaption_black76
#print axioms payerSwaption_black76

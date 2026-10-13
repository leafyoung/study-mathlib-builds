import Mathlib
import MathFin.FixedIncome.FRA
import MathFin.FixedIncome.InterestRateSwap
import MathFin.FixedIncome.ZCB

/-!
# Tier-1 build: curve bootstrapping (lesson 0030)

Every curve on a desk starts as quotes and ends as discount factors; the algorithm
between is **bootstrapping**. This file assembles the theorem that connects the
instruments (`fraValue`, `payerSwapValue` — both carry `zero_iff` root conditions at
the pin) to a *proved* root-finder, so that "the bootstrapped curve reprices its own
inputs to tolerance" becomes machine-checked.

`MathFin.Foundations.Bisection.lean` is **not in the pinned revision** (784a831) — it
exists only at the workspace `mathfin/` clone HEAD. Per the house-lemma pattern, the
engine (`bisectStep`, `bisect`, `bisectMid`, `mapsTo_bisectStep`,
`abs_bisectMid_sub_le`, `tendsto_bisectMid`) is rebuilt privately in namespace
`Bootstrap`, porting the workspace-HEAD proofs verbatim (pin-verified names:
`squeeze_zero` takes `ℝ`-valued functions at this pin; `Real.log₂` does not exist
here, so step budgets are stated with `Real.logb 2`).

## What is built

* **Engine** (private port): the bisection iteration and its three theorems —
  bracket invariance at a threshold, error ≤ half-interval per step, convergence.
* **Threshold bridges**: the engine's hypothesis (`∀ x ∈ [lo, hi], f x < C ↔ x < σ`)
  is produced from (i) an affine function with positive slope (global), (ii) any
  strictly monotone instrument with a root in the bracket, (iii) any strictly
  antitone one (after negating value and quote).
* **Affine bootstrap step**: `affineStep_err` / `affineStep_tendsto` /
  `affineStep_value_err` / `affineStep_stepBudget` — bisection of an
  increasing rearrangement `x ↦ b·x − a` at level `−c` converges to the root
  `(a − c)/b`; the instrument reprices to within `b·(hi − lo)/2^{n+1}` of the
  quote, and `⌈log₂ (b·(hi−lo)/ε)⌉` steps buy accuracy `ε`.
* **Instruments**:
  - *FRA* (`MathFin.fraValue`): value in the new factor `x` (the later discount
    factor) is `p − (1 + δ·K)·x` — affine. Covered when `1 + δ·K > 0`
    (`K > −1/δ`); strictly antitone, so the negated value is an increasing
    solving function (`fraThreshold`), and `fraValue_newUnknown_eq_quote_iff`
    is the `zero_iff` in the new unknown (generalizing the pin's
    `fraValue_zcb_eq_zero_iff`, which the flat-curve capstone
    `fraBootstrap_flatCurve` consumes directly).
  - *Payer swap* (`MathFin.payerSwapValue`) with the fixed schedule already
    bootstrapped (`A` constant in the new factor): value `(P0 − K·A) − x`,
    always strictly antitone — no positivity condition. Root
    `P0 − K·A − c`; at zero quote the root is exactly where the fixed rate is
    par (`swapRoot_is_par`, consuming the pin's `payerSwapValue_eq_zero_iff`).
  - *Payer swap with one payment at the new maturity* (annuity `A₀ + δ·x`):
    value `(P0 − K·A₀) − (1 + K·δ)·x` — covered under `1 + K·δ > 0`
    (`swapLastCouponThreshold`).
* **The induction**: `boot` builds the curve by structural recursion over the
  instrument index — step `i` bisects instrument `i`'s solving function on the
  prefix bootstrapped so far, so each step literally inherits the previous
  factors. `boot_step_err` / `boot_step_tendsto` bound every step,
  `boot_length` (proved by induction) tracks the curve, and `boot_reprices_all`
  is the repricing theorem over all instruments (the `Finset.range` form
  `boot_reprices_range` is lesson 0030's "all inputs up to εᵢ").

## Coverage caveats (lesson 0030, Exercise 2)

* Covered: one-factor-at-a-time instruments that are affine in their new unknown
  with slope of **known strict sign** (FRA: `1 + δ·K > 0`; known-schedule swap:
  always; last-coupon swap: `1 + K·δ > 0`).
* Excluded: instruments whose *already-fixed* legs contain the new factor
  (forward-starting fixed/floating exchanges). Their value is still affine in the
  bracket, but with a slope of unknown sign — possibly zero — so no bracketing
  sign change is guaranteed; the audit must be per-leg. Also excluded: joint
  solves for several new factors at once (multicurve, Bagaria ch. 7 §7.7 — the
  Tier-2 follow-on).

No `sorry`. `#print axioms` audit at the end (standard three only).
-/

set_option autoImplicit false

namespace Bootstrap

open Filter Topology

/-! ## The private bisection engine (house port of `MathFin/Foundations/Bisection.lean`)

`Foundations/Bisection.lean` is missing at the MathFin pin (784a831), so the engine
is rebuilt here with the workspace-HEAD proof shapes, verbatim. -/

/-- One **bisection step** toward `f x = C` on the bracket `I = (a, b)`: evaluate
`f` at the midpoint `m`, keep `(m, b)` if `f m < C` and `(a, m)` otherwise. -/
noncomputable def bisectStep (f : ℝ → ℝ) (C : ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  let m := (I.1 + I.2) / 2
  if f m < C then (m, I.2) else (I.1, m)

/-- The `n`-th **bisection bracket** for `f x = C`, starting from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (bisectStep f C)^[n] (a, b)

/-- The **bisection estimate** after `n` steps: the midpoint of the `n`-th
bracket. At `n = 0` it is the midpoint of the starting bracket. -/
noncomputable def bisectMid (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) : ℝ :=
  ((bisect f C a b n).1 + (bisect f C a b n).2) / 2

@[simp] lemma bisect_zero (f : ℝ → ℝ) (C a b : ℝ) : bisect f C a b 0 = (a, b) := rfl

lemma bisect_succ (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) :
    bisect f C a b (n + 1) = bisectStep f C (bisect f C a b n) :=
  Function.iterate_succ_apply' _ _ _

/-- A bisection step halves the bracket, whatever `f` and `C` are. -/
lemma bisectStep_snd_sub_fst (f : ℝ → ℝ) (C : ℝ) (I : ℝ × ℝ) :
    (bisectStep f C I).2 - (bisectStep f C I).1 = (I.2 - I.1) / 2 := by
  simp only [bisectStep]
  split_ifs <;> ring

/-- **Halving**: the `n`-th bracket has width `(b − a) / 2ⁿ`, whatever `f` and
`C` are. -/
theorem bisect_snd_sub_fst (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) :
    (bisect f C a b n).2 - (bisect f C a b n).1 = (b - a) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [bisect_succ, bisectStep_snd_sub_fst, ih, pow_succ, div_div]

variable {f : ℝ → ℝ} {C lo hi σ : ℝ}

/-- **The trap is invariant.** If `σ` is the threshold of `f` against `C` on
`[lo, hi]`, a bisection step keeps the left endpoint in `[lo, σ]` and the right
endpoint in `[σ, hi]`: at the midpoint `m`, `f m < C` means `m < σ`, and
otherwise `σ ≤ m`. -/
theorem mapsTo_bisectStep (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ) :
    Set.MapsTo (bisectStep f C) (Set.Icc lo σ ×ˢ Set.Icc σ hi)
      (Set.Icc lo σ ×ˢ Set.Icc σ hi) := by
  rintro ⟨a, b⟩ ⟨⟨hla, haσ⟩, hσb, hbh⟩
  have hm : (a + b) / 2 ∈ Set.Icc lo hi := ⟨by linarith, by linarith⟩
  simp only [bisectStep]
  split_ifs with h
  · exact ⟨⟨hm.1, ((hC _ hm).1 h).le⟩, hσb, hbh⟩
  · exact ⟨⟨hla, haσ⟩, not_lt.1 ((hC _ hm).not.1 h), hm.2⟩

/-- **Every bisection bracket traps the threshold**: the `n`-th bracket
`(aₙ, bₙ)` from `(lo, hi)` has `aₙ ∈ [lo, σ]` and `bₙ ∈ [σ, hi]`. -/
theorem bisect_mem (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ) (hσ : σ ∈ Set.Icc lo hi)
    (n : ℕ) : bisect f C lo hi n ∈ Set.Icc lo σ ×ˢ Set.Icc σ hi :=
  (mapsTo_bisectStep hC).iterate n ⟨⟨le_rfl, hσ.1⟩, hσ.2, le_rfl⟩

/-- **Error bound**: the `n`-th estimate is within `(hi − lo) / 2ⁿ⁺¹` of the
threshold, half the width of a bracket that contains both. -/
theorem abs_bisectMid_sub_le (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ)
    (hσ : σ ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid f C lo hi n - σ| ≤ (hi - lo) / 2 ^ (n + 1) := by
  obtain ⟨⟨-, ha⟩, hb, -⟩ := bisect_mem hC hσ n
  rw [pow_succ, ← div_div, ← bisect_snd_sub_fst f C, bisectMid, abs_sub_le_iff]
  constructor <;> linarith

/-- **Convergence**: the bisection estimates converge to the threshold. -/
theorem tendsto_bisectMid (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ)
    (hσ : σ ∈ Set.Icc lo hi) : Tendsto (bisectMid f C lo hi) atTop (𝓝 σ) :=
  tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ ↦ dist_nonneg)
    (abs_bisectMid_sub_le hC hσ) <| tendsto_const_nhds.div_atTop <|
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)

/-! ## Threshold bridges: from instrument shape to the engine's hypothesis -/

/-- The threshold property is *global* for an affine function with positive
slope: `b·x − a` crosses the level `−c` exactly at the root `x = (a − c)/b`. -/
theorem threshold_affine (a b c x : ℝ) (hb : 0 < b) :
    b * x - a < -c ↔ x < (a - c) / b := by
  rw [lt_div_iff₀ hb, mul_comm x b]
  constructor <;> intro h <;> linarith

/-- A strictly monotone instrument with its root at `σ` in the bracket
satisfies the bisection engine's threshold property verbatim. -/
theorem threshold_of_strictMonoOn {V : ℝ → ℝ} {c lo hi σ : ℝ}
    (hmono : StrictMonoOn V (Set.Icc lo hi)) (hroot : V σ = c) (hσ : σ ∈ Set.Icc lo hi) :
    ∀ x ∈ Set.Icc lo hi, V x < c ↔ x < σ := by
  intro x hx
  rw [← hroot]
  exact hmono.lt_iff_lt hx hσ

/-- A strictly antitone instrument with its root at `σ` in the bracket satisfies
the engine's threshold property after negating both the value and the quote:
bisection then runs on the *increasing rearrangement* `−V` at level `−c`. -/
theorem threshold_of_strictAntiOn {V : ℝ → ℝ} {c lo hi σ : ℝ}
    (hanti : StrictAntiOn V (Set.Icc lo hi)) (hroot : V σ = c) (hσ : σ ∈ Set.Icc lo hi) :
    ∀ x ∈ Set.Icc lo hi, -V x < -c ↔ x < σ := by
  intro x hx
  constructor
  · intro h
    have hc : c < V x := by linarith
    by_contra hge
    rcases (le_of_not_gt hge).eq_or_lt with heq | hlt
    · rw [← heq, hroot] at hc
      exact absurd hc (lt_irrefl c)
    · have hlt' : V x < V σ := hanti hσ hx hlt
      rw [hroot] at hlt'
      linarith
  · intro h
    have hVS : V σ < V x := hanti hx hσ h
    rw [hroot] at hVS
    linarith

/-! ## The affine bootstrap step -/

/-- **Bootstrap step, affine form.** For a value function whose increasing
rearrangement is `x ↦ b·x − a` (`b > 0`) and quote `c`, bisection from a bracket
containing the root `(a − c)/b` lands within `(hi − lo)/2^{n+1}` of it. -/
theorem affineStep_err (a b c lo hi : ℝ) (hb : 0 < b) (hσ : (a - c) / b ∈ Set.Icc lo hi)
    (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - (a - c) / b|
      ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (fun x _ => threshold_affine a b c x hb) hσ n

/-- Convergence form of the affine bootstrap step. -/
theorem affineStep_tendsto (a b c lo hi : ℝ) (hb : 0 < b) (hσ : (a - c) / b ∈ Set.Icc lo hi) :
    Tendsto (bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi) atTop (𝓝 ((a - c) / b)) :=
  tendsto_bisectMid (fun x _ => threshold_affine a b c x hb) hσ

/-- **Repricing bound.** The instrument value `a − b·x` at the bisection
estimate is within `b·(hi − lo)/2^{n+1}` of the quote `c` — the slope-weighed
half-interval. -/
theorem affineStep_value_err (a b c lo hi : ℝ) (hb : 0 < b)
    (hσ : (a - c) / b ∈ Set.Icc lo hi) (n : ℕ) :
    |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - c|
      ≤ b * ((hi - lo) / 2 ^ (n + 1)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have key := abs_bisectMid_sub_le (f := fun x : ℝ ↦ b * x - a) (C := -c)
    (σ := (a - c) / b) (fun x _ => threshold_affine a b c x hb) hσ n
  have hexp : a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - c
      = b * ((a - c) / b - bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n) := by
    field_simp
    ring
  have hle : |(a - c) / b - bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n|
      ≤ (hi - lo) / 2 ^ (n + 1) := by
    rw [abs_sub_comm]
    exact key
  calc |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - c|
      = |b * ((a - c) / b - bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n)| := by
        rw [hexp]
    _ = |b| * |(a - c) / b - bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n| := by
          rw [abs_mul]
    _ = b * |(a - c) / b - bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n| := by
          rw [abs_of_pos hb]
    _ ≤ b * ((hi - lo) / 2 ^ (n + 1)) := mul_le_mul_of_nonneg_left hle hb.le

/-- **Step budget.** `⌈log₂ (b·(hi − lo)/ε)⌉` bisection steps buy repricing
accuracy `ε` (lesson 0030, Exercise 3). `Real.logb 2` is `log₂` — `Real.log₂`
does not exist at this Mathlib pin. -/
theorem affineStep_stepBudget (a b c lo hi ε : ℝ) (hb : 0 < b)
    (hσ : (a - c) / b ∈ Set.Icc lo hi) (hε : 0 < ε) :
    ∃ n : ℕ,
      |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - c| ≤ ε ∧
        n ≤ Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) := by
  refine ⟨Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)), ?_, le_rfl⟩
  have hlohi : lo ≤ hi := hσ.1.trans hσ.2
  have hT0 : 0 ≤ b * (hi - lo) / ε :=
    div_nonneg (mul_nonneg hb.le (sub_nonneg.mpr hlohi)) hε.le
  have hTle : b * (hi - lo) / ε
      ≤ 2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1) := by
    rcases eq_or_lt_of_le hT0 with h0 | h0
    · rw [← h0]
      exact pow_nonneg (by norm_num) _
    · have h1 : Real.logb 2 (b * (hi - lo) / ε)
          ≤ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) : ℕ) := Nat.le_ceil _
      have h2 : Real.logb 2 (b * (hi - lo) / ε)
          ≤ Real.logb 2 (2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1)) := by
        rw [Real.logb_pow 2 2 _, Real.logb_self_eq_one (by norm_num), mul_one,
          Nat.cast_add]
        linarith
      exact (Real.logb_le_logb (by norm_num) h0 (by positivity)).mp h2
  have hmain := (div_le_iff₀ hε).mp hTle
  calc |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi
        (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε))) - c|
      ≤ b * ((hi - lo) / 2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1)) :=
        affineStep_value_err a b c lo hi hb hσ _
    _ = (b * (hi - lo)) / 2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1) :=
        mul_div_assoc' b (hi - lo) _
    _ ≤ ε := by
        rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _),
          mul_comm ε (2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1))]
        exact hmain

/-! ## Instruments I: the FRA (new unknown = the later discount factor) -/

section Fra
open MathFin

/-- **The FRA as an affine function of its new unknown.** With the earlier
discount factor `p` fixed and the later one `x` bootstrapped, the FRA value at
fixed rate `K` is `p − (1 + δ·K)·x` — consuming the pin's
`fraValue_forwardRate_eq_discount_difference`. -/
theorem fraValue_affine_of_newUnknown (p δ K x : ℝ) (hδ : δ ≠ 0) (hx : x ≠ 0) :
    fraValue δ x (fraForwardRate p x δ) K = p - (1 + δ * K) * x := by
  have h := fraValue_forwardRate_eq_discount_difference p x δ K hδ hx
  rw [h]
  ring

/-- **The FRA root condition** — the `zero_iff` layer in the new unknown.
For a positive candidate factor, the FRA reprices the quote exactly at
`x = (p − c)/(1 + δ·K)`. At `c = 0` on the flat `zcb` curve this specializes to
the pin's `fraValue_zcb_eq_zero_iff` (FRA.lean:67) — same content, general
curve. -/
theorem fraValue_newUnknown_eq_quote_iff (p δ K c x : ℝ) (hδ : δ ≠ 0) (hx : 0 < x)
    (hpos : 0 < 1 + δ * K) :
    fraValue δ x (fraForwardRate p x δ) K = c ↔ x = (p - c) / (1 + δ * K) := by
  rw [fraValue_affine_of_newUnknown p δ K x hδ hx.ne', eq_div_iff hpos.ne']
  constructor <;> intro h
  · rw [mul_comm]
    linarith
  · rw [mul_comm x (1 + δ * K)] at h
    linarith

/-- Consistency with the pin: on the flat `zcb` curve the affine identity
reproduces `fraValue_zcb_eq_discount_difference` (right side equal by `ring`). -/
theorem fraValue_affine_zcb (r δ K T1 T2 : ℝ) (hδ : δ ≠ 0) :
    fraValue δ (zcb r 0 T2) (fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ) K
      = zcb r 0 T1 - (1 + δ * K) * zcb r 0 T2 :=
  fraValue_affine_of_newUnknown _ δ K _ hδ (zcb_pos r 0 T2).ne'

/-- **FRA monotonicity** (the licensing fact for bracketing): in the new
discount factor the FRA value is strictly antitone — affine with slope
`−(1 + δ·K)`, covered when `1 + δ·K > 0`. -/
theorem strictAntiOn_fraValue (p δ K : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K) :
    StrictAntiOn (fun x : ℝ ↦ fraValue δ x (fraForwardRate p x δ) K) (Set.Ioi 0) := by
  intro x hx y hy hxy
  show fraValue δ y (fraForwardRate p y δ) K < fraValue δ x (fraForwardRate p x δ) K
  rw [fraValue_affine_of_newUnknown p δ K x hδ (ne_of_gt hx),
    fraValue_affine_of_newUnknown p δ K y hδ (ne_of_gt hy)]
  linarith [mul_lt_mul_of_pos_right hxy hpos]

/-- **FRA threshold**: on a bracket of positive discount factors, the negated
FRA value at level `−c` is an increasing solving function with threshold
`(p − c)/(1 + δ·K)` — the exact hypothesis `abs_bisectMid_sub_le` consumes. -/
theorem fraThreshold (p δ K c lo hi : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K)
    (hlo : 0 < lo) (x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    -(fraValue δ x (fraForwardRate p x δ) K) < -c ↔ x < (p - c) / (1 + δ * K) := by
  have hx0 : x ≠ 0 := (lt_of_lt_of_le hlo hx.1).ne'
  rw [fraValue_affine_of_newUnknown p δ K x hδ hx0, neg_sub]
  exact threshold_affine p (1 + δ * K) c x hpos

/-- **FRA bootstrap step.** Bisection of the negated FRA value at the negated
quote computes the later discount factor to within `(hi − lo)/2^{n+1}`. -/
theorem fraStep_err (p δ K c lo hi : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K)
    (hlo : 0 < lo) (hσ : (p - c) / (1 + δ * K) ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate p x δ) K)) (-c) lo hi n
      - (p - c) / (1 + δ * K)| ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (fraThreshold p δ K c lo hi hδ hpos hlo) hσ n

/-- Convergence form of the FRA bootstrap step. -/
theorem fraStep_tendsto (p δ K c lo hi : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K)
    (hlo : 0 < lo) (hσ : (p - c) / (1 + δ * K) ∈ Set.Icc lo hi) :
    Tendsto (bisectMid (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate p x δ) K)) (-c) lo hi)
      atTop (𝓝 ((p - c) / (1 + δ * K))) :=
  tendsto_bisectMid (fraThreshold p δ K c lo hi hδ hpos hlo) hσ

/-- At the zero quote the FRA root makes the forward rate par: the bootstrapped
factor `p/(1 + δ·K)` is exactly where the quoted fixed rate equals the simple
forward rate. -/
theorem fraRoot_parForward (p δ K : ℝ) (hδ : δ ≠ 0) (hp : p ≠ 0) :
    fraForwardRate p (p / (1 + δ * K)) δ = K := by
  unfold fraForwardRate
  field_simp
  ring

/-- Cross-check with the pin's `zero_iff` layer: on the flat `zcb` curve the
bootstrap root `p/(1 + δ·K)` and the pin's par-forward characterization
(`fraValue_zcb_eq_zero_iff`'s right side, `K = fraForwardRate p x δ`) describe
the same factor. -/
theorem fraRoot_agrees_with_pin (r δ K T1 T2 : ℝ) (hδ : δ ≠ 0) :
    zcb r 0 T2 = zcb r 0 T1 / (1 + δ * K) ↔
      K = fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ := by
  have hp : zcb r 0 T1 ≠ 0 := (zcb_pos r 0 T1).ne'
  have hx : zcb r 0 T2 ≠ 0 := (zcb_pos r 0 T2).ne'
  unfold fraForwardRate
  constructor <;> intro h
  · rw [h]
    field_simp
    ring
  · rw [h]
    have h1 : (1 : ℝ) + δ * ((zcb r 0 T1 / zcb r 0 T2 - 1) / δ)
        = zcb r 0 T1 / zcb r 0 T2 := by
      field_simp
      ring
    rw [h1]
    field_simp

end Fra

/-! ## Instruments II: the payer swap -/

section Swap
open MathFin

/-- **Swap, fixed schedule known.** With the annuity `A` already bootstrapped
(every fixed payment sits at a maturity before the new one), the payer swap
value in the new factor `x` is `(P0 − K·A) − x`: affine with slope `−1`,
strictly decreasing with **no** positivity condition. -/
theorem payerSwapValue_affine_of_newUnknown (P0 K A x : ℝ) :
    payerSwapValue P0 x K A = (P0 - K * A) - 1 * x := by
  show P0 - x - K * A = (P0 - K * A) - 1 * x
  ring

/-- Swap monotonicity, known schedule: strictly antitone on all of `ℝ`. -/
theorem strictAnti_payerSwapValue (P0 K A : ℝ) :
    StrictAnti (fun x : ℝ ↦ payerSwapValue P0 x K A) := by
  intro x y hxy
  show payerSwapValue P0 y K A < payerSwapValue P0 x K A
  show P0 - y - K * A < P0 - x - K * A
  linarith

/-- **Swap threshold**, known schedule: the negated value at level `−c` has
threshold `P0 − K·A − c`. -/
theorem swapThreshold (P0 K A c lo hi : ℝ) (x : ℝ) (_hx : x ∈ Set.Icc lo hi) :
    -(payerSwapValue P0 x K A) < -c ↔ x < P0 - K * A - c := by
  have h : payerSwapValue P0 x K A = P0 - K * A - x := by
    show P0 - x - K * A = P0 - K * A - x
    ring
  rw [h, neg_sub]
  simpa only [one_mul, div_one] using threshold_affine (P0 - K * A) 1 c x one_pos

/-- **Swap bootstrap step**, known schedule: bisection of the negated value at
the negated quote computes the new discount factor to within
`(hi − lo)/2^{n+1}`. -/
theorem swapStep_err (P0 K A c lo hi : ℝ) (hσ : P0 - K * A - c ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(payerSwapValue P0 x K A)) (-c) lo hi n - (P0 - K * A - c)|
      ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (swapThreshold P0 K A c lo hi) hσ n

/-- Convergence form of the swap bootstrap step. -/
theorem swapStep_tendsto (P0 K A c lo hi : ℝ) (hσ : P0 - K * A - c ∈ Set.Icc lo hi) :
    Tendsto (bisectMid (fun x : ℝ ↦ -(payerSwapValue P0 x K A)) (-c) lo hi)
      atTop (𝓝 (P0 - K * A - c)) :=
  tendsto_bisectMid (swapThreshold P0 K A c lo hi) hσ

/-- The par-rate interpretation of the swap root: at quote zero the bootstrapped
factor `P0 − K·A` is exactly where the fixed rate is par — consuming the pin's
`payerSwapValue_eq_zero_iff` (`InterestRateSwap.lean:53`). -/
theorem swapRoot_is_par (P0 K A : ℝ) (hA : A ≠ 0) : parSwapRate P0 (P0 - K * A) A = K := by
  have h0 : payerSwapValue P0 (P0 - K * A) K A = 0 := by
    show P0 - (P0 - K * A) - K * A = 0
    ring
  exact ((payerSwapValue_eq_zero_iff P0 (P0 - K * A) K hA).mp h0).symm

/-- **Swap with one payment at the new maturity.** The fixed leg's annuity is
`A₀ + δ·x` (`A₀ = annuity δ P s` over the already-bootstrapped schedule, plus
one accrual at the new factor): value `(P0 − K·A₀) − (1 + K·δ)·x` — affine,
covered when `1 + K·δ > 0`. -/
theorem payerSwapValue_affine_lastCoupon (P0 K A₀ δ x : ℝ) :
    payerSwapValue P0 x K (A₀ + δ * x) = (P0 - K * A₀) - (1 + K * δ) * x := by
  show P0 - x - K * (A₀ + δ * x) = (P0 - K * A₀) - (1 + K * δ) * x
  ring

/-- Same, with the annuity in the pin's `annuity δ P s` form. -/
theorem payerSwapValue_affine_lastCoupon_annuity {ι : Type*} (P0 K δ x : ℝ) (P : ι → ℝ)
    (s : Finset ι) :
    payerSwapValue P0 x K (annuity δ P s + δ * x)
      = (P0 - K * annuity δ P s) - (1 + K * δ) * x :=
  payerSwapValue_affine_lastCoupon P0 K (annuity δ P s) δ x

/-- Monotonicity of the last-coupon swap: strictly antitone on all of `ℝ` under
the slope condition `1 + K·δ > 0`. -/
theorem strictAnti_payerSwapValue_lastCoupon (P0 K A₀ δ : ℝ) (hpos : 0 < 1 + K * δ) :
    StrictAnti (fun x : ℝ ↦ payerSwapValue P0 x K (A₀ + δ * x)) := by
  have h : ∀ z : ℝ, payerSwapValue P0 z K (A₀ + δ * z) = (P0 - K * A₀) - (1 + K * δ) * z :=
    fun z => payerSwapValue_affine_lastCoupon P0 K A₀ δ z
  intro x y hxy
  show payerSwapValue P0 y K (A₀ + δ * y) < payerSwapValue P0 x K (A₀ + δ * x)
  rw [h y, h x]
  linarith [mul_lt_mul_of_pos_right hxy hpos]

/-- Threshold of the last-coupon swap. -/
theorem swapLastCouponThreshold (P0 K A₀ δ c lo hi : ℝ) (hpos : 0 < 1 + K * δ) (x : ℝ)
    (_hx : x ∈ Set.Icc lo hi) :
    -(payerSwapValue P0 x K (A₀ + δ * x)) < -c ↔ x < (P0 - K * A₀ - c) / (1 + K * δ) := by
  rw [payerSwapValue_affine_lastCoupon, neg_sub]
  exact threshold_affine _ _ _ x hpos

/-- Bootstrap step for the last-coupon swap. -/
theorem swapStep_lastCoupon_err (P0 K A₀ δ c lo hi : ℝ) (hpos : 0 < 1 + K * δ)
    (hσ : (P0 - K * A₀ - c) / (1 + K * δ) ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(payerSwapValue P0 x K (A₀ + δ * x))) (-c) lo hi n
      - (P0 - K * A₀ - c) / (1 + K * δ)| ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (swapLastCouponThreshold P0 K A₀ δ c lo hi hpos) hσ n

end Swap

/-! ## The induction: the bootstrapped curve

`boot` builds the discount curve by structural recursion over the instrument
index: step `i` bisects instrument `i`'s increasing rearrangement
`x ↦ −V i (x :: prefix)` at level `−c i` on the prefix bootstrapped so far —
each step literally inherits the previous factors. The parameter `n` is the
bisection step count used at *every* instrument (uniform budget; a
per-instrument budget `n : ℕ → ℕ` is a trivial reindexing). -/

/-- The **bootstrapped curve**: after the first `i` instruments, a list of
discount factors, the head being the newest. -/
noncomputable def boot (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n : ℕ) : ℕ → List ℝ
  | 0 => []
  | i + 1 =>
      bisectMid (fun x : ℝ ↦ -(V i (x :: boot V c lo hi n i))) (-(c i)) (lo i) (hi i) n
        :: boot V c lo hi n i

/-- Length: after `i` instruments the curve holds `i` factors (the `List`
induction of lesson 0030's build plan). -/
theorem boot_length (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n i : ℕ) :
    (boot V c lo hi n i).length = i := by
  induction i with
  | zero => simp [boot]
  | succ i ih => simp only [boot, List.length_cons, ih]

/-- Definitional unfolding of the recursive step (the `i + 1` equation). -/
theorem boot_succ (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n i : ℕ) :
    boot V c lo hi n (i + 1)
      = bisectMid (fun x : ℝ ↦ -(V i (x :: boot V c lo hi n i))) (-(c i)) (lo i) (hi i) n
        :: boot V c lo hi n i := rfl

/-- Every non-initial curve is nonempty, so its head is the newest factor. -/
theorem boot_succ_ne_nil (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n i : ℕ) :
    boot V c lo hi n (i + 1) ≠ [] := by
  rw [boot_succ]
  exact List.cons_ne_nil _ _

/-- **The bootstrap step theorem, indexed.** For every instrument `i`, the
`i`-th bootstrapped factor (with `n` bisection steps per instrument) is within
`(hi i − lo i)/2^{n+1}` of that instrument's threshold `σ i`, evaluated at the
factors bootstrapped so far. The threshold hypothesis is per instrument *and
per prefix* — it must hold at the prefix the recursion actually feeds in. Since
`n` is arbitrary, letting `n → ∞` recovers convergence to the threshold (the
prefix stabilizes only under an extra constant-threshold hypothesis, which is
why the pointwise form is the honest curve-level statement). -/
theorem boot_step_err (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (σ : ℕ → List ℝ → ℝ)
    (hthr : ∀ (i : ℕ) (p : List ℝ),
      (∀ x ∈ Set.Icc (lo i) (hi i), -(V i (x :: p)) < -(c i) ↔ x < σ i p)
        ∧ σ i p ∈ Set.Icc (lo i) (hi i))
    (i n : ℕ) :
    |(boot V c lo hi n (i + 1)).head (boot_succ_ne_nil V c lo hi n i)
      - σ i (boot V c lo hi n i)| ≤ (hi i - lo i) / 2 ^ (n + 1) := by
  have h := abs_bisectMid_sub_le
    (f := fun x : ℝ ↦ -(V i (x :: boot V c lo hi n i))) (C := -(c i))
    (lo := lo i) (hi := hi i) (σ := σ i (boot V c lo hi n i))
    (fun x hx => (hthr i (boot V c lo hi n i)).1 x hx)
    (hthr i (boot V c lo hi n i)).2 n
  simp only [boot_succ, List.head_cons]
  exact h

/-- **The bootstrap repricing theorem.** Given per instrument (and per prefix)
the affine shape `V i (x :: p) = a i p − b i p · x` with slope `b i p > 0` and a
bracket containing the root, every bootstrapped factor reprices its own quote
up to the slope-weighted half-interval `b i · (hi i − lo i)/2^{n+1}` — for
every instrument `i`; `boot_reprices_range` is the "all inputs" form. -/
theorem boot_reprices_all (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (a b : ℕ → List ℝ → ℝ)
    (hb : ∀ i p, 0 < b i p)
    (hV : ∀ (i : ℕ) (p : List ℝ) (x : ℝ), V i (x :: p) = a i p - b i p * x)
    (hσ : ∀ i p, (a i p - c i) / b i p ∈ Set.Icc (lo i) (hi i))
    (i n : ℕ) :
    |V i ((boot V c lo hi n (i + 1)).head (boot_succ_ne_nil V c lo hi n i)
        :: boot V c lo hi n i) - c i|
      ≤ b i (boot V c lo hi n i) * ((hi i - lo i) / 2 ^ (n + 1)) := by
  simp only [boot_succ, List.head_cons, hV i (boot V c lo hi n i), neg_sub]
  exact affineStep_value_err (a i (boot V c lo hi n i)) (b i (boot V c lo hi n i)) (c i)
    (lo i) (hi i) (hb i _) (hσ i _) n

/-- "Reprices all inputs": the repricing bound holds for every instrument index
inside a budget of `m` instruments — lesson 0030's induction, with the
inheritance carried structurally by `boot` (each step consumes the previous
factors) and the quantifier running over `Finset.range m`. -/
theorem boot_reprices_range (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (a b : ℕ → List ℝ → ℝ)
    (hb : ∀ i p, 0 < b i p)
    (hV : ∀ (i : ℕ) (p : List ℝ) (x : ℝ), V i (x :: p) = a i p - b i p * x)
    (hσ : ∀ i p, (a i p - c i) / b i p ∈ Set.Icc (lo i) (hi i))
    (m n : ℕ) :
    ∀ i ∈ Finset.range m,
      |V i ((boot V c lo hi n (i + 1)).head (boot_succ_ne_nil V c lo hi n i)
          :: boot V c lo hi n i) - c i|
        ≤ b i (boot V c lo hi n i) * ((hi i - lo i) / 2 ^ (n + 1)) :=
  fun i _ => boot_reprices_all V c lo hi a b hb hV hσ i n

/-! ## Flat-curve capstone: the pin's `zero_iff` layer closes a full bootstrap

If the fixed rate equals the flat forward rate, the FRA's true later discount
factor on the `zcb` curve *is* the root of the solving function — consuming the
pin's `fraValue_zcb_eq_zero_iff` (FRA.lean:67) for the zero-value direction and
the engine for the convergence. Bisection from any positive bracket around the
true factor reprices it to `(hi − lo)/2^{n+1}`. -/

open MathFin in
theorem fraBootstrap_flatCurve (r δ K T1 T2 lo hi : ℝ) (hδ : δ ≠ 0)
    (hK : K = fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ)
    (hx : zcb r 0 T2 ∈ Set.Icc lo hi) (hlo : 0 < lo) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate (zcb r 0 T1) x δ) K)) (-0) lo hi n
      - zcb r 0 T2| ≤ (hi - lo) / 2 ^ (n + 1) := by
  have hpos : 0 < 1 + δ * K := by
    simp only [hK, fraForwardRate]
    have h1 : δ * ((zcb r 0 T1 / zcb r 0 T2 - 1) / δ)
        = zcb r 0 T1 / zcb r 0 T2 - 1 := by
      field_simp
    rw [h1]
    linarith [div_pos (zcb_pos r 0 T1) (zcb_pos r 0 T2)]
  have hroot : fraValue δ (zcb r 0 T2) (fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ) K = 0 :=
    (fraValue_zcb_eq_zero_iff r δ K T1 T2 hδ).mpr hK
  have hσeq : (zcb r 0 T1 - 0) / (1 + δ * K) = zcb r 0 T2 := by
    rw [hK, sub_zero]
    have hp : zcb r 0 T1 ≠ 0 := (zcb_pos r 0 T1).ne'
    have hx : zcb r 0 T2 ≠ 0 := (zcb_pos r 0 T2).ne'
    have h1 : (1 : ℝ) + δ * ((zcb r 0 T1 / zcb r 0 T2 - 1) / δ)
        = zcb r 0 T1 / zcb r 0 T2 := by
      field_simp
      ring
    unfold fraForwardRate
    rw [h1, div_eq_iff (div_ne_zero hp hx)]
    field_simp
  have hthr : ∀ x ∈ Set.Icc lo hi,
      (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate (zcb r 0 T1) x δ) K)) x < -0
        ↔ x < zcb r 0 T2 := by
    intro x hx
    have hthr' := fraThreshold (zcb r 0 T1) δ K 0 lo hi hδ hpos hlo x hx
    simpa only [sub_zero, div_eq_div_iff, neg_zero, one_mul] using
      hthr'.trans (by rw [hσeq])
  exact abs_bisectMid_sub_le hthr hx n

end Bootstrap

/-! ## Axiom audit -/
#print axioms Bootstrap.bisectStep
#print axioms Bootstrap.bisect
#print axioms Bootstrap.bisectMid
#print axioms Bootstrap.bisect_snd_sub_fst
#print axioms Bootstrap.mapsTo_bisectStep
#print axioms Bootstrap.abs_bisectMid_sub_le
#print axioms Bootstrap.tendsto_bisectMid
#print axioms Bootstrap.threshold_affine
#print axioms Bootstrap.threshold_of_strictMonoOn
#print axioms Bootstrap.threshold_of_strictAntiOn
#print axioms Bootstrap.affineStep_err
#print axioms Bootstrap.affineStep_tendsto
#print axioms Bootstrap.affineStep_value_err
#print axioms Bootstrap.affineStep_stepBudget
#print axioms Bootstrap.fraValue_affine_of_newUnknown
#print axioms Bootstrap.fraValue_newUnknown_eq_quote_iff
#print axioms Bootstrap.fraValue_affine_zcb
#print axioms Bootstrap.strictAntiOn_fraValue
#print axioms Bootstrap.fraThreshold
#print axioms Bootstrap.fraStep_err
#print axioms Bootstrap.fraStep_tendsto
#print axioms Bootstrap.fraRoot_parForward
#print axioms Bootstrap.fraRoot_agrees_with_pin
#print axioms Bootstrap.payerSwapValue_affine_of_newUnknown
#print axioms Bootstrap.strictAnti_payerSwapValue
#print axioms Bootstrap.swapThreshold
#print axioms Bootstrap.swapStep_err
#print axioms Bootstrap.swapStep_tendsto
#print axioms Bootstrap.swapRoot_is_par
#print axioms Bootstrap.payerSwapValue_affine_lastCoupon
#print axioms Bootstrap.payerSwapValue_affine_lastCoupon_annuity
#print axioms Bootstrap.strictAnti_payerSwapValue_lastCoupon
#print axioms Bootstrap.swapLastCouponThreshold
#print axioms Bootstrap.swapStep_lastCoupon_err
#print axioms Bootstrap.boot
#print axioms Bootstrap.boot_length
#print axioms Bootstrap.boot_succ
#print axioms Bootstrap.boot_step_err
#print axioms Bootstrap.boot_reprices_all
#print axioms Bootstrap.boot_reprices_range
#print axioms Bootstrap.fraBootstrap_flatCurve

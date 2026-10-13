/-
Prototype for the integrated Itô–drift identity (the `hitoid` hypothesis of
`GyongyScratch.lean`, lesson 0038), study-mathlib workspace.

Stage 1 (this file): the **constant-coefficient** specialization
`X_t = X₀ + b·t + σ·B_t`. Composed from the pinned MathFin tower:

* `MathFin.ito_formula_itoProcess` — the pathwise (a.e.) Itô formula for
  constant-coefficient Itô processes, `C³` exponential-growth class;
* `MathFin.ItoIntegralProcessGeneral.integral_itoIntegralCLM_T` — the
  stochastic term is centered, so it dies under the expectation;
* `ItoContribution.expectation_pathIntegral_eq` (new here) — the Fubini step
  `𝔼[∫₀ᵀ g s ds] = ∫₀ᵀ 𝔼[g s] ds` for a bounded path-continuous family,
  proved by pathwise Riemann sums (`MathFin.tendsto_riemann_continuous`) +
  dominated convergence on both sides; no product-measure machinery needed.

Stage 2 (the general bounded adapted case `β, δ`) is IN PROGRESS. Landed here
(toward `MathFin.ItoFormulaAdaptedDrift`):

* `crossTerminal_isometry` — the terminal cross-isometry (polarization of
  `itoIntegralCLM_T_norm`): `𝔼[(∫₀ᵀ p dB)(∫₀ᵀ q dB)] = ⟨p, q⟩_{L²(trim)}`;
* `bandIntegral_slice` — the band-slice conversion
  `∫_{(u,v]×Ω} uncurry ψ d(trimMeasure_T T) = ∫_u^v 𝔼[ψ_s] ds` for bounded adapted
  path-continuous `ψ` (predictability drops the trim; the band restriction moves
  to the time coordinate; `integral_prod` Fubini-factors).

The remaining gap to the integrated identity `𝔼[f(X_t)] = 𝔼[f(X_0)] +
∫₀ᵗ 𝔼[f′(X_s)β_s + ½f″(X_s)δ_s²] ds` (designed route, next dispatch):

1. Data shape: `β, δ` bounded adapted path-continuous; `M` a path-continuous
   strongly `natFiltration`-adapted version of the Itô integral of `δ`
   (`∀ t, M t =ᵐ itoProcessCLM (processToLp δ)`); `X := fun t ω ↦ X₀ + ∫₀ᵗβ + M t ω`
   (defined, not hypothesized — paths continuous by construction).
2. Increment-energy law: `𝔼[(M_v − M_u)²] = ∫_u^v 𝔼[δ_s²] ds` — via
   `𝔼[M_u M_v] = 𝔼[M_u²]` (Mathlib `condExp` tower + pull-out, `M_t =ᵐ 𝔼[I_T δ | 𝓕_t]`)
   + `itoProcessCLM_norm_sq` + band-difference algebra + `bandIntegral_slice`.
3. Weighted increment-isometry (the one genuinely new theory piece):
   `𝔼[w (M_v−M_u)²] = 𝔼[w ∫_u^v δ²]` for `w` bounded, `AdaptedAt B u w` — via the
   left-endpoint step approximants `δⁿ` of `δ`: for them the identity is
   independence-algebra (`adapted_indepFun_increment` + `integral_increment_sq`),
   and the passage `n → ∞` is the L²-contraction `‖Δ(M − Mⁿ)‖₂ ≤ 2‖δ − δⁿ‖_{L²(trim)}`
   plus `∫ (δ − δⁿ)² → 0` by pathwise uniform continuity + DCT.
4. Drift block: `Σₖ f′(X_{tₖ})∫_cell β → ∫₀ᵀ f′(X)β` in L¹ (pathwise
   `tendsto_riemann_continuous` + the cell-oscillation bound `C₁Tω_β(T/n) → 0` + DCT).
5. Taylor remainder: `𝔼[R_n] ≤ C₃Σₖ𝔼|ΔX_k|³` needs a third-moment bound for the
   bounded-coefficient martingale increment `𝔼|∫_cell δ dW|³ = O(cell^{3/2})` —
   NOT in the stack (no BDG); cheapest route is the discrete 4th-moment
   combinatorics for finite sums of independent centered increments.
6. Assembly: `DiscreteIto.discrete_ito_formula` per path (exact identity), take
   expectations, apply 3–5, close with `expectation_pathIntegral_eq` (stage 1).

`GyongyScratch.lean` keeps `hitoid` until 1–6 land.

**Dispatch-5 status (2026-10-07).** Landed, zero `sorry`, standard-three axioms: the
**unconditional gap decay** — `errorIncr_ae` (the error increment `δεₖ = ΔMₖ − δ(tₖ)ΔBₖ`
is a.e. the band increment of the CLM process of the integrand error `ψₙ = φ − δⁿ`), the
band-energy transfer `errorIncr_sq_eq_band` / `weightedErrorIncr_sq_le` (weighted error
energy ≤ `C_w²` cell-band energies), the real `L²` triangle `sqrtIntegral_sq_add_le`, the
**per-cell gap bound** `cellGap_le` (Cauchy–Schwarz pairing of `δεₖ` against the cell
energy `ΔMₖ + δ(tₖ)ΔBₖ`; bound `2|C_w||D_δ|√cell·√bandE` exactly as designed), and the
**summed gap bound** `gapSum_le` (finite-sum Cauchy–Schwarz over cell lengths and band
energies; total `2|C_w||D_δ|√T·‖φ − δⁿ‖`), feeding `quadraticSqSum_tendsto_uncond` —
the convergence of the quadratic block UNCONDITIONAL (the `hgap` hypothesis of
`quadraticSqSum_tendsto` discharged by `gapSum_le` + `deltaStepLp_tendsto` with
`r n := ‖φ − δⁿ‖_{L²(trim)}`). Stage 4's summed weighted increment isometry is therefore
complete. **Stage 5b/5c remain** (third-moment bound + drift/cross/remainder assembly);
a full implementation draft of the step-sum 4th-moment recursion `stepSum_pow4_le`
(independence expansion, potential `3S² + 6D²SC + 3D⁴Q`, odd-term kernels by Young's
inequality `|a|³|b| ≤ (3/4)|a|⁴ + (1/4)|b|⁴`) is preserved at
`builds/lean/itocontribution-stage5b-wip.lean` — it needs a final integrability-plumbing
pass (the `abs_of_nonneg`/`pow_abs`/`sq_le_sq'` elaboration-order details) before
landing; resume from there.

**Dispatch-4 status (2026-10-07).** Landed, zero `sorry`, standard-three axioms:
the **per-cell weighted identity** `weightedCellSq_step` (`𝔼[w·(δ(tₖ)·ΔBₖ)²] =
𝔼[w·δ(tₖ)²]·(tₖ₊₁ − tₖ)` — the isometry kernel `integral_adapted_mul_increment_sq` at
`χ = w·δ(tₖ)²`, adapted via the Doob–Dynkin bridge `adaptedAt_of_measurable_natural`),
the **per-cell step identification** `stepIncr_stepCLM_ae` (`Δ(CLM(δⁿ))ₖ = δ(tₖ)ΔBₖ` a.e.,
min-algebra on `itoSimpleProcess_apply`), the **CLM band-energy law** `clm_band_energy`
(`𝔼[(CLM(φ′)_v − CLM(φ′)_u)²] = ∫_{(u,v]×Ω}(φ′)²` — version-free, via the a.e.
pull-out + `itoProcessCLM_norm_sq` + the nested-band split), the **frozen Riemann
convergence** `frozenRiemann_tendsto` (mean-function Riemann sums via
`tendsto_riemann_continuous`), the **uniform-band split** `uniform_band_split`, the
real-`L²` pairing bound `integral_abs_mul_le_L2L2`, the energy bounds `trueIncr_sq_le`
(`𝔼[(ΔM)²] ≤ D_δ²·cell`) and `stepIncrSq_le`, and the **convergence of the quadratic
block** `quadraticSqSum_tendsto` — conditional on the per-partition `L¹` gap decay
(hypothesis `hgap`, an abstract null-sequence bound): the per-cell Cauchy–Schwarz pairing
of the error increment `δε = ΔM − δ(tₖ)ΔBₖ` against the cell energy, each factor bounded
by `trueIncr_sq_le`/`stepIncrSq_le`/`clm_band_energy`, the cell bands paired by
finite-sum Cauchy–Schwarz, total decay `2|C_w||D_δ|√T·‖φ − δⁿ‖ → 0` by
`deltaStepLp_tendsto`. The conditional statement is the honest cut: the gap proof's
plumbing (a.e.-congruence bookkeeping for `δε`, the `TendstoInMeasure` → a.e.-subsequence
→ Fatou passage for the third-moment bound) is the designed next step (≈300 lines), as is
the full assembly `itoDrift_expectation_identity_adapted` (drift block by pathwise
step-family DCT + stage-1 Fubini; cross terms by the martingale pull-out; Taylor remainder
by the third-moment bound) — consuming `quadraticSqSum_tendsto` with
`r n := ‖φ − δⁿ‖_{L²(trim)}` and `DiscreteIto.discrete_ito_formula`.

**Dispatch-3 status (2026-10-07).** Landed, zero `sorry`, standard-three axioms:
item 2 of the designed route — `incrementEnergy` (the unweighted increment isometry
`𝔼[(M_v − M_u)²] = ∫_u^v 𝔼[δ_s²] ds`, via the martingale pull-out `𝔼[M_u M_v] =
𝔼[M_u²]`, `itoProcessCLM_norm_sq`, the nested-band split, and `bandIntegral_slice`);
plus the two stage-3 analytic inputs — `integral_mul_condExp_eq` (tower pull-out),
`memLp_M`, `deltaStepLp`/`deltaStepLp_tendsto` (`‖δⁿ − δ‖_{L²(trim)} → 0`, obtained
isometry-free by transferring the Riemann bridge's `L²` convergence of the Itô sums
through `itoIntegralCLM_T_norm`). TwoLean-level discoveries recorded here for the
next dispatch: (i) this Mathlib pin defines `MemLp f p μ` as a *conjunction*
(`AEStronglyMeasurable ∧ eLpNorm < ∞`) — no `MemLp.congr_ae` projection, build it
with `⟨h.1.congr …, (eLpNorm_congr_ae …).trans h.2⟩`; (ii) `IntegrableOn f s μ` is
`Integrable f (μ.restrict s)`, and `setIntegral_union` wants the *predictable*
measurability of the band. Remaining (designed route items 3–6, ≈600–800 lines):
the per-cell weighted identity `𝔼[wₖ·(δ(tₖ)ΔBₖ)²] = 𝔼[wₖδ(tₖ)²]·cell`
(`integral_adapted_mul_increment_sq` at `χ = wₖ·δ(tₖ)²`), the per-cell step
identification `Δ(CLM(φⁿ))ₖ = δ(tₖ)ΔBₖ` (cutoff algebra via `itoSimpleProcess_apply`
+ `itoProcessCLM_simpleAssembly_T`), the L¹-difference decay
`Σₖ𝔼|wₖ((ΔMₖ)² − (δₖΔBₖ)²)| ≤ 2C₂D_δ√T·‖δ − δⁿ‖ → 0` (Cauchy–Schwarz pairing
band_k with cell_k), the Riemann convergence of `Σₖcellₖ·𝔼[f″(X_{tₖ})δ(tₖ)²]`, the
third-moment bound `𝔼|ΔMₖ|³ ≤ 9^{3/4}D_δ³cell^{3/2}` (step-sum 4th-moment recursion
+ `TendstoInMeasure.exists_seq_tendsto_ae` + Fatou via `lintegral_liminf_le`), and
the drift/remainder assembly with `DiscreteIto.discrete_ito_formula`.
-/
import MathFin.Foundations.ItoFormulaItoProcess
import MathFin.Foundations.ItoIntegralProcessGeneral
import MathFin.Foundations.AdaptedProcessToLp
import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
import MathFin.Foundations.WeightedQuadraticVariation
import MathFin.Foundations.ItoFormulaRemainder
import MathFin.Foundations.DiscreteIto
import MathFin.Foundations.ItoIntegralProcessIsometry
import MathFin.Foundations.ItoIsometryAdapted
import MathFin.Foundations.ItoIntegralBrownian
import MathFin.Foundations.QuadraticVariationL2
import MathFin.Foundations.GaussianMoments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ItoContribution

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Telescoping over a partition: `∑_{k<n} (a_{k+1} − a_k) = a_n − a_0`. -/
private theorem sum_telescope (a : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (a (k + 1) - a k) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Fubini for the path integral of a bounded path-continuous family** (the
interchange the integrated Itô–drift identity needs):

  `𝔼[∫₀ᵀ g(s, ω) ds] = ∫₀ᵀ 𝔼[g(s, ·)] ds`

for `g` bounded on `[0, T] × Ω` with every `ω`-path continuous. Proof shape:
pathwise Riemann sums (`MathFin.tendsto_riemann_continuous` — deterministic,
applied per `ω` and to the deterministic mean function `s ↦ 𝔼[g s]`) +
dominated convergence (dominator `C·T`) for the expectation of the limit. No
product measure, no Tonelli — boundedness makes both DCTs one-liners. -/
theorem expectation_pathIntegral_eq {w : ℝ≥0 → Ω → ℝ}
    (hw_meas : ∀ s, Measurable (w s))
    (hw_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    ∫ ω, (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  -- bounded functions are integrable under the probability measure
  have hint_w : ∀ s, Integrable (w s) μ := fun s ↦
    Integrable.of_bound (hw_meas s).aestronglyMeasurable C
      (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hw_bdd s ω)
  -- the mean function `s ↦ 𝔼[w s]` is bounded by `C` and continuous in `s`
  have hu_bdd : ∀ s, |∫ ω, w s ω ∂μ| ≤ C := by
    intro s
    calc |∫ ω, w s ω ∂μ| ≤ ∫ ω, |w s ω| ∂μ :=
        MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ ω, C ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ abs_nonneg _) (integrable_const C)
          (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hw_bdd s ω)
      _ = C := by rw [integral_const]; simp
  have hu_cont : Continuous fun s : ℝ≥0 ↦ ∫ ω, w s ω ∂μ :=
    continuous_iff_continuousAt.2 fun s₀ ↦
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (bound := fun _ : Ω ↦ C)
        (Eventually.of_forall fun s ↦ (hw_meas s).aestronglyMeasurable)
        (Eventually.of_forall fun s ↦ Eventually.of_forall fun ω ↦ by
          simpa [Real.norm_eq_abs] using hw_bdd s ω)
        (integrable_const C)
        (Eventually.of_forall fun ω ↦ (hw_cont ω).continuousAt)
  -- pathwise Riemann convergence per `ω` (the tower's deterministic lemma,
  -- applied to each `ω`-path) and for the deterministic mean function
  have hpath : ∀ ω : Ω, Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
          w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure)) :=
    fun ω ↦ tendsto_riemann_continuous (h := fun s : ℝ≥0 ↦ w s ω) (hw_cont ω) T
      (fun s _ ↦ hw_bdd s ω)
  have hdet : Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) :=
    tendsto_riemann_continuous (h := fun s : ℝ≥0 ↦ ∫ ω, w s ω ∂μ) hu_cont T
      (fun s _ ↦ hu_bdd s)
  -- measurability / integrability of the Riemann sums
  have hmeas_R : ∀ n : ℕ, Measurable (fun ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := fun n ↦
    Finset.measurable_sum _ fun k _ ↦ (hw_meas _).mul_const _
  have hint_R : ∀ n : ℕ, Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) μ := fun n ↦
    integrable_finsetSum _ fun k _ ↦ (hint_w _).mul_const _
  -- domination of the Riemann sums: `|R_n(ω)| ≤ C·T`
  have hR_bound : ∀ n : ℕ, ∀ ω : Ω,
      |∑ k ∈ Finset.range n,
          w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ C * (T : ℝ) := by
    intro n ω
    have hCT : (0 : ℝ) ≤ C * (T : ℝ) := mul_nonneg hC0 (NNReal.coe_nonneg T)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      exact hCT
    · have hΔ : ∀ k : ℕ, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ≥ 0 :=
        fun k ↦ sub_nonneg.mpr (by exact_mod_cast unifPart_mono T n (Nat.le_succ k))
      have hnn : unifPart T n n = T := by
        have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
        simp only [unifPart, div_self hne, one_mul]
      calc |∑ k ∈ Finset.range n,
            w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
          ≤ ∑ k ∈ Finset.range n,
            |w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range n,
            |w (unifPart T n k) ω| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
            Finset.sum_congr rfl fun k _ ↦ by rw [abs_mul, abs_of_nonneg (hΔ k)]
        _ ≤ ∑ k ∈ Finset.range n, C * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
            Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hw_bdd _ ω) (hΔ k)
        _ = C * ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
            (Finset.mul_sum (Finset.range n)
              (fun k ↦ ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) C).symm
        _ = C * ((unifPart T n n : ℝ) - unifPart T n 0) := by
            rw [sum_telescope (a := fun k ↦ ((unifPart T n k : ℝ)))]
        _ = C * (T : ℝ) := by
            rw [hnn]
            simp only [unifPart, Nat.cast_zero, zero_div, zero_mul, NNReal.coe_zero,
              sub_zero]
  -- dominated convergence: `𝔼[R_n] → 𝔼[∫ w]`
  have hdct : Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ∂μ)
      atTop (𝓝 (∫ ω, (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ C * (T : ℝ))
      (fun n ↦ (hmeas_R n).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ Eventually.of_forall fun (ω : Ω) ↦ by
        simpa [Real.norm_eq_abs] using hR_bound n ω)
      (Eventually.of_forall fun ω ↦ hpath ω)
  -- the deterministic Riemann sums have the same values as `𝔼[R_n]` (finite sums),
  -- so the deterministic limit must be `𝔼[∫ w]`
  have hsum_eq : ∀ n : ℕ,
      ∫ ω, (∑ k ∈ Finset.range n,
          w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ∂μ
        = ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    rw [integral_finsetSum _ fun k _ ↦ (hint_w _).mul_const _]
    exact Finset.sum_congr rfl fun k _ ↦ integral_mul_const _ _
  have hdet' : Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
    refine hdet.congr' ?_
    exact Eventually.of_forall fun n ↦ (hsum_eq n).symm
  exact (tendsto_nhds_unique hdet' hdct).symm

/-- **The integrated Itô–drift identity, constant-coefficient case** (stage 1 of
the `hitoid` content of `GyongyScratch.lean`). For the constant-coefficient Itô
process `X_t = X₀ + b·t + σ·B_t` and `f ∈ C³` with bounded first three
derivatives,

  `𝔼[f(X_T)] = 𝔼[f(X₀ + b·0 + σ·B₀)] + ∫₀ᵀ 𝔼[f'(X_s)·b + ½·f''(X_s)·σ²] ds`.

Route: `MathFin.ito_formula_itoProcess` (the pathwise a.e. Itô formula) gives
`f(X_T) − f(X_0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ g(s,·) ds` with the stochastic
term the genuine Itô integral of `σ·f'(X_·)`; integrating kills the stochastic
term by centering (`integral_itoIntegralCLM_T`) and interchanges the drift
integral with the expectation by `ItoContribution.expectation_pathIntegral_eq`.
The C³-with-bounded-derivatives class instantiates the exponential-growth
hypotheses of `ito_formula_itoProcess` at `λ = 0`. -/
theorem itoDrift_expectation_identity
    (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    (T : ℝ≥0) (X₀ b σ : ℝ) {f f' f'' f''' : ℝ → ℝ}
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf'' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg' : ∀ x, |f' x| ≤ C1) (hg'' : ∀ x, |f'' x| ≤ C2)
    (hg''' : ∀ x, |f''' x| ≤ C3) :
    ∫ ω, f (X₀ + b * (T : ℝ) + σ * B T ω) ∂μ
      = ∫ ω, f (X₀ + b * (0 : ℝ) + σ * B 0 ω) ∂μ
        + ∫ s in Set.Ioc 0 T,
            (∫ ω, f' (X₀ + b * (s : ℝ) + σ * B s ω) * b
                + (1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2) ∂μ)
          ∂ItoIntegralL2.timeMeasure := by
  have hC1 : (0 : ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg' 0)
  -- continuity of `f`, `f'`, `f''` (one higher derivative each)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  have hf''c : Continuous f'' := Differentiable.continuous fun x ↦ (hf''' x).differentiableAt
  -- the drift weight process `g`, in the exact shape of the formula's drift term
  set g : ℝ≥0 → Ω → ℝ := fun s ω ↦ f' (X₀ + b * (s : ℝ) + σ * B s ω) * b
      + (1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2) with hg_def
  -- measurability of the inner argument and of the weight sections
  have harg_meas : ∀ s : ℝ≥0, Measurable (fun ω ↦ X₀ + b * (s : ℝ) + σ * B s ω) :=
    fun s ↦ ((hBmeas s).const_mul σ).const_add (X₀ + b * (s : ℝ))
  have hg_meas : ∀ s, Measurable (g s) := fun s ↦
    ((hf'c.measurable.comp (harg_meas s)).mul_const b).add
      (((hf''c.measurable.comp (harg_meas s)).mul_const (σ ^ 2)).const_mul (1 / 2))
  -- path continuity of the weight
  have harg_cont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ X₀ + b * (s : ℝ) + σ * B s ω :=
    fun ω ↦ (continuous_const.add (continuous_const.mul NNReal.continuous_coe)).add
      (continuous_const.mul (hBcont ω))
  have hg_cont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ g s ω := fun ω ↦
    ((hf'c.comp (harg_cont ω)).mul continuous_const).add
      (((hf''c.comp (harg_cont ω)).mul continuous_const).const_mul (1 / 2))
  -- boundedness: `|g| ≤ |b|·C₁ + ½·σ²·C₂`
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg'' 0)
  have hG0 : (0 : ℝ) ≤ |b| * C1 + (1 / 2) * (σ ^ 2 * C2) :=
    add_nonneg (mul_nonneg (abs_nonneg b) hC1)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (mul_nonneg (sq_nonneg σ) hC2))
  have hg_bdd : ∀ s ω, |g s ω| ≤ |b| * C1 + (1 / 2) * (σ ^ 2 * C2) := by
    intro s ω
    have h1 : |f' (X₀ + b * (s : ℝ) + σ * B s ω) * b| ≤ |b| * C1 := by
      rw [abs_mul]
      calc |f' (X₀ + b * (s : ℝ) + σ * B s ω)| * |b|
          ≤ C1 * |b| := mul_le_mul_of_nonneg_right (hg' _) (abs_nonneg b)
        _ = |b| * C1 := mul_comm _ _
    have h2 : |(1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2)|
        ≤ (1 / 2) * (σ ^ 2 * C2) := by
      have habs : |(1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2)|
          = (1 / 2) * (|f'' (X₀ + b * (s : ℝ) + σ * B s ω)| * |σ ^ 2|) := by
        rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      have hσ : |σ ^ 2| = σ ^ 2 := abs_of_nonneg (sq_nonneg σ)
      rw [habs, hσ]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hg'' _) (sq_nonneg σ)
    calc |g s ω| ≤ |f' (X₀ + b * (s : ℝ) + σ * B s ω) * b|
          + |(1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2)| :=
        by simpa only [Real.norm_eq_abs] using abs_add_le _ _
      _ ≤ |b| * C1 + (1 / 2) * (σ ^ 2 * C2) := add_le_add h1 h2
  -- `f` has linear growth from the `|f'| ≤ C₁` bound; hence `f(X_t)` is integrable
  have hf_lin : ∀ x, |f x| ≤ |f 0| + C1 * |x| := by
    intro x
    have hmv : |f x - f 0| ≤ C1 * |x| := by
      have h := abs_sub_le_of_hasDerivAt (g := f) (g' := f') hf' hg' 0 x
      simpa using h
    calc |f x| = |f 0 + (f x - f 0)| := by congr 1; ring
      _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
      _ ≤ |f 0| + C1 * |x| := by linarith
  have hB_int : ∀ t : ℝ≥0, Integrable (B t) μ :=
    fun t ↦ (memLp_eval hB t).integrable one_le_two
  have hfX_int : ∀ t : ℝ≥0, Integrable (fun ω ↦ f (X₀ + b * (t : ℝ) + σ * B t ω)) μ := by
    intro t
    have hmeas : AEStronglyMeasurable (fun ω ↦ f (X₀ + b * (t : ℝ) + σ * B t ω)) μ :=
      (hfcont.measurable.comp (harg_meas t)).aestronglyMeasurable
    have habsB : Integrable (fun ω ↦ |B t ω|) μ := by
      have h := (memLp_eval hB t).norm.integrable one_le_two
      simpa [Real.norm_eq_abs] using h
    have hdom : Integrable (fun ω ↦ (|f 0| + C1 * (|X₀| + |b| * (t : ℝ)))
        + C1 * |σ| * |B t ω|) μ :=
      (integrable_const _).add (habsB.const_mul (C1 * |σ|))
    refine Integrable.mono' hdom hmeas (Eventually.of_forall fun ω ↦ ?_)
    have harg : |X₀ + b * (t : ℝ) + σ * B t ω| ≤ |X₀| + |b| * (t : ℝ) + |σ| * |B t ω| := by
      calc |X₀ + b * (t : ℝ) + σ * B t ω| ≤ |X₀ + b * (t : ℝ)| + |σ * B t ω| :=
            abs_add_le _ _
        _ ≤ (|X₀| + |b * (t : ℝ)|) + |σ * B t ω| := by
            have := abs_add_le X₀ (b * (t : ℝ)); linarith
        _ = |X₀| + |b| * (t : ℝ) + |σ| * |B t ω| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (NNReal.coe_nonneg t)]
    calc |f (X₀ + b * (t : ℝ) + σ * B t ω)|
        ≤ |f 0| + C1 * |X₀ + b * (t : ℝ) + σ * B t ω| := hf_lin _
      _ ≤ |f 0| + C1 * (|X₀| + |b| * (t : ℝ) + |σ| * |B t ω|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left harg hC1)
      _ = (|f 0| + C1 * (|X₀| + |b| * (t : ℝ))) + C1 * |σ| * |B t ω| := by ring
  -- the Itô formula at the bounded (λ = 0) exponential-growth class
  have hgrowth : ∀ h : ℝ → ℝ, (∀ x, |h x| ≤ max C1 (max C2 C3)) →
      ∀ x, |h x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) := by
    intro h hh x
    have hz : (0 : ℝ) * |x| = 0 := zero_mul _
    rw [hz, Real.exp_zero, mul_one]
    exact hh x
  have hb1 : ∀ x, |f' x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) :=
    hgrowth f' fun x ↦ le_trans (hg' x) (le_max_left C1 (max C2 C3))
  have hb2 : ∀ x, |f'' x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) :=
    hgrowth f'' fun x ↦ le_trans (hg'' x) (le_max_of_le_right (le_max_left C2 C3))
  have hb3 : ∀ x, |f''' x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) :=
    hgrowth f''' fun x ↦ le_trans (hg''' x)
      (le_max_of_le_right (le_max_of_le_right le_rfl))
  obtain ⟨gfx, _, hId⟩ := ito_formula_itoProcess hB hBmeas hBcont T X₀ b σ hf' hf'' hf'''
    (lam := 0) (C := max C1 (max C2 C3)) (by norm_num : (0 : ℝ) ≤ 0) hb1 hb2 hb3
  -- the stochastic term is integrable (an L² element under a probability measure)
  have hsto_int : Integrable (fun ω ↦ (itoIntegralCLM_T hB T hBmeas gfx) ω) μ :=
    (Lp.memLp (itoIntegralCLM_T hB T hBmeas gfx)).integrable one_le_two
  -- the drift term is integrable (bounded path integral)
  have hdrift_int : Integrable (fun ω ↦ ∫ s in Set.Ioc 0 T, g s ω
      ∂ItoIntegralL2.timeMeasure) μ :=
    (memLp_pathIntegral_process hg_meas hg_cont hG0 hg_bdd T).integrable one_le_two
  -- integrate the a.e. identity; centering kills the stochastic term, Fubini
  -- interchanges the drift integral with the expectation
  have hfX0 : Integrable (fun ω ↦ f (X₀ + b * (0 : ℝ) + σ * B 0 ω)) μ := hfX_int 0
  have hmain : ∫ ω, f (X₀ + b * (T : ℝ) + σ * B T ω) ∂μ
      - ∫ ω, f (X₀ + b * (0 : ℝ) + σ * B 0 ω) ∂μ
      = ∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
    calc ∫ ω, f (X₀ + b * (T : ℝ) + σ * B T ω) ∂μ
          - ∫ ω, f (X₀ + b * (0 : ℝ) + σ * B 0 ω) ∂μ
        = ∫ ω, (f (X₀ + b * (T : ℝ) + σ * B T ω)
            - f (X₀ + b * (0 : ℝ) + σ * B 0 ω)) ∂μ := by
          rw [integral_sub (hfX_int T) hfX0]
      _ = ∫ ω, (itoIntegralCLM_T hB T hBmeas gfx) ω
            + ∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure ∂μ :=
          MeasureTheory.integral_congr_ae hId
      _ = ∫ ω, (itoIntegralCLM_T hB T hBmeas gfx) ω ∂μ
            + ∫ ω, (∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure) ∂μ :=
          integral_add hsto_int hdrift_int
      _ = ∫ ω, (∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure) ∂μ := by
          rw [integral_itoIntegralCLM_T hB T hBmeas gfx, zero_add]
      _ = ∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure :=
          expectation_pathIntegral_eq hg_meas hg_cont hG0 hg_bdd T
  linarith [hmain]

/-! ### Stage 2 — the bounded *adapted* coefficients (`β`, `δ` random)

The integrated Itô–drift identity for a genuine Itô process with random adapted coefficients.
The data: a pre-Brownian motion `B` (with measurable sections and continuous paths), bounded
adapted path-continuous `β, δ`, and `M` — a path-continuous adapted *version* of the Itô
integral of `δ` on `[0, T]` (`∀ t, M t =ᵐ (δ●B)_t`, the process-values of
`ItoIntegralProcessGeneral.itoProcessCLM` at the σ-realization `processToLp δ`). The process
under test is defined from the data by

  `X_t := X₀ + ∫₀ᵗ β_s ds + M_t`,

so its paths are continuous and `ΔX` over a cell splits into the drift increment plus the
martingale increment. The proof is the partition/Taylor skeleton of `ItoFormulaC2` at the
path `k ↦ X_{tₖ}` (`DiscreteIto.discrete_ito_formula` — an exact per-path identity), with the
three terms dispatched by: pathwise Riemann convergence (drift), the stack's weighted
quadratic variation at the adapted weight `f''(X)·δ²` plus an `L¹` cell-correction
(martingale-square), and a cubic-moment bound (Taylor remainder). Taking expectations turns
the pathwise identity into the integrated one; the drift integral crosses the expectation by
the stage-1 Fubini lemma `expectation_pathIntegral_eq`.

The per-cell moment facts (`E[(M_v−M_u)²]`, `E[(M_v−M_u)(B_v−B_u)]`) come from the
martingale property of `M` (inherited a.e. from `itoProcessCLM`), the time-indexed Itô
isometry `itoProcessCLM_norm_sq`, and the terminal cross-isometry `crossTerminal_isometry`
(polarization of `itoIntegralCLM_T_norm`) — no pathwise statement about `(δ●B)_t` is needed,
so the modification a.e.-friction never enters. -/

section Adapted

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

/-- `E[g²] = ‖g‖²_{L²}` for the coe of an `Lp ℝ 2` element (real `L²`). -/
private theorem sqIntegral_of_Lp {ν : Measure Ω} (g : Lp ℝ 2 ν) :
    ∫ ω, g ω ^ 2 ∂ν = ‖g‖ ^ 2 := (lp_two_norm_sq g).symm

/-- **Expansion of the squared sum under the integral** (all three integrands integrable):
`E[(a+b)²] = E[a²] + 2·E[a·b] + E[b²]`. -/
private theorem integral_sq_add {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}
    {a b : α → ℝ}
    (ha2 : Integrable (fun ω ↦ a ω ^ 2) ν) (hb2 : Integrable (fun ω ↦ b ω ^ 2) ν)
    (hab : Integrable (fun ω ↦ a ω * b ω) ν) :
    ∫ ω, (a ω + b ω) ^ 2 ∂ν
      = ∫ ω, a ω ^ 2 ∂ν + 2 * ∫ ω, a ω * b ω ∂ν + ∫ ω, b ω ^ 2 ∂ν := by
  have hpt : (fun ω ↦ (a ω + b ω) ^ 2) = fun ω ↦ a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2 := by
    funext ω; ring
  have hpt : (fun ω ↦ (a ω + b ω) ^ 2) = fun ω ↦ a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2 := by
    funext ω; ring
  rw [hpt]
  have h1 : ∫ ω, (a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2) ∂ν
      = ∫ ω, (a ω ^ 2 + 2 * (a ω * b ω)) ∂ν + ∫ ω, b ω ^ 2 ∂ν :=
    integral_add (by exact (ha2.add (hab.const_mul 2))) hb2
  have h2 : ∫ ω, (a ω ^ 2 + 2 * (a ω * b ω)) ∂ν
      = ∫ ω, a ω ^ 2 ∂ν + 2 * ∫ ω, a ω * b ω ∂ν := by
    rw [integral_add ha2 (hab.const_mul 2), integral_const_mul]
  rw [h1, h2]

set_option maxHeartbeats 1000000 in
/-- **The terminal cross-isometry** (polarization of the terminal Itô isometry): the `L²`
pairing of two predictable integrands equals the expectation of the product of their Itô
integrals, `𝔼[(∫₀ᵀ p dB)·(∫₀ᵀ q dB)] = ⟨p, q⟩_{L²(trim)}`. Route: the Itô integral is
linear, so `I(p+q)² = (Ip + Iq)²` a.e.; expanding that square under the expectation and the
`L²` norm `‖p+q‖²` under the integral, and matching the two against the isometry
`itoIntegralCLM_T_norm`, pins the cross term. -/
private theorem crossTerminal_isometry (p q : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∫ ω, itoIntegralCLM_T hB T hBmeas p ω * itoIntegralCLM_T hB T hBmeas q ω ∂μ
      = ∫ z, (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  have hpair : Integrable (fun z : ℝ≥0 × Ω ↦ (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp p).integrable_mul (Lp.memLp q)
  -- the terminal isometry read as an integral identity, at `r` and at `p + q`
  have hI2 : ∀ r : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ∫ ω, itoIntegralCLM_T hB T hBmeas r ω ^ 2 ∂μ = ‖r‖ ^ 2 := by
    intro r
    rw [sqIntegral_of_Lp (itoIntegralCLM_T hB T hBmeas r),
      itoIntegralCLM_T_norm hB T hBmeas r]
  -- `I(p+q)` = `I p + I q` a.e. (linearity of the Itô integral as an Lp map)
  have haddae : (fun ω ↦ itoIntegralCLM_T hB T hBmeas (p + q) ω)
      =ᵐ[μ] (fun ω ↦ itoIntegralCLM_T hB T hBmeas p ω + itoIntegralCLM_T hB T hBmeas q ω) := by
    filter_upwards [Lp.coeFn_add (itoIntegralCLM_T hB T hBmeas p)
      (itoIntegralCLM_T hB T hBmeas q)] with ω hω
    have h1 : itoIntegralCLM_T hB T hBmeas (p + q) ω
        = (itoIntegralCLM_T hB T hBmeas p
            + itoIntegralCLM_T hB T hBmeas q : Lp ℝ 2 μ) ω := by
      rw [map_add]
    rw [h1, hω]
    simp only [Pi.add_apply]
  -- expansion A: the expectation side
  have hEexpand : ∫ ω, (itoIntegralCLM_T hB T hBmeas p ω
        + itoIntegralCLM_T hB T hBmeas q ω) ^ 2 ∂μ
      = ∫ ω, itoIntegralCLM_T hB T hBmeas p ω ^ 2 ∂μ
        + 2 * ∫ ω, itoIntegralCLM_T hB T hBmeas p ω * itoIntegralCLM_T hB T hBmeas q ω ∂μ
        + ∫ ω, itoIntegralCLM_T hB T hBmeas q ω ^ 2 ∂μ :=
    integral_sq_add (a := fun ω ↦ itoIntegralCLM_T hB T hBmeas p ω)
      (b := fun ω ↦ itoIntegralCLM_T hB T hBmeas q ω)
      (Lp.memLp _).integrable_sq (Lp.memLp _).integrable_sq
      ((Lp.memLp (itoIntegralCLM_T hB T hBmeas p)).integrable_mul
        (Lp.memLp (itoIntegralCLM_T hB T hBmeas q)))
  -- expansion B: the norm side
  have hNexpand : ‖p + q‖ ^ 2
      = ∫ z, (p : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        + 2 * ∫ z, (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z, (q : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have hsquare : (fun z : ℝ≥0 × Ω ↦ (p : ℝ≥0 × Ω → ℝ) z + (q : ℝ≥0 × Ω → ℝ) z) ^ 2
        = fun z ↦ (p : ℝ≥0 × Ω → ℝ) z ^ 2 + 2 * (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z
            + (q : ℝ≥0 × Ω → ℝ) z ^ 2 := by
      funext z
      simp only [Pi.pow_apply]
      ring
    have hsqae : (fun z : ℝ≥0 × Ω ↦
          ((p + q : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
          (fun z : ℝ≥0 × Ω ↦
            ((fun z : ℝ≥0 × Ω ↦ (p : ℝ≥0 × Ω → ℝ) z + (q : ℝ≥0 × Ω → ℝ) z) z) ^ 2) := by
      filter_upwards [Lp.coeFn_add p q] with z hz
      simp only [hz, Pi.add_apply]
    calc ‖p + q‖ ^ 2
        = ∫ z, ((p + q : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := lp_two_norm_sq _
      _ = ∫ z, ((fun z : ℝ≥0 × Ω ↦ (p : ℝ≥0 × Ω → ℝ) z + (q : ℝ≥0 × Ω → ℝ) z) z) ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := integral_congr_ae hsqae
      _ = ∫ z, (p : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
            + 2 * ∫ z, (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z
                ∂(trimMeasure_T (μ := μ) T hBmeas)
            + ∫ z, (q : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) :=
            integral_sq_add (a := fun z ↦ (p : ℝ≥0 × Ω → ℝ) z)
              (b := fun z ↦ (q : ℝ≥0 × Ω → ℝ) z)
              (Lp.memLp p).integrable_sq (Lp.memLp q).integrable_sq hpair
  -- match: `E[(Ip + Iq)²] = ‖p+q‖²` through the two expansions
  have hEnorm : ∫ ω, itoIntegralCLM_T hB T hBmeas p ω ^ 2 ∂μ
      + 2 * ∫ ω, itoIntegralCLM_T hB T hBmeas p ω * itoIntegralCLM_T hB T hBmeas q ω ∂μ
      + ∫ ω, itoIntegralCLM_T hB T hBmeas q ω ^ 2 ∂μ
      = ∫ z, (p : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        + 2 * ∫ z, (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z, (q : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    calc ∫ ω, itoIntegralCLM_T hB T hBmeas p ω ^ 2 ∂μ
        + 2 * ∫ ω, itoIntegralCLM_T hB T hBmeas p ω * itoIntegralCLM_T hB T hBmeas q ω ∂μ
        + ∫ ω, itoIntegralCLM_T hB T hBmeas q ω ^ 2 ∂μ
        = ∫ ω, (itoIntegralCLM_T hB T hBmeas p ω
            + itoIntegralCLM_T hB T hBmeas q ω) ^ 2 ∂μ := hEexpand.symm
      _ = ∫ ω, itoIntegralCLM_T hB T hBmeas (p + q) ω ^ 2 ∂μ := by
          have hsq : (fun ω ↦ (itoIntegralCLM_T hB T hBmeas p ω
                + itoIntegralCLM_T hB T hBmeas q ω) ^ 2)
              =ᵐ[μ] (fun ω ↦ itoIntegralCLM_T hB T hBmeas (p + q) ω ^ 2) := by
            filter_upwards [haddae] with ω hω
            show (itoIntegralCLM_T hB T hBmeas p ω + itoIntegralCLM_T hB T hBmeas q ω) ^ 2
                = itoIntegralCLM_T hB T hBmeas (p + q) ω ^ 2
            rw [hω]
          exact integral_congr_ae hsq
      _ = ‖p + q‖ ^ 2 := hI2 (p + q)
      _ = ∫ z, (p : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
            + 2 * ∫ z, (p : ℝ≥0 × Ω → ℝ) z * (q : ℝ≥0 × Ω → ℝ) z
                ∂(trimMeasure_T (μ := μ) T hBmeas)
            + ∫ z, (q : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          hNexpand
  -- the four isometries collapse the squares, leaving the cross terms equal
  have hEp : ∫ ω, itoIntegralCLM_T hB T hBmeas p ω ^ 2 ∂μ = ‖p‖ ^ 2 := hI2 p
  have hEq : ∫ ω, itoIntegralCLM_T hB T hBmeas q ω ^ 2 ∂μ = ‖q‖ ^ 2 := hI2 q
  have hEpq : ∫ z, (p : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) = ‖p‖ ^ 2 :=
    (lp_two_norm_sq p).symm
  have hEqq : ∫ z, (q : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) = ‖q‖ ^ 2 :=
    (lp_two_norm_sq q).symm
  rw [hEp, hEq, hEpq, hEqq] at hEnorm
  linarith [hEnorm]

/-- **The band-slice conversion**: for a bounded adapted path-continuous `ψ`, the
`(u,v]`-band integral of its uncurried form over the predictable trim measure equals the
plain slice integral `∫_u^v 𝔼[ψ_s] ds`. Route: predictability of `(s,ω) ↦ ψ s ω`
(`isStronglyPredictable_of_bdd_adapted_cont`) drops the trim (`integral_trim`), the band
restriction moves to the time coordinate (`Measure.restrict_prod_eq_prod_univ` +
`Measure.restrict_restrict`), and the product integral Fubini-factors (`integral_prod`). -/
private theorem bandIntegral_slice (ψ : ℝ≥0 → Ω → ℝ)
    (hψadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (ψ t))
    (hψcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ ψ s ω)
    {Cψ : ℝ} (hψbdd : ∀ s ω, |ψ s ω| ≤ Cψ)
    (u v : ℝ≥0) (hvT : v ≤ T) :
    ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ s in Set.Ioc u v, (∫ ω, ψ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  have hpred : IsStronglyPredictable (natFiltration hBmeas) ψ :=
    isStronglyPredictable_of_bdd_adapted_cont hBmeas hψadap hψcont
  have hband : MeasurableSet[(natFiltration hBmeas).predictable]
      (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ
  -- measurability/integrability of the band-indicatored integrand
  have hsm : StronglyMeasurable[(natFiltration hBmeas).predictable]
      ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ)) :=
    (show StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry ψ) from
      hpred).indicator hband
  have hint : Integrable (Function.uncurry ψ) (trimMeasure_T (μ := μ) T hBmeas) :=
    (MemLp.of_bound hpred.aestronglyMeasurable Cψ
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hψbdd z.1 z.2)).integrable one_le_two
  have hUVamb : MeasurableSet (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  haveI : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator
      (Function.uncurry ψ)) ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) :=
    ⟨_, StronglyMeasurable.mono hsm (natFiltration hBmeas).predictable_le_prod,
      Eventually.of_forall fun _ ↦ rfl⟩
  have hint' : Integrable ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ))
      ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) := by
    refine Integrable.of_bound haesm (max Cψ 0) ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
    · rw [Set.indicator_of_mem hz]
      exact le_trans (hψbdd z.1 z.2) (le_max_left Cψ 0)
    · rw [Set.indicator_of_notMem hz]
      simp
  calc ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
        (integral_indicator (μ := trimMeasure_T (μ := μ) T hBmeas)
          (f := Function.uncurry ψ) hband).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(((timeMeasure_T T).prod μ).trim
            (natFiltration hBmeas).predictable_le_prod) := rfl
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((timeMeasure_T T).prod μ) :=
        (integral_trim (natFiltration hBmeas).predictable_le_prod hsm).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((ItoIntegralL2.timeMeasure.prod μ).restrict (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))) := by
        rw [show (((timeMeasure_T T).prod μ : Measure (ℝ≥0 × Ω))
            = (ItoIntegralL2.timeMeasure.prod μ).restrict
              (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))) from by
          rw [timeMeasure_T, Measure.restrict_prod_eq_prod_univ]]
    _ = ∫ z, (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator
          ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ)) z
          ∂(ItoIntegralL2.timeMeasure.prod μ) :=
        (integral_indicator (MeasurableSet.prod measurableSet_Ioc
          MeasurableSet.univ)).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(ItoIntegralL2.timeMeasure.prod μ) := by
        have hsub : (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
            ⊆ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) := by
          rintro z hz
          exact ⟨⟨lt_of_le_of_lt (NNReal.coe_nonneg _) hz.1.1, le_trans hz.1.2 hvT⟩, hz.2⟩
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        by_cases hz : z ∈ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        · rw [Set.indicator_of_mem (hsub hz), Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          by_cases hz2 : z ∈ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          · rw [Set.indicator_of_mem hz2, Set.indicator_of_notMem hz]
          · rw [Set.indicator_of_notMem hz2]
    _ = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
          ∂(ItoIntegralL2.timeMeasure.prod μ) := integral_indicator hUVamb
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) := by
        haveI : SFinite ItoIntegralL2.timeMeasure := inferInstance
        have hmeas : ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ)
            = (ItoIntegralL2.timeMeasure.prod μ).restrict
              (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) := by
          rw [Measure.restrict_prod_eq_prod_univ]
        rw [hmeas, integral_indicator hUVamb,
          Measure.restrict_restrict_of_subset
            (Set.Subset.refl (Set.Ioc u v ×ˢ (Set.univ : Set Ω)))]
    _ = ∫ s, (∫ ω, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) ∂μ)
          ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
        integral_prod _ hint'
    _ = ∫ s in Set.Ioc u v, (∫ ω, ψ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs ↦ ?_)
        have hslice : ∀ ω' : Ω, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator
            (Function.uncurry ψ) (s, ω') = ψ s ω' := by
          intro ω'
          rw [Set.indicator_of_mem
            (Set.mem_prod.mpr ⟨hs, Set.mem_univ ω'⟩)]
          rfl
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
          show (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) = _
          rw [hslice ω])

/-! ### Stages 3–5 — the weighted increment isometry, the third-moment bound, and the
assembly of the adapted drift identity

The data (per the designed route): a pre-Brownian `B` with measurable sections; bounded
adapted path-continuous `β, δ`; and `M` — a path-continuous strongly-adapted *version* of
the Itô integral of `δ` on `[0,T]` (`M t =ᵐ (δ●B)_t`, the CLM process values of the
σ-realization `processToLp δ`). The Itô process under test is *defined* (not hypothesized)
by `X t ω := X₀ + ∫₀ᵗ β_s ds + M t ω`, so its paths are continuous by construction.

* `driftPath` / `itoProcX` — the data section: path continuity, strong adaptedness and
  `L²`-boundedness of the constructed process;
* `integral_mul_condExp_eq` — the expectation pull-out `𝔼[h · g] = 𝔼[h · 𝔼[g | 𝓕]]`;
* `incrementEnergy` — the unweighted increment isometry `𝔼[(M_v − M_u)²] = ∫_{(u,v]} δ² d(trim)`
  (`= ∫_u^v 𝔼[δ_s²] ds`), by the martingale pull-out `𝔼[M_u M_v] = 𝔼[M_u²]` plus the
  time-indexed isometry `itoProcessCLM_norm_sq` and the stage-2 `bandIntegral_slice`. No
  pathwise statement about the modification `M` is used anywhere — only its a.e. agreement
  with the CLM process, which makes the whole stage-3/4/5 build immune to the
  version-selection friction. -/

end Adapted

section AdaptedData

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The pathwise drift integral splits over the time scale: `∫₀^v = ∫₀^u + ∫_{(u,v]}`
for `u ≤ v` (`timeMeasure`-form; `(0,u]` and `(u,v]` are exactly disjoint). -/
theorem driftPath_add {β : ℝ≥0 → Ω → ℝ} (hbcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hbdd : ∀ s ω, |β s ω| ≤ Db) {u v : ℝ≥0} (huv : u ≤ v) (ω : Ω) :
    (∫ s in Set.Ioc 0 v, β s ω ∂ItoIntegralL2.timeMeasure)
      = ∫ s in Set.Ioc 0 u, β s ω ∂ItoIntegralL2.timeMeasure
        + ∫ s in Set.Ioc u v, β s ω ∂ItoIntegralL2.timeMeasure := by
  have hβm : Measurable (fun s : ℝ≥0 ↦ β s ω) := hbcont ω |>.measurable
  have hintOf : ∀ w : Set ℝ≥0, IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict w) →
      IntegrableOn (fun s : ℝ≥0 ↦ β s ω) w ItoIntegralL2.timeMeasure := by
    intro w _
    refine Integrable.of_bound
      (μ := ItoIntegralL2.timeMeasure.restrict w)
      ⟨fun z : ℝ≥0 ↦ β z ω, hβm.stronglyMeasurable,
        Eventually.of_forall fun _ ↦ rfl⟩ Db ?_
    exact Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs] using hbdd z ω
  haveI hfin0 : IsFiniteMeasure
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 u)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  haveI hfinv : IsFiniteMeasure
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hint0 : IntegrableOn (fun s : ℝ≥0 ↦ β s ω) (Set.Ioc 0 u)
      ItoIntegralL2.timeMeasure := hintOf _ hfin0
  have hintv : IntegrableOn (fun s : ℝ≥0 ↦ β s ω) (Set.Ioc u v)
      ItoIntegralL2.timeMeasure := hintOf _ hfinv
  have hunion : Set.Ioc 0 u ∪ Set.Ioc u v = Set.Ioc 0 v :=
    Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ≥0) ≤ u) huv
  rw [← hunion]
  exact setIntegral_union
    (Set.disjoint_left.2 fun a ha hb ↦ by
      have h1 : (u : ℝ) < (a : ℝ) := by exact_mod_cast hb.1
      have h2 : (a : ℝ) ≤ (u : ℝ) := by exact_mod_cast ha.2
      linarith) measurableSet_Ioc hint0 hintv

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The pathwise drift integral is **Lipschitz in `t`, uniformly in `ω`**, with constant
the `β`-bound: `|∫₀^v β − ∫₀^u β| ≤ D_β·|v − u|`. The cell increments of the drift block
are `O(mesh)`. -/
theorem abs_driftPath_sub_le {β : ℝ≥0 → Ω → ℝ} (hbcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hbdd : ∀ s ω, |β s ω| ≤ Db) (u v : ℝ≥0) (ω : Ω) :
    |(∫ s in Set.Ioc 0 v, β s ω ∂ItoIntegralL2.timeMeasure)
      - ∫ s in Set.Ioc 0 u, β s ω ∂ItoIntegralL2.timeMeasure| ≤ Db * |(v : ℝ) - u| := by
  have hβm : Measurable (fun s : ℝ≥0 ↦ β s ω) := hbcont ω |>.measurable
  -- bound of the indicator integral of `β` over a cell `(a,b]` by `D_β·(b−a)`
  have hcell : ∀ a b : ℝ≥0, a ≤ b →
      |∫ z, (Set.Ioc a b).indicator (fun s : ℝ≥0 ↦ β s ω) z
      ∂ItoIntegralL2.timeMeasure| ≤ Db * ((b : ℝ) - a) := by
    intro a b hab
    have hint1 : Integrable ((Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ))
        ItoIntegralL2.timeMeasure := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (hs := ne_of_lt (by
        rw [ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top))
    have hintB : Integrable (fun z : ℝ≥0 ↦
        Db * (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) z) ItoIntegralL2.timeMeasure :=
      hint1.const_mul Db
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    refine le_trans (integral_mono_of_nonneg
      (Eventually.of_forall fun z ↦ abs_nonneg _) hintB ?_) ?_
    · filter_upwards with z
      by_cases hz : z ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        simpa using hbdd z ω
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; norm_num
    · rw [integral_const_mul, integral_indicator_one measurableSet_Ioc, measureReal_def,
        ItoIntegralL2.timeMeasure_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (by linarith [NNReal.coe_le_coe.mpr hab]))]
  rcases le_total u v with huv | hvu
  · rw [driftPath_add hbcont hbdd huv ω, add_sub_cancel_left, ← integral_indicator
      (μ := ItoIntegralL2.timeMeasure) (f := fun s : ℝ≥0 ↦ β s ω) measurableSet_Ioc,
      abs_of_nonneg (show (0 : ℝ) ≤ (v : ℝ) - (u : ℝ) by
        linarith [NNReal.coe_le_coe.mp huv])]
    exact hcell u v huv
  · have hsub : (∫ s in Set.Ioc 0 v, β s ω ∂ItoIntegralL2.timeMeasure)
        - ∫ s in Set.Ioc 0 u, β s ω ∂ItoIntegralL2.timeMeasure
        = -(∫ s in Set.Ioc v u, β s ω ∂ItoIntegralL2.timeMeasure) := by
      rw [driftPath_add hbcont hbdd hvu ω]; ring
    rw [hsub, abs_neg, ← integral_indicator
      (μ := ItoIntegralL2.timeMeasure) (f := fun s : ℝ≥0 ↦ β s ω) measurableSet_Ioc,
      abs_of_nonpos (show (v : ℝ) - (u : ℝ) ≤ 0 by
        linarith [NNReal.coe_le_coe.mp hvu])]
    exact (hcell v u hvu).trans (by rw [neg_sub])

/-! #### Stage 3 foundations — the expectation pull-out and the increment-energy law -/

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **Expectation pull-out across a sub-σ-algebra** (the tower step): an `𝓕`-measurable
factor crosses the conditional expectation, `𝔼[h·g] = 𝔼[h·𝔼[g | 𝓕]]`. -/
theorem integral_mul_condExp_eq {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ)
    {h g : Ω → ℝ} (hh : StronglyMeasurable[𝓕] h) (hgh : Integrable (h * g) μ)
    (hg : Integrable g μ) :
    ∫ ω, h ω * g ω ∂μ = ∫ ω, h ω * μ[g | 𝓕] ω ∂μ := by
  calc ∫ ω, h ω * g ω ∂μ
      = ∫ ω, μ[h * g | 𝓕] ω ∂μ := (integral_condExp h𝓕).symm
    _ = ∫ ω, h ω * μ[g | 𝓕] ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hh hgh hg)

omit hMadap in
/-- The Itô-integral process `M` is square-integrable at every time (its values are
a.e.-equal to `L²` CLM values). -/
theorem memLp_M (t : ℝ≥0) : MemLp (M t) 2 μ := by
  have h := Lp.memLp (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd))
  refine ⟨h.1.congr (hMeq t).symm, ?_⟩
  rw [eLpNorm_congr_ae (hMeq t)]
  exact h.2

/-- **The increment-energy law** (the unweighted half of stage 3): for `u ≤ v ≤ T`,

  `𝔼[(M_v − M_u)²] = ∫_u^v 𝔼[δ_s²] ds`,

the energy of the Itô-integral increment over a time band is the predictable energy
of the band. Route: expand the square under the expectation and kill the cross term
by the martingale pull-out `𝔼[M_u M_v] = 𝔼[M_u²]` (the Itô integral is an
`𝓕_u`-martingale and `M_u` is `𝓕_u`-measurable), read the two second moments as
band energies by the time-indexed isometry `itoProcessCLM_norm_sq`, split the nested
bands `(0,u]` ⊔ `(u,v]` = `(0,v]`, and convert the band to the slice integral by the
stage-2 `bandIntegral_slice`. No pathwise statement about the modification `M` is
used anywhere — only its a.e. agreement with the CLM process. -/
theorem incrementEnergy {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
      = ∫ s in Set.Ioc u v, (∫ ω, δ s ω * δ s ω ∂μ)
          ∂ItoIntegralL2.timeMeasure := by
  set φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    processToLp T hBmeas hδadap hδcont hδbdd with hφdef
  -- the martingale congruence `μ[M v | 𝓕_u] =ᵐ M u`
  have hmart : μ[M v | natFiltration hBmeas u] =ᵐ[μ] M u :=
    condExp_congr_ae (hMeq v) |>.trans
      ((itoIntegralProcessGen_isMartingale hB T hBmeas φ huv).trans (hMeq u).symm)
  -- the cross-term pull-out: `E[M_u M_v] = E[M_u²]`
  have hMM : ∫ ω, M u ω * M v ω ∂μ = ∫ ω, M u ω ^ 2 ∂μ := by
    have hprod : Integrable (fun ω ↦ M u ω * M v ω) μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable_mul
        (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v)
    have hcond : μ[(fun ω ↦ M u ω * M v ω) | natFiltration hBmeas u]
        =ᵐ[μ] (fun ω ↦ M u ω * μ[M v | natFiltration hBmeas u] ω) :=
      condExp_mul_of_stronglyMeasurable_left (hMadap u) hprod
        ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).integrable one_le_two)
    have hle : (natFiltration hBmeas u) ≤ mΩ := (natFiltration hBmeas).le u
    calc ∫ ω, M u ω * M v ω ∂μ
        = ∫ ω, μ[(fun ω ↦ M u ω * M v ω) | natFiltration hBmeas u] ω ∂μ :=
          (integral_condExp hle).symm
      _ = ∫ ω, M u ω * M u ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hcond, hmart] with ω hω hm
          rw [hω, hm]
      _ = ∫ ω, M u ω ^ 2 ∂μ := by
          exact integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  -- second moment as band energy of the σ-realization (coe form)
  have hM2 : ∀ t : ℝ≥0, t ≤ T → ∫ ω, M t ω ^ 2 ∂μ
      = ∫ z in Set.Ioc (0:ℝ≥0) t ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro t htT
    calc ∫ ω, M t ω ^ 2 ∂μ
        = ∫ ω, (itoProcessCLM hB T t hBmeas φ : Ω → ℝ) ω ^ 2 ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hMeq t] with ω hω
          rw [hω, hφdef]
      _ = ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 := sqIntegral_of_Lp _
      _ = ∫ z in Set.Ioc (0:ℝ≥0) t ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := itoProcessCLM_norm_sq hB htT hBmeas φ
  -- the nested-band split of the band energies
  have hbandv := hM2 v hvT
  have hbandu := hM2 u (le_trans huv hvT)
  have hdisj : Disjoint
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) :=
    Set.disjoint_left.2 fun a ha hb ↦ by
      have h1 : (u : ℝ) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
      have h2 : (a.1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast ha.1.2
      linarith
  have hint : Integrable (fun z : ℝ≥0 × Ω ↦ (φ : ℝ≥0 × Ω → ℝ) z ^ 2)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp φ).integrable_sq
  have hintUU : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hintUV : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hbandsplit : ∫ z in Set.Ioc (0:ℝ≥0) v ×ˢ (Set.univ : Set Ω),
      (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω),
          (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω),
          (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have hprod0 : (Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω))
        ∪ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        = (Set.Ioc (0:ℝ≥0) v) ×ˢ (Set.univ : Set Ω) := by
      rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ≥0) ≤ u) huv]
    rw [← hprod0]
    exact setIntegral_union hdisj
      (MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ)
      hintUU hintUV
  -- the band-to-slice conversion (stage-2 `bandIntegral_slice` at `δ²`)
  have hbandδ : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ s in Set.Ioc a b, (∫ ω, δ s ω * δ s ω ∂μ)
            ∂ItoIntegralL2.timeMeasure := by
    intro a b hab hbT
    have hcoe : ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω),
        (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω),
            Function.uncurry (fun s ω ↦ δ s ω * δ s ω) z
            ∂(trimMeasure_T (μ := μ) T hBmeas) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae
        (processToLp_coeFn T hBmeas hδadap hδcont hδbdd)] with z hz
      show (φ : ℝ≥0 × Ω → ℝ) z ^ 2 = Function.uncurry (fun s ω ↦ δ s ω * δ s ω) z
      rw [hz, pow_two]
      rfl
    rw [hcoe, bandIntegral_slice hBmeas (μ := μ)
      (ψ := fun (t : ℝ≥0) (ω : Ω) ↦ δ t ω * δ t ω)
      (hψadap := fun t ↦ (hδadap t).mul (hδadap t))
      (hψcont := fun ω ↦ (hδcont ω).mul (hδcont ω))
      (hψbdd := fun s ω ↦ by
        rw [abs_mul]
        calc |δ s ω| * |δ s ω| ≤ Dd * |δ s ω| :=
              mul_le_mul_of_nonneg_right (hδbdd s ω) (abs_nonneg _)
          _ ≤ Dd * Dd := mul_le_mul_of_nonneg_left (hδbdd s ω)
              (le_trans (abs_nonneg _) (hδbdd 0 ω)))
      a b hbT]
  -- expansion of the squared increment under the expectation
  have hprod : Integrable (fun ω ↦ M u ω * M v ω) μ :=
    (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable_mul
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v)
  have hsplit : ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
      = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := by
    have hint1 : Integrable (fun ω ↦ M v ω ^ 2) μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).integrable_sq
    have hint2 : Integrable (fun ω ↦ M u ω ^ 2) μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable_sq
    have hA : Integrable (fun ω ↦ M v ω ^ 2 - 2 * (M u ω * M v ω)) μ :=
      hint1.sub (hprod.const_mul 2)
    have hstep : ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2) ∂μ
        = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := by
      calc ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2) ∂μ
          = ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω)) ∂μ + ∫ ω, M u ω ^ 2 ∂μ :=
            integral_add hA hint2
        _ = (∫ ω, M v ω ^ 2 ∂μ - ∫ ω, 2 * (M u ω * M v ω) ∂μ) + ∫ ω, M u ω ^ 2 ∂μ :=
            by rw [integral_sub hint1 (hprod.const_mul 2)]
        _ = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := by
            rw [integral_const_mul, hMM]
            ring
    calc ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
        = ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
          show (M v ω - M u ω) ^ 2 = M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2
          ring
      _ = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := hstep
  rw [hsplit, hbandv, hbandu, hbandsplit,
    hbandδ (0:ℝ≥0) u (by norm_num : (0:ℝ≥0) ≤ u) (le_trans huv hvT),
    hbandδ u v huv hvT]
  ring

/-! #### Stage 3 — the weighted increment isometry via left-endpoint step approximants

The designed route: for the left-endpoint step approximant `δⁿ` of `δ` on the uniform
partition, the per-cell increment of the approximant integral is the single-rectangle
integral `δ(tₖ)·ΔBₖ`, so the weighted second-moment identity is independence algebra
(`integral_adapted_mul_increment_sq`); the passage `n → ∞` is the `L²`-contraction
of the Itô isometry plus `‖δ − δⁿ‖_{L²(trim)} → 0`. The convergence
`deltaStepLp_tendsto` needs no new analytic work: the terminal Itô isometry is an
isometry, so it transfers the Riemann bridge's `L²` convergence of the Itô sums
(`itoIntegralCLM_T_of_bdd_adapted_cont`) to the integrand classes. -/

open ItoIntegralRiemannBridge

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `n`-th left-endpoint step approximant of the integrand `δ`, as an element of
the Itô-integrand space (the `simpleAssembly_T` embedding of `stepσ n`). -/
noncomputable def deltaStepLp (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) (n : ℕ) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)

omit hB hMadap hMeq in
omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **`L²`-convergence of the step approximants**: `‖δⁿ − δ‖_{L²(trim)} → 0`. The
terminal Itô isometry `itoIntegralCLM_T_norm` is an isometry, so the norm of the
integrand difference equals the norm of the difference of the Itô sums — the
Riemann bridge's `L²` convergence (`itoIntegralCLM_T_of_bdd_adapted_cont`), with the
step-integrand sum identified with the Riemann sum by `itoIntegralCLM_T_stepσ`. -/
theorem deltaStepLp_tendsto (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) :
    Tendsto (fun n : ℕ ↦ (deltaStepLp hBmeas hδadap hδbdd n :
        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))) atTop
      (𝓝 (processToLp T hBmeas hδadap hδcont hδbdd)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hiso : ∀ ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ‖ψ‖ = ‖itoIntegralCLM_T hB T hBmeas ψ‖ := fun ψ ↦
    (itoIntegralCLM_T_norm hB T hBmeas ψ).symm
  have hstep : ∀ n : ℕ, itoIntegralCLM_T hB T hBmeas (deltaStepLp hBmeas hδadap hδbdd n)
      = (memLp_riemannσ hB hBmeas hδadap hδbdd T n).toLp (riemannσ δ T n) :=
    fun n ↦ itoIntegralCLM_T_stepσ hB hBmeas hδadap hδbdd T n
  have key : ∀ n : ℕ,
      ‖(deltaStepLp hBmeas hδadap hδbdd n
          - processToLp T hBmeas hδadap hδcont hδbdd : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
      = ‖((memLp_riemannσ hB hBmeas hδadap hδbdd T n).toLp (riemannσ δ T n)
          - itoIntegralCLM_T hB T hBmeas (processToLp T hBmeas hδadap hδcont hδbdd) :
            Lp ℝ 2 μ)‖ := by
    intro n
    rw [hiso _]
    congr 1
    rw [map_sub, hstep n]
  have hbridge := itoIntegralCLM_T_of_bdd_adapted_cont hB hBmeas hδadap hδcont hδbdd T
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbridge ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hN' := hN n hn
  rw [dist_eq_norm] at hN'
  rw [key n, dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact hN' 

end AdaptedData

/-! #### Stage 4 — the weighted increment isometry (per-cell step identification, the
`L¹` gap decay, and the summed isometry)

The route (per the dispatch-3 design): for the left-endpoint step approximant `δⁿ` of `δ`
on the uniform partition, the per-cell increment of the approximant process is the single
rectangle `δ(tₖ)·ΔBₖ` (min-algebra on `itoSimpleProcess_apply`), so the weighted
second-moment identity on the approximant is the independence isometry kernel
`integral_adapted_mul_increment_sq` at `χ = wₖ·δ(tₖ)²`; the true increment decomposes as
`ΔMₖ = δ(tₖ)ΔBₖ + δεₖ` with `δεₖ` the band-restricted CLM increment of the integrand
error `φ − δⁿ`, whose `L²` norm is exactly the cell band energy (`clm_band_energy`),
and Cauchy–Schwarz pairs each cell band with the cell energy. Summing kills the gap at
rate `√T·‖δ − δⁿ‖_{L²(trim)} → 0` (`deltaStepLp_tendsto`). -/

section StageFour

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Real `L²` pairing bound: `∫ |f g| ≤ ‖f‖₂·‖g‖₂` (Hölder at exponents `2, 2`). -/
private theorem integral_abs_mul_le_L2L2 {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, |f ω * g ω| ∂μ
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf' : MemLp |f| (ENNReal.ofReal 2) μ := by simpa using hf.abs
  have hg' : MemLp |g| (ENNReal.ofReal 2) μ := by simpa using hg.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hp
    (f := fun ω ↦ |f ω|) (g := fun ω ↦ |g ω|)
    (ae_of_all μ fun ω ↦ abs_nonneg _) (ae_of_all μ fun ω ↦ abs_nonneg _)
    hf' hg'
  have h2f : ∫ a, |f a| ^ (2 : ℝ) ∂μ = ∫ a, f a ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    show |f a| ^ (2 : ℝ) = f a ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have h2g : ∫ a, |g a| ^ (2 : ℝ) ∂μ = ∫ a, g a ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    show |g a| ^ (2 : ℝ) = g a ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h2f, h2g] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hfin : ∫ a, |f a| * |g a| ∂μ = ∫ a, |f a * g a| ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    show |f a| * |g a| = |f a * g a|
    rw [abs_mul]
  rw [hfin] at h
  exact h

/-- The process-level elementary Itô integral is additive over finite sums of simple
processes (the `itoSimpleProcess` analogue of `ItoIntegralBrownian.itoSimple_sum`). -/
private lemma itoSimpleProcess_finsetSum {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {ι' : Type*} (s : Finset ι') (V : ι' → SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (∑ i ∈ s, V i) t = ∑ i ∈ s, itoSimpleProcess hBmeas (V i) t := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimpleProcess]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimpleProcess_add, ih]

/-- A single bounded adapted step evaluated at an arbitrary time is the coefficient times
the truncated increment. -/
private lemma itoSimpleProcess_stepSP_apply {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {T a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[natFiltration hBmeas a] φ) {Mφ : ℝ} (hφM : ∀ ω, |φ ω| ≤ Mφ)
    (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas (stepSP hBmeas hab hbT hφ hφM).val t ω
      = φ ω * (B (min b t) ω - B (min a t) ω) := by
  rw [itoSimpleProcess_apply]
  show (Finsupp.single (a, b) φ).sum (fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω)) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- **Per-cell step identification** (min-algebra): over cell `k` of the uniform partition,
the `n`-step left-endpoint step process increments by exactly the single rectangle
`δ(tₖ)·(B_{tₖ₊₁} − B_{tₖ})` — every other cell telescopes to zero and the diagonal cell
is untruncated. -/
private lemma itoSimpleProcess_stepσ_incr {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) (T : ℝ≥0) {n k : ℕ} (hk : k < n) (ω : Ω) :
    itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val (unifPart T n (k + 1)) ω
        - itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val (unifPart T n k) ω
      = δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) := by
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  set t : ℕ → ℝ≥0 := unifPart T n with ht
  -- both process values as sums of per-cell single-rectangle evaluations
  have hstepval : ∀ t' : ℝ≥0,
      itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val t' ω
        = ∑ j ∈ (Finset.range n).attach,
            δ (t j.1) ω * (B (min (t (j.1 + 1)) t') ω - B (min (t j.1) t') ω) := by
    intro t'
    rw [stepσ, AddSubmonoidClass.coe_finsetSum, itoSimpleProcess_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [itoSimpleProcess_stepSP_apply hBmeas (unifPart_mono T n (Nat.le_succ j.1))
      (unifPart_le_T (Finset.mem_range.mp j.2)) (hδadap (t j.1)).measurable]
  rw [hstepval, hstepval, ← Finset.sum_sub_distrib]
  have hzero : ∀ j ∈ (Finset.range n).attach,
      j ≠ ⟨k, Finset.mem_range.mpr hk⟩ →
        δ (t ↑j) ω * (B (min (t (↑j + 1)) (t (k + 1))) ω - B (min (t ↑j) (t (k + 1))) ω)
          - δ (t ↑j) ω * (B (min (t (↑j + 1)) (t k)) ω - B (min (t ↑j) (t k)) ω) = 0 := by
    rintro j _ hj
    have hjk : (j : ℕ) ≠ k := fun h => hj (Subtype.ext h)
    by_cases hlt : (j : ℕ) < k
    · have h1 : min (t ((j : ℕ) + 1)) (t (k + 1)) = t ((j : ℕ) + 1) :=
        min_eq_left (hmono (by omega))
      have h2 : min (t (j : ℕ)) (t (k + 1)) = t (j : ℕ) := min_eq_left (hmono (by omega))
      have h3 : min (t ((j : ℕ) + 1)) (t k) = t ((j : ℕ) + 1) := min_eq_left (hmono (by omega))
      have h4 : min (t (j : ℕ)) (t k) = t (j : ℕ) := min_eq_left (hmono (by omega))
      rw [h1, h2, h3, h4]; ring
    · have h1 : min (t ((j : ℕ) + 1)) (t (k + 1)) = t (k + 1) :=
        min_eq_right (hmono (by omega))
      have h2 : min (t (j : ℕ)) (t (k + 1)) = t (k + 1) := min_eq_right (hmono (by omega))
      have h3 : min (t ((j : ℕ) + 1)) (t k) = t k := min_eq_right (hmono (by omega))
      have h4 : min (t (j : ℕ)) (t k) = t k := min_eq_right (hmono (by omega))
      rw [h1, h2, h3, h4]; ring
  rw [Finset.sum_eq_single_of_mem (f := fun j : {x // x ∈ Finset.range n} ↦
      δ (t j.1) ω * (B (min (t (j.1 + 1)) (t (k + 1))) ω - B (min (t j.1) (t (k + 1))) ω)
        - δ (t j.1) ω * (B (min (t (j.1 + 1)) (t k)) ω - B (min (t j.1) (t k)) ω))
    (⟨k, Finset.mem_range.mpr hk⟩) (Finset.mem_attach _ _) hzero]
  show δ (t k) ω * (B (min (t (k + 1)) (t (k + 1))) ω - B (min (t k) (t (k + 1))) ω)
      - δ (t k) ω * (B (min (t (k + 1)) (t k)) ω - B (min (t k) (t k)) ω)
    = δ (t k) ω * (B (t (k + 1)) ω - B (t k) ω)
  rw [min_self, min_self,
    min_eq_left (hmono (Nat.le_succ k)), min_eq_right (hmono (Nat.le_succ k))]
  ring

/-- **The CLM band-energy law**: the `L²` energy of the increment of the CLM Itô-integral
process of an arbitrary integrand class `φ'` over a band `(u,v]` is the band energy of the
integrand — the version-free analogue of `incrementEnergy`, proved directly at the CLM
level (the a.e. pull-out for the martingale cross term, the time-indexed isometry
`itoProcessCLM_norm_sq`, and the nested-band split). -/
private theorem clm_band_energy {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (φ' : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, ((itoProcessCLM hB T v hBmeas φ' : Ω → ℝ) ω
        - (itoProcessCLM hB T u hBmeas φ' : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  set A := itoProcessCLM hB T v hBmeas φ' with hAdef
  set b := itoProcessCLM hB T u hBmeas φ' with hbdef
  -- the martingale congruence at CLM level
  have hmart : μ[(A : Ω → ℝ) | natFiltration hBmeas u] =ᵐ[μ] (b : Ω → ℝ) :=
    itoIntegralProcessGen_isMartingale hB T hBmeas φ' huv
  have hAmem := Lp.memLp A
  have hbmem := Lp.memLp b
  have hAint : Integrable (A : Ω → ℝ) μ := hAmem.integrable one_le_two
  have hbint : Integrable (b : Ω → ℝ) μ := hbmem.integrable one_le_two
  -- cross-term kill through the a.e. pull-out (CLM values are a.e. 𝓕_u-measurable)
  have hbae : AEStronglyMeasurable[natFiltration hBmeas u] (b : Ω → ℝ) μ :=
    itoProcessCLM_aeStronglyMeasurable (μ := μ) hB T u hBmeas φ'
  have hAprod : Integrable (fun ω ↦ (b : Ω → ℝ) ω * (A : Ω → ℝ) ω) μ :=
    hbmem.integrable_mul hAmem
  have hcross : ∫ ω, (b : Ω → ℝ) ω * (A : Ω → ℝ) ω ∂μ
      = ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ := by
    calc ∫ ω, (b : Ω → ℝ) ω * (A : Ω → ℝ) ω ∂μ
        = ∫ ω, μ[(fun ω' ↦ (b : Ω → ℝ) ω' * (A : Ω → ℝ) ω') | natFiltration hBmeas u] ω ∂μ :=
          (integral_condExp ((natFiltration hBmeas).le u)).symm
      _ = ∫ ω, (b : Ω → ℝ) ω * μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω ∂μ :=
          integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left hbae hAprod hAint)
      _ = ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hmart] with ω hω
          rw [hω]
  have hAmem2 : Integrable (fun ω ↦ (A : Ω → ℝ) ω ^ 2) μ := hAmem.integrable_sq
  have hbmem2 : Integrable (fun ω ↦ (b : Ω → ℝ) ω ^ 2) μ := hbmem.integrable_sq
  -- expansion of the squared increment
  have hsplit : ∫ ω, ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ := by
    have hsq : ∫ ω, ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 ∂μ
        = ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)
            + (b : Ω → ℝ) ω ^ 2) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      show ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 = _
      ring
    rw [hsq]
    have h1 : ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)
        + (b : Ω → ℝ) ω ^ 2) ∂μ
        = ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)) ∂μ
          + ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ :=
      integral_add (hAmem2.sub (hAprod.const_mul 2)) hbmem2
    rw [h1]
    have h2 : ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)) ∂μ
        = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω) ∂μ :=
      integral_sub hAmem2 (hAprod.const_mul 2)
    rw [h2, integral_const_mul, hcross]
    have hbb : ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ = ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω ↦ by
        show (b : Ω → ℝ) ω * (b : Ω → ℝ) ω = _
        ring)
    rw [hbb]
    ring
  -- band energies through the time-indexed isometry
  have hband : ∀ w : ℝ≥0, w ≤ T →
      ∫ ω, (itoProcessCLM hB T w hBmeas φ' : Ω → ℝ) ω ^ 2 ∂μ
        = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro w hwT
    calc ∫ ω, (itoProcessCLM hB T w hBmeas φ' : Ω → ℝ) ω ^ 2 ∂μ
        = ‖itoProcessCLM hB T w hBmeas φ'‖ ^ 2 := sqIntegral_of_Lp _
      _ = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := itoProcessCLM_norm_sq hB hwT hBmeas φ'
  have hint : Integrable (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp φ').integrable_sq
  have hintU : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hintUV : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hdisj : Disjoint
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) :=
    Set.disjoint_left.2 fun a ha hb ↦ by
      have h1 : (u : ℝ) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
      have h2 : (a.1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast ha.1.2
      linarith
  have hbandsplit : ∫ z in Set.Ioc (0:ℝ≥0) v ×ˢ (Set.univ : Set Ω),
      (φ' : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have hprod0 : (Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω))
        ∪ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        = (Set.Ioc (0:ℝ≥0) v) ×ˢ (Set.univ : Set Ω) := by
      rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ≥0) ≤ u) huv]
    rw [← hprod0]
    exact setIntegral_union hdisj
      (MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ)
      hintU hintUV
  rw [hsplit, hband v hvT, hband u (le_trans huv hvT), hbandsplit]
  ring

end StageFour

/-! #### Stage 4 (headline) — the per-cell weighted identity, the `L¹` gap decay, and the
summed weighted increment isometry -/

section StageFourB

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The uniform-partition band split: the `(0,T]`-band integral of an integrable
space-time function is the sum of its uniform cell integrals (iterated
`setIntegral_union` over the nested left endpoints). -/
private lemma uniform_band_split (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {n : ℕ}
    (hn : 0 < n) {F : ℝ≥0 × Ω → ℝ}
    (hFint : Integrable F (trimMeasure_T (μ := μ) T hBmeas)) :
    ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω), F z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∑ k ∈ Finset.range n,
          ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
            F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  have hTn : unifPart T n n = T := by
    have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [unifPart, div_self hne, one_mul]
  have hintOn : ∀ m : ℕ, m ≤ n →
      IntegrableOn F ((Set.Ioc (0:ℝ≥0) (unifPart T n m)) ×ˢ (Set.univ : Set Ω))
        (trimMeasure_T (μ := μ) T hBmeas) := by
    intro m hm
    exact hFint.mono_measure (Measure.restrict_le_self)
  have key : ∀ m : ℕ, 0 < m → m ≤ n →
      ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω), F z
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∑ k ∈ Finset.range m,
            ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
              F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro m
    induction m with
    | zero => intro hm; exact absurd hm (Nat.not_lt_zero 0)
    | succ m ih =>
      intro hm hmT
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have h0 : unifPart T n 0 = 0 := by
          unfold unifPart
          norm_num
        rw [Finset.range_one, Finset.sum_singleton, h0]
      · have hmt : unifPart T n m ≤ unifPart T n (m + 1) :=
          unifPart_mono T n (Nat.le_succ m)
        have hunion : (Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω))
            ∪ (Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω))
            = (Set.Ioc (0:ℝ≥0) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω) := by
          rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc
            (show (0:ℝ≥0) ≤ unifPart T n m from by simp only [unifPart]; positivity) hmt]
        have hdisj : Disjoint
            ((Set.Ioc (0:ℝ≥0) (unifPart T n m)) ×ˢ (Set.univ : Set Ω))
            ((Set.Ioc (unifPart T n m) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω)) :=
          Set.disjoint_left.2 fun a ha hb ↦ by
            have h1 : ((unifPart T n m : ℝ)) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
            have h2 : (a.1 : ℝ) ≤ ((unifPart T n m : ℝ)) := by exact_mod_cast ha.1.2
            linarith
        have hintV : IntegrableOn F
            ((Set.Ioc (unifPart T n m) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω))
            (trimMeasure_T (μ := μ) T hBmeas) := by
          exact hFint.mono_measure (Measure.restrict_le_self)
        calc ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω), F z
              ∂(trimMeasure_T (μ := μ) T hBmeas)
            = ∫ z in (Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω))
                ∪ (Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω)),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by rw [hunion]
          _ = ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω), F z
                ∂(trimMeasure_T (μ := μ) T hBmeas)
              + ∫ z in Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) :=
              setIntegral_union hdisj
                (MeasureTheory.measurableSet_predictable_Ioc_prod (unifPart T n m)
                  (unifPart T n (m + 1)) MeasurableSet.univ)
                (hintOn m (by omega)) hintV
          _ = ∑ k ∈ Finset.range m,
                ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  F z ∂(trimMeasure_T (μ := μ) T hBmeas)
              + ∫ z in Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
              rw [ih hm0 (by omega)]
          _ = ∑ k ∈ Finset.range (m + 1),
                ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  F z ∂(trimMeasure_T (μ := μ) T hBmeas) := (Finset.sum_range_succ _ m).symm
  have hkey := key n hn (le_refl n)
  rw [hTn] at hkey
  exact hkey

/-- **Per-cell step identification at CLM level**: the increment over cell `k` of the
uniform partition of the step-approximant CLM process is a.e. the single rectangle
`δ(tₖ)·ΔBₖ`. -/
private theorem stepIncr_stepCLM_ae (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) {n k : ℕ} (hk : k < n) :
    (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω)
      =ᵐ[μ] (fun ω ↦ δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) := by
  have hcoe : ∀ t : ℝ≥0,
      (itoProcessCLM hB T t hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ)
        =ᵐ[μ] itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val t := by
    intro t
    rw [itoProcessCLM_simpleAssembly_T hB T t hBmeas (stepσ hBmeas hδadap hδbdd T n)]
    exact (memLp_itoSimpleProcess hB hBmeas (stepσ hBmeas hδadap hδbdd T n).val t).coeFn_toLp
  filter_upwards [hcoe (unifPart T n (k + 1)), hcoe (unifPart T n k)] with ω h2 h3
  show (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
    = δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
  rw [h2, h3, itoSimpleProcess_stepσ_incr hBmeas hδadap hδbdd T hk ω]

omit [IsProbabilityMeasure μ] in
/-- **The per-cell weighted identity** (the stage-4 core): for an `𝓕_{tₖ}`-measurable
weight `w`, the weighted second moment of the single rectangle `δ(tₖ)·ΔBₖ` is the frozen
rectangle energy `𝔼[w·δ(tₖ)²]·(tₖ₊₁ − tₖ)` — the isometry kernel
`integral_adapted_mul_increment_sq` at `χ = w·δ(tₖ)²` (adapted by the Doob–Dynkin bridge
`adaptedAt_of_measurable_natural` and its closure under products). -/
theorem weightedCellSq_step {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    {n k : ℕ} {w : Ω → ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w) :
    ∫ ω, w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = (∫ ω, w ω * δ (unifPart T n k) ω ^ 2 ∂μ)
        * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
  have hcongr : (fun ω ↦ w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2)
      =ᵐ[μ] (fun ω ↦ (w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω))
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) := by
    filter_upwards [] with ω
    show w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 = _
    ring
  have hχ : ItoIsometryAdapted.AdaptedAt B (unifPart T n k)
      (fun ω ↦ w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω)) :=
    (adaptedAt_of_measurable_natural hBmeas hwm).mul
      ((adaptedAt_of_measurable_natural hBmeas
        (hδadap (unifPart T n k)).measurable).mul
      (adaptedAt_of_measurable_natural hBmeas
        (hδadap (unifPart T n k)).measurable))
  have hcongr2 : (∫ ω, w ω * δ (unifPart T n k) ω ^ 2 ∂μ)
      = ∫ ω, w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by
      show w ω * δ (unifPart T n k) ω ^ 2 = _
      rw [pow_two])
  rw [integral_congr_ae hcongr, hcongr2]
  exact integral_adapted_mul_increment_sq hB hBmeas (unifPart_mono T n (Nat.le_succ k)) hχ

end StageFourB

/-! #### Stage 4 (headline) — the `L¹` gap decay, the summed weighted increment isometry,
and the convergence of the quadratic block -/

section StageFourC

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))

omit hB in
/-- The mean function of a bounded measurable path-continuous family is continuous
(the stage-1 DCT interchange, factored out). -/
private lemma continuous_mean_of_bdd_cont {g : ℝ≥0 → Ω → ℝ}
    (hgmeas : ∀ s, Measurable (g s)) (hgcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ g s ω)
    {C : ℝ} (hgbdd : ∀ s ω, |g s ω| ≤ C) :
    Continuous fun s : ℝ≥0 ↦ ∫ ω, g s ω ∂μ :=
  continuous_iff_continuousAt.mpr fun s₀ ↦
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : Ω ↦ C)
      (Eventually.of_forall fun s ↦ (hgmeas s).aestronglyMeasurable)
      (Eventually.of_forall fun s ↦ Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using hgbdd s ω)
      (integrable_const C)
      (Eventually.of_forall fun ω ↦ (hgcont ω).continuousAt)

omit hB in
/-- **The frozen Riemann convergence**: the left-endpoint Riemann sums of the deterministic
mean function of a bounded measurable path-continuous family converge to the time integral
of the means (the deterministic `tendsto_riemann_continuous` applied to the mean function). -/
theorem frozenRiemann_tendsto {g : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hgmeas : ∀ s, Measurable (g s)) (hgcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ g s ω)
    {C : ℝ} (hgbdd : ∀ s ω, |g s ω| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        (∫ ω, g (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hmeanbdd : ∀ s : ℝ≥0, |∫ ω, g s ω ∂μ| ≤ C := fun s ↦ by
    calc |∫ ω, g s ω ∂μ| ≤ ∫ ω, |g s ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ abs_nonneg _)
          (integrable_const C)
          (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hgbdd s ω)
      _ = C := by rw [integral_const]; simp
  exact tendsto_riemann_continuous (continuous_mean_of_bdd_cont hgmeas hgcont hgbdd) T
    (fun s _ ↦ hmeanbdd s)

variable {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

/-- The energy of the true increment: `𝔼[(M_v − M_u)²] ≤ D_δ²·(v−u)` for `u ≤ v ≤ T`
(`incrementEnergy` plus the pointwise `δ`-bound on the mean function). -/
private theorem trueIncr_sq_le {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, (M v ω - M u ω) ^ 2 ∂μ ≤ Dd ^ 2 * ((v : ℝ) - u) := by
  rw [incrementEnergy hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv hvT]
  have hgmeas : ∀ s : ℝ≥0, Measurable (fun ω ↦ δ s ω * δ s ω) :=
    fun s ↦ (((hδadap s).measurable.mul (hδadap s).measurable).mono
      ((natFiltration hBmeas).le s) le_rfl)
  have hgcont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ δ s ω * δ s ω :=
    fun ω ↦ (hδcont ω).mul (hδcont ω)
  have hDsq2 : |Dd| * |Dd| = Dd * Dd := by
    rcases le_total 0 Dd with h | h
    · rw [abs_of_nonneg h]
    · rcases eq_or_lt_of_le h with rfl | h'
      · simp
      · rw [abs_of_neg h']
        ring
  have hmeanbdd : ∀ s : ℝ≥0, |∫ ω, δ s ω * δ s ω ∂μ| ≤ Dd * Dd := by
    intro s
    calc |∫ ω, δ s ω * δ s ω ∂μ| ≤ ∫ ω, |δ s ω * δ s ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|Dd| * |Dd|) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            (integrable_const (μ := μ) (|Dd| * |Dd|)) ?_
          filter_upwards [] with ω
          show |δ s ω * δ s ω| ≤ |Dd| * |Dd|
          rw [abs_mul]
          calc |δ s ω| * |δ s ω| ≤ |Dd| * |δ s ω| :=
                mul_le_mul_of_nonneg_right
                  (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
            _ ≤ |Dd| * |Dd| := mul_le_mul_of_nonneg_left
                  (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
      _ = Dd * Dd := by
          rw [integral_const, hDsq2]
          simp
  have hmeanmeas : Measurable (fun s : ℝ≥0 ↦ ∫ ω, δ s ω * δ s ω ∂μ) :=
    (continuous_mean_of_bdd_cont hgmeas hgcont (fun s ω ↦ by
      show |δ s ω * δ s ω| ≤ |Dd| * |Dd|
      rw [abs_mul]
      calc |δ s ω| * |δ s ω| ≤ |Dd| * |δ s ω| :=
            mul_le_mul_of_nonneg_right (le_trans (hδbdd s ω) (le_abs_self Dd))
              (abs_nonneg _)
        _ ≤ |Dd| * |Dd| := mul_le_mul_of_nonneg_left
            (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _))).measurable
  haveI : IsFiniteMeasure
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top
  have hconst : ∫ s in Set.Ioc u v, (|Dd| * |Dd|) ∂ItoIntegralL2.timeMeasure
      = (|Dd| * |Dd|) * ((v : ℝ) - u) := by
    rw [MeasureTheory.setIntegral_const, measureReal_def,
      ItoIntegralL2.timeMeasure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv))]
    ring
  refine le_trans (integral_mono_of_nonneg
    (Eventually.of_forall fun s ↦ integral_nonneg (μ := μ)
      (f := fun ω ↦ δ s ω * δ s ω)
      (fun ω ↦ by
        show (0:ℝ) ≤ δ s ω * δ s ω
        rw [← pow_two]
        exact sq_nonneg (δ s ω)))
    (integrable_const (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v))
      (|Dd| * |Dd|))
    (Eventually.of_forall fun s ↦ by
      show (fun s : ℝ≥0 ↦ ∫ ω, δ s ω * δ s ω ∂μ) s
        ≤ (fun _ : ℝ≥0 ↦ |Dd| * |Dd|) s
      exact le_trans (le_of_eq rfl)
        (le_trans (le_abs_self (∫ ω, δ s ω * δ s ω ∂μ))
          (le_trans (hmeanbdd s) (le_of_eq hDsq2.symm))))) ?_
  calc ∫ s in Set.Ioc u v, (|Dd| * |Dd|) ∂ItoIntegralL2.timeMeasure
      = (|Dd| * |Dd|) * ((v : ℝ) - u) := hconst
    _ ≤ Dd ^ 2 * ((v : ℝ) - u) := by
        show |Dd| * |Dd| * ((v : ℝ) - u) ≤ Dd ^ 2 * ((v : ℝ) - u)
        rw [sq Dd, hDsq2]

set_option maxHeartbeats 1600000 in
/-- **The convergence of the quadratic block** (the summed weighted increment isometry,
conditional on the per-partition `L¹` gap decay): if the weighted second-moment sum along
the uniform partition differs from the frozen rectangle sum by at most
`2·|C_w|·|D_δ|·√T·‖φ − δⁿ‖_{L²(trim)}` — the per-cell Cauchy–Schwarz pairing of the error
increment against the cell energy, each factor bounded via `clm_band_energy`,
`trueIncr_sq_le` and `stepIncrSq_le`, and the cell bands paired by
`Finset.sum`-Cauchy–Schwarz against `deltaStepLp_tendsto` — then the sum converges to the
quadratic block `∫₀ᵀ 𝔼[w·δ²] ds`. -/
theorem quadraticSqSum_tendsto (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω)
    (hwbdd : ∀ s ω, |w s ω| ≤ Cw)
    (hgap : ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n →
      |∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ) * r n) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T,
          (∫ ω, w s ω * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hgmeas : ∀ s, Measurable (fun ω ↦ w s ω * (δ s ω * δ s ω)) := by
    intro s
    exact (((hwadap s).mono ((natFiltration hBmeas).le s) le_rfl).mul
      (((hδadap s).mono ((natFiltration hBmeas).le s)).measurable.mul
        ((hδadap s).mono ((natFiltration hBmeas).le s)).measurable))
  have hgcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω * (δ s ω * δ s ω) :=
    fun ω ↦ (hwcont ω).mul ((hδcont ω).mul (hδcont ω))
  have hgbdd : ∀ s ω, |w s ω * (δ s ω * δ s ω)| ≤ |Cw| * (Dd * Dd) := by
    intro s ω
    have hDd : |Dd| * |Dd| = Dd * Dd := by
      rcases le_total 0 Dd with h | h
      · rw [abs_of_nonneg h]
      · rcases eq_or_lt_of_le h with rfl | h'
        · simp
        · rw [abs_of_neg h']
          ring
    have hd2 : |δ s ω * δ s ω| ≤ |Dd| * |Dd| := by
      rw [abs_mul]
      exact mul_le_mul (le_trans (hδbdd s ω) (le_abs_self Dd))
        (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
        (abs_nonneg Dd)
    show |w s ω * (δ s ω * δ s ω)| ≤ |Cw| * (Dd * Dd)
    rw [abs_mul]
    exact (mul_le_mul (le_trans (hwbdd s ω) (le_abs_self Cw)) hd2 (abs_nonneg _)
      (abs_nonneg _)).trans (by rw [hDd])
  -- the frozen sums converge to the quadratic block
  have hF := frozenRiemann_tendsto (μ := μ) (T := T) hgmeas hgcont hgbdd
  have hFeq : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        = ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ by show _ = _; ring)
  obtain ⟨r, hr0, hgap'⟩ := hgap
  -- the gap dies along the null sequence r
  have hSFabs : Tendsto (fun n : ℕ ↦ |(∑ k ∈ Finset.range n,
      ∫ ω, w (unifPart T n k) ω
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
    - ∑ k ∈ Finset.range n,
        (∫ ω, w (unifPart T n k) ω
          * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
          * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ) * r n)
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have h := hgap' n hn
      rw [hFeq n] at h
      exact h
    · simpa using (tendsto_const_nhds
        (x := 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ))).mul hr0
  have hSF : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      - ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) atTop (𝓝 0) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    refine Filter.Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hSFabs
    show |(∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
      = dist ((∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) 0
    rw [Real.dist_eq, sub_zero]
  have key := hSF.add hF
  rw [zero_add] at key
  exact key.congr' (Eventually.of_forall fun n ↦ by
    show (∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      + ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
      = _
    ring)

end StageFourC

/-! #### Stage 5a — the `L¹` gap decay, unconditional

The per-cell Cauchy–Schwarz pairing of the error increment `δεₖ = ΔMₖ − δ(tₖ)·ΔBₖ`
against the cell energy. The error increment is the band increment of the CLM process of
the integrand error `ψₙ = φ − δⁿ` (linearity of the CLM map + the per-cell step
identification), so its band energy is `∫_{bandₖ} ψₙ²` (`clm_band_energy`) and the summed
band energies telescope to `‖ψₙ‖²_{L²(trim)}` (`uniform_band_split` + the `Lp` norm).
The pairing gives exactly the constant `2·|C_w|·|D_δ|·√T` of `quadraticSqSum_tendsto`'s
`hgap`, and `deltaStepLp_tendsto` makes the bound a null sequence. -/

section StageFiveA

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

omit hδadap hδcont hδbdd hMadap hMeq in
/-- Coe-linearity of the CLM process in the integrand class (the a.e. form). -/
private theorem clm_coe_sub_ae (T t : ℝ≥0)
    (φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ((itoProcessCLM hB T t hBmeas (φ₁ - φ₂) : Lp ℝ 2 μ) : Ω → ℝ)
      =ᵐ[μ] (fun ω ↦ (itoProcessCLM hB T t hBmeas φ₁ : Ω → ℝ) ω
        - (itoProcessCLM hB T t hBmeas φ₂ : Ω → ℝ) ω) := by
  rw [map_sub]
  exact Lp.coeFn_sub _ _

omit hMadap in
/-- The per-cell error increment `δεₖ := ΔMₖ − δ(tₖ)·ΔBₖ` is a.e. the band increment of the
CLM process of the integrand error `φ − δⁿ`. -/
private theorem errorIncr_ae {n k : ℕ} (hk : k < n) :
    (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
      =ᵐ[μ] (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) := by
  have h1 := hMeq (unifPart T n (k + 1))
  have h0 := hMeq (unifPart T n k)
  have hsub1 := clm_coe_sub_ae (μ := μ) hB hBmeas T (unifPart T n (k + 1))
    (processToLp T hBmeas hδadap hδcont hδbdd) (deltaStepLp hBmeas hδadap hδbdd n)
  have hsub0 := clm_coe_sub_ae (μ := μ) hB hBmeas T (unifPart T n k)
    (processToLp T hBmeas hδadap hδcont hδbdd) (deltaStepLp hBmeas hδadap hδbdd n)
  have hstep : (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω)
      =ᵐ[μ] (fun ω ↦ δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) :=
    stepIncr_stepCLM_ae (μ := μ) (B := B) (hB := hB) (hBmeas := hBmeas)
    (hδadap := hδadap) (hδbdd := hδbdd) (T := T) (n := n) (k := k) hk
  filter_upwards [h1, h0, hsub1, hsub0, hstep] with ω h1 h0 hsub1 hsub0 hstep
  calc M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
      = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
        - ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) := by
        rw [h1, h0, ← hstep]
    _ = ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω)
        - ((itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) := by ring
    _ = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω := by
        rw [hsub1, hsub0]

omit hMadap in
/-- The second moment of the error increment is the band energy of the integrand error
`ψₙ = φ − δⁿ` over the cell (the version-free `clm_band_energy` transferred along the a.e.
identification). -/
private theorem errorIncr_sq_eq_band {n k : ℕ} (hk : k < n) :
    ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  refine (integral_congr_ae ?_).trans
    (clm_band_energy hB hBmeas T
      (processToLp T hBmeas hδadap hδcont hδbdd - deltaStepLp hBmeas hδadap hδbdd n)
      (unifPart_mono T n (Nat.le_succ k))
      (unifPart_le_T hk))
  filter_upwards [errorIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq hk] with ω hω
  rw [hω]

set_option linter.unusedSectionVars false in
omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Generic weighted-square transfer: if `f =ᵐ g`, `g²` is integrable with energy `E`,
and `|w| ≤ C`, then `𝔼[(w·f)²] ≤ C²·E`. -/
private theorem weighted_sq_le_of_congr {f g w : Ω → ℝ} {C : ℝ}
    (hwb : ∀ ω, |w ω| ≤ C) (hcongr : f =ᵐ[μ] g)
    (hint2 : Integrable (fun ω ↦ g ω ^ 2) μ) (hE : ∫ ω, g ω ^ 2 ∂μ = E) :
    ∫ ω, (w ω * f ω) ^ 2 ∂μ ≤ C ^ 2 * E := by
  have hw : ∀ ω : Ω, w ω ^ 2 ≤ C ^ 2 := fun ω ↦ by
    have h := mul_self_le_mul_self (abs_nonneg (w ω)) (hwb ω)
    have e1 : |w ω| * |w ω| = w ω ^ 2 := by
      rw [← pow_two, sq_abs]
    have e2 : C * C = C ^ 2 := (sq C).symm
    rwa [e1, e2] at h
  have hdom : Integrable (fun ω ↦ (C * g ω) ^ 2) μ :=
    (hint2.const_mul (C ^ 2)).congr
      (Eventually.of_forall fun ω ↦ by ring)
  calc ∫ ω, (w ω * f ω) ^ 2 ∂μ
      = ∫ ω, (w ω * g ω) ^ 2 ∂μ := integral_congr_ae
          (by filter_upwards [hcongr] with ω hω; rw [hω])
    _ ≤ ∫ ω, (C * g ω) ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          hdom (Eventually.of_forall fun ω ↦ ?_)
        show (w ω * g ω) ^ 2 ≤ (C * g ω) ^ 2
        have h1 : (w ω * g ω) ^ 2 = w ω ^ 2 * g ω ^ 2 := by ring
        have h2 : (C * g ω) ^ 2 = C ^ 2 * g ω ^ 2 := by ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_right (hw ω) (sq_nonneg _)
    _ = C ^ 2 * E := by
        rw [integral_congr_ae (Eventually.of_forall fun ω ↦ by
          show (C * g ω) ^ 2 = C ^ 2 * g ω ^ 2; ring), integral_const_mul, hE]

include hB hMadap hMeq in
/-- **Weighted error energy**: the second moment of `w·δεₖ` is at most `C_w²` cell-band
energies of the integrand error (`|w| ≤ C_w` pointwise, the error increment paired with the
band energy through `errorIncr_sq_eq_band`). -/
private theorem weightedErrorIncr_sq_le {n k : ℕ} (hk : k < n) {w : Ω → ℝ} {Cw : ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w)
    (hwb : ∀ ω, |w ω| ≤ Cw) :
    ∫ ω, (w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))) ^ 2 ∂μ
      ≤ Cw ^ 2 * ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
            (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  -- the CLM error increment and its square integrability
  have hDmem : MemLp
      (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n))).sub
      (Lp.memLp (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n)))
  -- the energy of the CLM error increment is the band energy
  have hbandE : ∫ ω, ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
    (clm_band_energy hB hBmeas T
      (processToLp T hBmeas hδadap hδcont hδbdd - deltaStepLp hBmeas hδadap hδbdd n)
      (unifPart_mono T n (Nat.le_succ k))
      (unifPart_le_T hk))
  exact weighted_sq_le_of_congr hwb
    (errorIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq hk)
    hDmem.integrable_sq hbandE

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The real `L²` triangle inequality at the integral level: `‖a + b‖₂ ≤ ‖a‖₂ + ‖b‖₂`. -/
private theorem sqrtIntegral_sq_add_le {a b : Ω → ℝ}
    (ham : MemLp a 2 μ) (hbm : MemLp b 2 μ) :
    Real.sqrt (∫ ω, (a ω + b ω) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ) := by
  have ha2 := ham.integrable_sq
  have hb2 := hbm.integrable_sq
  have hab := ham.integrable_mul hbm
  have hexp : ∫ ω, (a ω + b ω) ^ 2 ∂μ
      = ∫ ω, a ω ^ 2 ∂μ + 2 * ∫ ω, a ω * b ω ∂μ + ∫ ω, b ω ^ 2 ∂μ :=
    integral_sq_add ha2 hb2 hab
  have hcs : ∫ ω, a ω * b ω ∂μ
      ≤ Real.sqrt (∫ ω, a ω ^ 2 ∂μ) * Real.sqrt (∫ ω, b ω ^ 2 ∂μ) := by
    refine le_trans (integral_mono hab hab.abs (fun ω ↦ le_abs_self _)) ?_
    exact integral_abs_mul_le_L2L2 ham hbm
  calc Real.sqrt (∫ ω, (a ω + b ω) ^ 2 ∂μ)
      = Real.sqrt (∫ ω, a ω ^ 2 ∂μ + 2 * ∫ ω, a ω * b ω ∂μ + ∫ ω, b ω ^ 2 ∂μ) := by
        rw [hexp]
    _ ≤ Real.sqrt ((Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have hA : Real.sqrt (∫ ω, a ω ^ 2 ∂μ) ^ 2 = ∫ ω, a ω ^ 2 ∂μ :=
          Real.sq_sqrt (integral_nonneg fun ω ↦ sq_nonneg _)
        have hB : Real.sqrt (∫ ω, b ω ^ 2 ∂μ) ^ 2 = ∫ ω, b ω ^ 2 ∂μ :=
          Real.sq_sqrt (integral_nonneg fun ω ↦ sq_nonneg _)
        have hrw : (Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ)) ^ 2
            = Real.sqrt (∫ ω, a ω ^ 2 ∂μ) ^ 2
              + 2 * (Real.sqrt (∫ ω, a ω ^ 2 ∂μ) * Real.sqrt (∫ ω, b ω ^ 2 ∂μ))
              + Real.sqrt (∫ ω, b ω ^ 2 ∂μ) ^ 2 := by ring
        rw [hrw, hA, hB]
        linarith [hcs]
    _ = Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- **Per-cell gap bound**: the `L¹` distance over one cell between the weighted
true-increment square and the weighted rectangle square — the Cauchy–Schwarz pairing of the
error increment `δεₖ` against the cell energy `ΔMₖ + δ(tₖ)ΔBₖ`, each factor bounded by the
weighted error energy (`weightedErrorIncr_sq_le`) and the `2·|D_δ|·√cell` cell energy
(`trueIncr_sq_le` + the rectangle second moment). -/
private theorem cellGap_le {n k : ℕ} (hk : k < n) {w : Ω → ℝ} {Cw : ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w)
    (hwb : ∀ ω, |w ω| ≤ Cw) :
    |∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
      ≤ 2 * |Cw| * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
        * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
            (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
  have huv : unifPart T n k ≤ unifPart T n (k + 1) := unifPart_mono T n (Nat.le_succ k)
  have hδm : Measurable (δ (unifPart T n k)) :=
    ((hδadap (unifPart T n k)).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hdBm : Measurable (fun ω ↦ B (unifPart T n (k + 1)) ω
      - B (unifPart T n k) ω) := (hBmeas _).sub (hBmeas _)
  have hwm' : Measurable w := hwm.mono ((natFiltration hBmeas).le _) le_rfl
  have hsmeas : Measurable (fun ω ↦ δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) := hδm.mul hdBm
  have hMsub : MemLp (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) 2 μ :=
    (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n (k + 1))).sub
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))
  have hMsub2 : Integrable (fun ω ↦ (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2) μ := hMsub.integrable_sq
  have hdB : MemLp (fun ω ↦ B (unifPart T n (k + 1)) ω
      - B (unifPart T n k) ω) 2 μ := hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  -- the rectangle increment `s = δ(tₖ)·ΔBₖ` is `L²`
  have hs : MemLp (fun ω ↦ δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) 2 μ :=
    MemLp.mono' (hdB.const_mul (|Dd|)).abs
      hsmeas.aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        show ‖δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)‖
          ≤ |(|Dd| * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))|
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (abs_nonneg Dd)]
        exact mul_le_mul_of_nonneg_right (le_trans (hδbdd (unifPart T n k) ω)
          (le_abs_self Dd)) (abs_nonneg _))
  -- measurability of the true increment
  have hM1m : Measurable (M (unifPart T n (k + 1))) :=
    ((hMadap (unifPart T n (k + 1))).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hM0m : Measurable (M (unifPart T n k)) :=
    ((hMadap (unifPart T n k)).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hMsubm : Measurable (fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) := hM1m.sub hM0m
  -- integrability of the two weighted terms
  have hwM2 : Integrable (fun ω ↦ w ω * (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2) μ := by
    refine Integrable.mono' (hMsub2.const_mul Cw)
      (hwm'.mul (hMsubm.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))]
        exact mul_le_mul_of_nonneg_right (hwb ω) (sq_nonneg _))
  have hws2 : Integrable (fun ω ↦ w ω * (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2) μ := by
    refine Integrable.mono' ((hdB.integrable_sq).const_mul (Cw * Dd ^ 2))
      (hwm'.mul (hsmeas.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_mul]
        have hδ2 : |δ (unifPart T n k) ω| ≤ |Dd| :=
          le_trans (hδbdd (unifPart T n k) ω) (le_abs_self Dd)
        have hAB : |δ (unifPart T n k) ω| * |B (unifPart T n (k + 1)) ω
            - B (unifPart T n k) ω| ≤ |Dd| * |B (unifPart T n (k + 1)) ω
            - B (unifPart T n k) ω| :=
          mul_le_mul_of_nonneg_right hδ2 (abs_nonneg _)
        have h2 := sq_le_sq' (by
          have hB0 := mul_nonneg (abs_nonneg (|Dd|))
            (abs_nonneg (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          have hA0 := mul_nonneg (abs_nonneg (δ (unifPart T n k) ω))
            (abs_nonneg (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          linarith) hAB
        have h3 : (|Dd| * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω|) ^ 2
            = Dd ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
          rw [mul_pow, sq_abs, sq_abs]
        calc |w ω| * (|δ (unifPart T n k) ω| * |B (unifPart T n (k + 1)) ω
                - B (unifPart T n k) ω|) ^ 2
            ≤ |w ω| * ((|Dd| * |B (unifPart T n (k + 1)) ω
              - B (unifPart T n k) ω|) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ Cw * ((|Dd| * |B (unifPart T n (k + 1)) ω
              - B (unifPart T n k) ω|) ^ 2) :=
              mul_le_mul_of_nonneg_right (hwb ω) (sq_nonneg _)
          _ = Cw * Dd ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
              rw [h3]; ring)
  -- the square identity and the integral form of the gap
  have key : ∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = ∫ ω, w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ∂μ := by
    rw [← integral_sub hwM2 hws2]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  -- the Cauchy–Schwarz pairing
  have hDmem : MemLp (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n))).sub
      (Lp.memLp (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n)))
  have haede := errorIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq hk
  have hδεsm : AEStronglyMeasurable (fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω
      - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) μ :=
    AEStronglyMeasurable.congr hDmem.1 haede.symm
  have hpair : ∫ ω, |w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
          - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
        * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))| ∂μ
      ≤ Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
            - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))) ^ 2 ∂μ)
        * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
    integral_abs_mul_le_L2L2
      (MemLp.mono' ((hDmem.abs).const_mul (|Cw|))
        (hwm'.aestronglyMeasurable.mul hδεsm)
        (by
          filter_upwards [haede] with ω hω
          rw [Real.norm_eq_abs, abs_mul, hω]
          exact mul_le_mul_of_nonneg_right (le_trans (hwb ω) (le_abs_self Cw))
            (abs_nonneg _)))
      (hMsub.add hs)
  -- the two energy factors
  have hwde := weightedErrorIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq hk hwm hwb
  have htri : Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        + Real.sqrt (∫ ω, (δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
    sqrtIntegral_sq_add_le hMsub hs
  have hM2le := trueIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv
    (unifPart_le_T hk)
  have hs2le : ∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      ≤ Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    have hdom : Integrable (fun ω ↦ Dd ^ 2
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ :=
      (hdB.integrable_sq.const_mul (Dd ^ 2)).congr
        (Eventually.of_forall fun ω ↦ by ring)
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
      hdom (ae_of_all _ fun ω ↦ ?_)) ?_
    · show (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ≤ _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq).mpr (le_trans (hδbdd (unifPart T n k) ω) (le_abs_self Dd))) (sq_nonneg _)
    · rw [integral_const_mul]
      have hΔ : ∫ ω, (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 ∂μ
          = ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
        integral_increment_sq hB (unifPart_mono T n (Nat.le_succ k))
      rw [hΔ]
  -- the two sqrt bounds
  have hsqrtM : Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2 ∂μ) ≤ |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k) := by
    refine le_trans (Real.sqrt_le_sqrt hM2le) ?_
    rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
  have hsqrts : Real.sqrt (∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    refine le_trans (Real.sqrt_le_sqrt hs2le) ?_
    rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
  have hsqrttri : Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ 2 * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    have h1 := htri
    have h2 := hsqrtM
    have h3 := hsqrts
    nlinarith [Real.sqrt_nonneg (∫ ω, (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2 ∂μ), Real.sqrt_nonneg (∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)]
  -- assembly
  calc |∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w ω * (δ (unifPart T n k) ω
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
      = |∫ ω, w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
            * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ∂μ| :=
        by rw [key]
    _ ≤ ∫ ω, |w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
            * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))) ^ 2 ∂μ)
          * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
        hpair
    _ ≤ (|Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)))
          * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_right
          (by
            calc Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
                      - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω
                        - B (unifPart T n k) ω)))) ^ 2 ∂μ)
                ≤ Real.sqrt (Cw ^ 2 * ∫ z in Set.Ioc (unifPart T n k)
                    (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  ((processToLp T hBmeas hδadap hδcont hδbdd
                      - deltaStepLp hBmeas hδadap hδbdd n :
                        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
                  ∂(trimMeasure_T (μ := μ) T hBmeas)) := Real.sqrt_le_sqrt hwde
              _ = |Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k)
                    (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  ((processToLp T hBmeas hδadap hδcont hδbdd
                      - deltaStepLp hBmeas hδadap hδbdd n :
                        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
                  ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
                  rw [Real.sqrt_mul (sq_nonneg Cw), Real.sqrt_sq_eq_abs])
          (Real.sqrt_nonneg _)
    _ ≤ (|Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)))
          * (2 * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) :=
        mul_le_mul_of_nonneg_left hsqrttri
          (mul_nonneg (abs_nonneg Cw) (Real.sqrt_nonneg _))
    _ = 2 * |Cw| * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
          * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)) := by ring

/-- **The summed gap bound** (the `hgap` witness of `quadraticSqSum_tendsto`, made
unconditional): the summed per-cell `L¹` gap is at most `2·|C_w|·|D_δ|·√T` times the `L²`
norm of the integrand error `φ − δⁿ` — per-cell Cauchy–Schwarz (`cellGap_le`), then
finite-sum Cauchy–Schwarz against the cell lengths (telescoping to `T`) and the summed band
energies of the error class (telescoping to `‖φ − δⁿ‖²` via `uniform_band_split` and the
`Lp` norm). -/
theorem gapSum_le (n : ℕ) (hn : 0 < n) {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwbdd : ∀ t ω, |w t ω| ≤ Cw) :
    |∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
      - ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
      ≤ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ)
        * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
  -- the cell lengths and the band energies of the integrand error
  set cell : ℕ → ℝ := fun k ↦ ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hcelldef
  set bandE : ℕ → ℝ := fun k ↦ ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
      (Set.univ : Set Ω),
      ((processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas) with hbandEdef
  -- bridge the frozen sum to the rectangle sum (the per-cell weighted identity)
  have hsumbridge : ∑ k ∈ Finset.range n,
      (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ) * cell k
      = ∑ k ∈ Finset.range n, ∫ ω, w (unifPart T n k) ω
          * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ :=
    Finset.sum_congr rfl fun k _ ↦
      (weightedCellSq_step hB hBmeas hδadap (hwadap (unifPart T n k))).symm
  -- per-cell gap bounds
  have hpercell : ∀ k ∈ Finset.range n,
      |∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
        ≤ 2 * |Cw| * |Dd| * Real.sqrt (cell k) * Real.sqrt (bandE k) :=
    fun k hk => cellGap_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq (Finset.mem_range.mp hk)
      (hwadap (unifPart T n k)) (hwbdd (unifPart T n k))
  -- the cell lengths telescope to `T`; the band energies telescope to `‖φ − δⁿ‖²`
  have hsumcell : ∑ k ∈ Finset.range n, cell k = (T : ℝ) := by
    rw [sum_telescope (a := fun k ↦ ((unifPart T n k : ℝ)))]
    have hnT : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart, div_self hne, one_mul]
    have h0 : unifPart T n 0 = 0 := by simp only [unifPart]; norm_num
    rw [hnT, h0]; simp
  have hbandsum : ∑ k ∈ Finset.range n, bandE k
      = ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas) :=
    (uniform_band_split hBmeas hn
      (hFint := (Lp.memLp (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n)).integrable_sq)).symm
  -- finite-sum Cauchy–Schwarz on the cell/band pairing
  have hf2 : ∀ k : ℕ, (Real.sqrt (cell k)) ^ 2 = cell k := fun k ↦
    Real.sq_sqrt (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k))))
  have hg2 : ∀ k : ℕ, (Real.sqrt (bandE k)) ^ 2 = bandE k := fun k ↦
    Real.sq_sqrt (integral_nonneg fun z ↦ sq_nonneg _)
  have hsq : (∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))) ^ 2
      ≤ (T : ℝ) * ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (f := fun k : ℕ ↦ Real.sqrt (cell k)) (g := fun k : ℕ ↦ Real.sqrt (bandE k))
    rw [Finset.sum_congr rfl fun k _ ↦ hf2 k, Finset.sum_congr rfl fun k _ ↦ hg2 k,
      hsumcell, hbandsum] at key
    exact key
  have hpair : ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))
      ≤ Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
    have hX0 : 0 ≤ ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k)) :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))
        ≤ Real.sqrt ((∑ k ∈ Finset.range n,
          (Real.sqrt (cell k) * Real.sqrt (bandE k))) ^ 2) := by
          rw [Real.sqrt_sq hX0]
      _ ≤ Real.sqrt ((T : ℝ) * ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
          rw [Real.sqrt_mul (NNReal.coe_nonneg T)]
  -- assembly
  calc |∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ) * cell k|
      = |∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)| := by
        rw [hsumbridge, ← Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range n,
          |∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, 2 * |Cw| * |Dd| * (Real.sqrt (cell k)
          * Real.sqrt (bandE k)) :=
        Finset.sum_le_sum fun k hk ↦ by
          rw [show (2:ℝ) * |Cw| * |Dd| * (Real.sqrt (cell k) * Real.sqrt (bandE k))
              = 2 * |Cw| * |Dd| * Real.sqrt (cell k) * Real.sqrt (bandE k) from by ring]
          exact hpercell k hk
    _ = 2 * |Cw| * |Dd| * ∑ k ∈ Finset.range n,
          (Real.sqrt (cell k) * Real.sqrt (bandE k)) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * |Cw| * |Dd| * (Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ
          (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas))) :=
        mul_le_mul_of_nonneg_left hpair
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg Cw)) (abs_nonneg Dd))
    _ = 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ)
          * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)) := by ring

/-- **The convergence of the quadratic block, unconditional** (the `hgap` hypothesis of
`quadraticSqSum_tendsto` discharged by `gapSum_le` + `deltaStepLp_tendsto`). -/
theorem quadraticSqSum_tendsto_uncond (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω)
    (hwbdd : ∀ s ω, |w s ω| ≤ Cw) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T,
          (∫ ω, w s ω * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  refine quadraticSqSum_tendsto hB hBmeas hδadap hδcont hδbdd hMadap hMeq
    hB hBmeas hδadap hδcont hδbdd hMadap hMeq hwadap hwcont hwbdd
    ⟨fun n ↦ Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
      ((processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas)), ?_, ?_⟩
  · -- `r n` is squeezed by `‖φ − δⁿ‖ → 0` (the band integral is at most the full norm²)
    have htend := deltaStepLp_tendsto (T := T) hB hBmeas hδadap hδcont hδbdd
    have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp htend).congr'
      (Eventually.of_forall fun n ↦ by rw [norm_sub_rev])
    refine squeeze_zero' (Eventually.of_forall fun n ↦ Real.sqrt_nonneg _) ?_ hnorm
    filter_upwards [] with n
    refine le_trans (Real.sqrt_le_sqrt ?_)
      (le_of_eq (show Real.sqrt (‖(processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ ^ 2)
        = ‖(processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ from
        Real.sqrt_sq (norm_nonneg _)))
    have hsqint : Integrable (fun z ↦
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        (trimMeasure_T (μ := μ) T hBmeas) :=
      (Lp.memLp (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n)).integrable_sq
    have hintband : IntegrableOn (fun z ↦
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
      hsqint.mono_measure Measure.restrict_le_self
    have hbandmsP : MeasurableSet[(natFiltration hBmeas).predictable]
        (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioc_prod (0:ℝ≥0) T MeasurableSet.univ
    have hbandms : MeasurableSet (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) :=
      MeasurableSet.prod (measurableSet_Ioc (α := ℝ≥0)) MeasurableSet.univ
    have hintInd : Integrable ((Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)).indicator
        (fun z ↦ ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2))
        (trimMeasure_T (μ := μ) T hBmeas) :=
      (integrable_indicator_iff (μ := trimMeasure_T (μ := μ) T hBmeas)
        (f := fun z : ℝ≥0 × Ω ↦
          ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        hbandmsP).mpr hintband
    calc ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ z, (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)).indicator
            (fun z ↦ ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          (integral_indicator (μ := trimMeasure_T (μ := μ) T hBmeas)
            (f := fun z : ℝ≥0 × Ω ↦
              ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
            hbandmsP).symm
      _ ≤ ∫ z, ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          integral_mono hintInd hsqint (fun z ↦ by
            by_cases hz : z ∈ Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)
            · rw [Set.indicator_of_mem hz]
            · rw [Set.indicator_of_notMem hz]
              exact sq_nonneg _)
      _ = ‖(processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ ^ 2 :=
          (lp_two_norm_sq (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n)).symm
  · exact fun n hn ↦ gapSum_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq n hn hwadap hwbdd

end StageFiveA

end ItoContribution

#print axioms ItoContribution.expectation_pathIntegral_eq
#print axioms ItoContribution.itoDrift_expectation_identity
#print axioms ItoContribution.incrementEnergy
#print axioms ItoContribution.deltaStepLp_tendsto
#print axioms ItoContribution.weightedCellSq_step
#print axioms ItoContribution.gapSum_le
#print axioms ItoContribution.quadraticSqSum_tendsto
#print axioms ItoContribution.quadraticSqSum_tendsto_uncond

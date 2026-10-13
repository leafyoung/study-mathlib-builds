# Lean builds — affine engine (lesson 0033)

`AffineEngineScratch.lean` — the affine engine, deterministic core, landed 2026-10-04
in four sequential subagent stages (max-thinking, one at a time), 906 lines, zero
`sorry`, all axioms standard (`propext`, `Classical.choice`, `Quot.sound`):

- Stage 1: OU generator + exponential-affine invariance lemma + Riccati corollary
- Stage 2: Vasicek bond ODE (`bondSlope` = MathFin's `vasicekBondB`, proved `rfl`),
  Bernoulli Riccati flow (minus-form — the prompt's plus-form was caught wrong),
  discounted pricing PDE for the bond ansatz
- Stage 3: CIR generator invariance, bracket corollary, CIR discounted pricing PDE
  (corrected calendar-time system: ψ′ = κψ + ξ²/2·ψ² − 1 — the prompt's undiscounted
  hψ made the PDE false)
- Stage 4: CIR bond closed form (γ = √(κ²+2ξ²); B(0) = 0 — the prompt's B(0) = 1 was
  inconsistent), log-A antiderivative, `cirBondPrice_pde` + terminal condition

Build: copy into `AmericanPutConvexity/` and run `lake env lean AffineEngineScratch.lean`
(elan with Lean 4.32.0 required; MathFin import needs
`lake build MathFin.FixedIncome.VasicekBondPrice` once).

Still open for a complete CIR pricing theorem (per lesson 0033): CIR existence via
squared-OU (Feller 2κθ ≥ ξ²), the Dynkin/expectation bridge (absent from Mathlib),
ODE-uniqueness lemma, optional explicit-A integral form.

---

# Build queue item 9 — MathFin Itô contribution (adapted drift identity), dispatch 4

`ItoContribution.lean` (prototype in `AmericanPutConvexity/`, archived here), landed
2026-10-07 by dispatch 4, 1729 lines, zero `sorry`, all public theorems standard-three
axioms. Cumulative across dispatches 1–4:

- Stage 1 (d1): constant-coefficient integrated Itô–drift identity
  `itoDrift_expectation_identity` + the Fubini lemma `expectation_pathIntegral_eq`.
- Stage 2 (d2): terminal cross-isometry `crossTerminal_isometry`, band-slice conversion
  `bandIntegral_slice`.
- Stage-3 foundations (d3): `integral_mul_condExp_eq`, `memLp_M`, `incrementEnergy`
  (unweighted increment isometry), `deltaStepLp`/`deltaStepLp_tendsto`.
- Stage 4 (d4, this dispatch): per-cell weighted identity `weightedCellSq_step`
  (isometry kernel at the adapted weight, via the Doob–Dynkin bridge
  `ItoIntegralL2.adaptedAt_of_measurable_natural`), per-cell step identification
  `stepIncr_stepCLM_ae`, version-free `clm_band_energy`, `uniform_band_split`,
  `integral_abs_mul_le_L2L2`, `trueIncr_sq_le`, `stepIncrSq_le`,
  `frozenRiemann_tendsto`, and `quadraticSqSum_tendsto` — the convergence of the
  quadratic block, conditional on the per-partition `L¹` gap decay (hypothesis `hgap`,
  stated as an abstract null-sequence bound; the designed proof is the per-cell
  Cauchy–Schwarz pairing, all analytic inputs landed).

Remaining to the full Bagaria ch. 9 Thm 9.6 support: (a) discharge `hgap` (the a.e.
bookkeeping for `δε = ΔM − δ(tₖ)ΔBₖ` + `TendstoInMeasure.exists_seq_tendsto_ae` +
Fatou for the third-moment bound, ≈300 lines); (b) the assembly
`itoDrift_expectation_identity_adapted` (drift block: pathwise step-family DCT +
stage-1 Fubini; cross terms: martingale pull-out via `integral_mul_condExp_eq`;
Taylor remainder: the third-moment bound), consuming `quadraticSqSum_tendsto` with
`r n := ‖φ − δⁿ‖_{L²(trim)}`; (c) Gyöngy adapter (item 11). MathFin port deferred per
the do-not-port-partial-instruments rule until (a)+(b) land.

`GyongyScratch.lean`: docstring updated (comment-only) to cite the dispatch-4
theorems; `hitoid` retained — the abstract ℝ-indexed `BoundedItoProcess` still needs
the adapter lemma.

---

# Build queue item 15 — Tier-1 Cox-intensity credit (lesson 0032)

`cox_scratch.lean` (in `AmericanPutConvexity/`, archived here), landed 2026-10-10,
697 lines, 20 public theorems + 9 private helpers, zero `sorry`, zero errors, zero
warnings, all public theorems standard-three axioms. Build:
`cd AmericanPutConvexity && lake env lean cox_scratch.lean` (MathFin import needs
`lake build MathFin.FixedIncome.CDSTimeVarying` once — done).

- **Layer 1 (consumed, not re-proved)**: `defaultSurvival_const` /
  `defaultTimeLaw_const` package the pin's
  `PoissonInterarrival.survival_eq` / `.map_firstArrival_eq_expMeasure` in
  credit variables (one rewrite each; `map_count_eq_poissonMeasure` recorded as
  the alternative route, lesson 0032 Ex. 1).
- **Layer 2 (constant λ, closed forms)**: `riskyAnnuity_eq`
  (`∫₀ᵀ e^{−(r+λ)s} = (1−e^{−(r+λ)T})/(r+λ)`), `riskyAnnuity_pos`,
  `protectionLeg_const` (protection = λ × annuity), `cdsLegs_balance_const`
  (the pin's abstract `cds_leg_equality` realized at the concrete integral —
  fair spread = `cdsFairSpread λ R`), `cdsFairSpread_const_balances`.
- **Layer 3 (deterministic λ(t) — the honest intermediate)**: `cumHazard_deriv`
  (FTC `Λ' = h`), `cumHazard_strictMono` (via `strictMono_of_hasDerivAt_pos`),
  `cumHazard_surjOn_Ici` (IVT from divergence), and the constructed default time
  `coxDefaultTime h ξ = invFun (cumHazard h) ∘ ξ` for a unit-exponential clock:
  **`cox_survival_timeVarying`: P(τ > t) = e^{−Λ(t)}** and
  `cox_cdf_timeVarying`: P(τ ≤ a) = 1 − e^{−Λ(a)}. Mechanism: a.e. set equality
  `{τ > t} = {ξ > Λ t}` off the null set `{ξ < 0}` — no inverse continuity or
  inverse measurability needed (no `Monotone.invFun` API at the pin).
- **Layer 4 (the headline)**: `cdsAnnuity`/`cdsLosses` (concrete integrals),
  `premiumLeg`/`protectionLeg` (the legs as definitions), `cdsAnnuity_pos`
  (annuity positivity discharged), **`cdsFairSpread_TV_balances`** (premium =
  protection iff `c = (1−R)·losses/annuity` — the pin's
  `cdsFairSpread_TV_cash_flow_balance` realized at the integrals),
  **`cdsFairSpread_TV_const`** (constant-λ regression: collapses to
  `cdsFairSpread λ R`), `defaultDensity_antideriv`
  (`∫₀^a h·S = 1 − S(a)`), `clockTail_eq_defaultDensity`
  (`∫₀^{Λa} e^{−y} dy = ∫₀^a h e^{−Λ}` — FTC on the shared antiderivative,
  no change-of-variables lemma), and
  **`cox_defaultProb_density`**: P(τ ≤ a) = ∫₀^a h·S — the density-pricing
  identity at r = 0.
- **Layer 5 (restricted Cox mixing — stretch, landed)**:
  `cox_mixing_survival` on the product of a path space with the exponential
  clock: (μ × Exp(1)){clock > Λ(path,t)} = ∫⁻ e^{−Λ(path,t)} — the tower
  identity E[E[1{τ>t}|path]] = E[e^{−Λ_t}] at the Fubini level, random Λ;
  `cox_mixing_survival_le` (it is a probability), `cox_mixed_survival`
  (packaged as a default-time survival; per-path inverse construction is the
  stated hypothesis).

Documented gaps (in the file header, per lesson 0032's scope fences): filtration
enlargement (general Cox) out of scope; the σ-algebra-level conditional
expectation (Doob–Dynkin) replaced by its Fubini content; the discounted density
identity E[e^{−rτ}1{τ≤T}] = ∫₀ᵀ e^{−rs} h S ds for r > 0 (needs generalized-
inverse continuity for substitution inside the integrand); the Girsanov
measure-change layer (`GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted`,
`GirsanovPredictableTheta.isExpQMartingale_BthetaPredictable`) cited for the
driven-intensity case, not exercised.

## HW calibration (lesson 0020, step 4) — `hw_scratch.lean`, landed 2026-10-11

Extension of `hw_scratch.lean` (steps 1–3) with the calibration step (queue item 16):
767 lines total, zero `sorry`, all `#print axioms` standard three. New declarations
(HW-5 section):

- `hwTheta f0 κ σ t := deriv f0 t + κ·f0 t + (σ²/2κ)(1 − e^{−2κt})` — the verified
  calibration identity (research addendum; Bagaria ch. 8). Defined with `deriv`;
  theorems bind `hf0 : ContDiff ℝ 1 f0` (packages differentiability + continuity of
  the derivative via `contDiff_one_iff_deriv`).
- `hwCalibAlpha` — the calibrated particular solution in closed form
  `β(t) = f(0,t) + (σ²/2κ²)(1 − e^{−κt})²`.
- `hwCalibAlpha_solves_ODE` — β′ = θ − κβ pointwise (the addendum's identity verified
  by differentiation; the pointwise core is `(1−E²) − (1−E)² = 2E(1−E)`).
- `hwCalibMean` — `hwDeterministic θ κ (f0 0) t = β t` (ODE uniqueness; β(0) = f(0,0)
  automatic). `hwCalibMean_eq_forward` — the law-level form
  𝔼[r_t] = f(0,t) + (σ²/2κ²)(1−e^{−κt})² (Gaussian mean via `integral_id_gaussianReal`).
- `hwVar_eq_interval` — `vasicekBondV κ T = ∫₀ᵀ B(u)² du` in interval form: reuses
  `vasicekIntegratedKernel_integral_sq` + the kernel reflection
  `g(u) = B(T−u)`, `∫₀ᵀ φ(u) = ∫₀ᵀ φ(T−u)` (`integral_comp_sub_left`).
- `hwCalibIntegratedMean` — `∫₀ᵀ α = ∫₀ᵀ f0 + (σ²/2)·V(T)` — the identity the
  repricing exactness lives on (the mean's convexity correction offsets σ²V/2).
- **`hw_reprices_curve`** (headline) — `P^hw(0,T) = exp(−∫₀ᵀ f(0,s) ds)`:
  `hwBondPrice_eq` + `hwCalibIntegratedMean`, the σ²V/2 cancels exactly.

Toolchain notes for future dispatches at this pin: `intervalIntegral.integral_const_mul`
is `*`-stated (not `•`); never `rw` with a lemma carrying metavariables against
`↑⟨T, hT⟩`-coercions — bind `𝕋 : ℝ≥0` variables instead (kabstract does not reduce
anonymous-constructor projections); `ring` does not cancel `κ⁻¹` against `κ` —
`field_simp` first. Elaboration-order gotcha: `Eq.trans (integral_add …) lemma`
fails where `refine Eq.trans … ?_; rw [← lemma (r := …) (f := …)]` succeeds.

## Heston 2D affine transform — item 19 (2026-10-13, first ZCode-subagent dispatch)

`heston_scratch.lean` — 794 lines, 41 declarations (29 public), zero `sorry`, 29/29
axiom lines standard-three (orchestrator re-verified; V-pass statement-fidelity diff
passed — the 0<u<1 strip restriction is Bagaria Thm 14.7's necessary moment strip,
numerically verified, documented). Contents: 2D exp-affine calculus (incl. the mixed
derivative), `hestonGenerator` + invariance (`LE = (c₀+c₁v)E`, x-coefficient ≡ 0),
ρ-shifted Riccati flows (`hestonGamma` = √((κ−ρξu)²+ξ²(u−u²)), `hestonBv`, `hestonA`,
both `hasDerivAt` flow facts + calendar flips), PDE headline (`hestonProfile_pde`
hypothesis-ODE + `hestonTransform_pde` closed form + terminal), gated expectation
residue as a proved implication. Bv-flow RE-DERIVED (no reusable engine member had
constant+quadratic+sign all matching); engine discipline extended with numeric/symbolic
pre-verification (ODE residuals via substitution; RK4 ≈ closed forms to 1e-17; ξ=0
degenerate case reproduces the Gaussian answer). Dispatch economics: 6.35M subagent
tokens, 57 tool calls, 42 min (glm-5.3 max via ZCode Agent tool).

---

# Build queue item 10 — Forward-eq stage 3, flux-form Fokker–Planck (lesson 0021/0054)

`ForwardEqScratch.lean` grown in place: 1,273 → 1,397 lines (+124, stage 1–2
byte-stable), landed 2026-10-13, zero `sorry`, standard-three axioms on both new
theorems (orchestrator re-verified). Build: `cd AmericanPutConvexity && lake env lean
../builds/lean/ForwardEqScratch.lean`. New public theorems:

- `forward_eq_timeDependent_flux` — ∂_t p = −∂_x(μ(t)·p) + ½ ∂²_x(σ(t)²·p): the
  divergence/flux form of the forward equation (Bagaria eq. 9.2, coefficients inside
  the derivatives), for the Gaussian p(t,x) = K(v t, x − m t) with differentiable
  mean/variance curves. Proof: stage 2's `forward_eq_timeDependent` plus the
  constant-coefficient product rule (`HasDerivAt.const_mul`, twice for ∂²).
- `forward_eq_convolution_timeDependent_flux` — the migration lemma in flux form;
  hypotheses identical to stage 2's `forward_eq_convolution_timeDependent`; re-runs the
  private `hasDerivAt_convDenGen_*` engine and transports across the product rule.

Route verdict (E-memo `memos/item10-memo.md`): Route B (flux form, t-only
coefficients); Route C (genuine (t,x)) rejected as hypothesis-echo — no non-Gaussian
density carrier exists in any clone; full Dupire stays gated on item-11-class
existence work. First ZCode-workflow dispatch: B = GLM-5.3 max (workflow `dwfrun-
f4592720`), independent V-fidelity diff = GLM-5.3 high, deterministic lake/sorry
gates; one builder escalation (orchestrator contract typo: σ² double-count + ill-typed
nesting) resolved to the delivered ½-outside form, which the orchestrator's V-pass
then verified term-by-term.

---

# Build queue item 11 — Gyöngy Thm 9.6 mimicry, gated (lesson 0038)

`GyongyScratch.lean` grown in place: 1,147 → 1,702 lines (+555, prefix byte-stable),
landed 2026-10-13, zero `sorry`, standard-three axioms on all four contracted theorems
(orchestrator re-verified; fidelity diff vs the QUEUE-stored contract PASSED). Build:
`cd AmericanPutConvexity && lake env lean ../builds/lean/GyongyScratch.lean`. New
public theorems (namespace `Gyongy`):

- `exists_driftCoeff_fn` / `exists_diffCoeffSq_fn` — Doob–Dynkin: the conditional-
  expectation coefficients are genuine Borel functions of X_t (pointwise
  `g = h ∘ f`; the program's first (t,x)-form coefficients).
- `marginal_flow_weak_equation_fn_constructed` — the constructed-process weak forward
  equation with composed coefficient functions â(t, X), b̂²(t, X).
- `gyongy_mimicry_gated` — Thm 9.6's one-time-marginal mimicry modulo the named gate:
  Y as data on its own space (Ω', ν), Y-side integrated forward identity `hyflow`,
  `HasLaw (Y 0) (μ.map (X 0)) ν`, and measure-flow uniqueness `hgate` ⇒
  ∫ f(Y_t) = ∫ f(X_t) on (0, T]. (Private engines: `exists_coeffFn_comp`,
  `constructedGenIntegrandExp_fn`, `hitoid_constructed_fn_Ioc`.)

Route verdict (memo `memos/item11-memo.md`): Route 3 (Euler-chain laws) rejected as
gated-on-air; strong existence for merely-Borel coefficients is false in general; the
Skorokhod/martingale-problem core is absent from every clone — the gate isolates
exactly that. First two-workflow item (E'/judgment `dwfrun-689d1d66`, B `dwfrun-
9152c50d`, both glm-5.3 max). Item-18 finding 4 corrected in NOTES.md (a.e.
modifications exist in-repo; the pointwise-all-ω shape does not;
`ItoIntegralProcessContinuousModification.lean` is HEAD-verified only and is banned
from build imports until pin-checked).

# Item 11 memo — E-pass substrate sweep: Gyöngy Thm 9.6 Y-existence (weak, non-Lipschitz coefficients)

E-pass (glm-max "Substrate explorer", read-only), 2026-10-13. Scope per the dispatch:
inventory what `GyongyScratch.lean` proves and what its `:203–205` gate actually blocks;
what the adapted-integrand machinery provides toward a construction; what Mathlib
existence machinery exists at this rev; whether the item-18 "no pathwise-continuous Itô
integral" finding blocks weak existence. All names below are grep-verified in the local
clones on 2026-10-13; line numbers are current file states. Read-only git was used only
for rev identification (`git -C <clone> log -1`), never for mutation.

## Headline verdict (the question the build must answer)

**Can a process Y with the Gyöngy conditional-expectation coefficients be constructed
at this pin, and in what sense?**

1. **Strong solution: NO — and mathematically false as a general target.** The Gyöngy
   coefficients `a = E[β_t | X_t = ·]`, `b² = E[δ_t² | X_t = ·]` are merely Borel
   (bounded) functions of `(t, x)`; strong existence for such coefficients fails in
   general (the classical reason Gyöngy's theorem is stated weakly). MathFin's only
   solver is Lipschitz-autonomous: `SDEExistence.picardMap` takes
   `b σ : ℝ → ℝ` with `LipschitzWith` (mathfin/MathFin/Foundations/SDEExistence.lean:82–89),
   contraction :95, solution :156 — and even there the deliverable is an `Lp`-class
   fixed point, not a path-level process. The `:203–205` gate stands.
2. **Weak solution (Skorokhod/Stroock–Varadhan): NOT landable at this pin — the gap is
   the analytic identification core, not the measure-construction machinery.** Verified
   absent from *every* clone (zero grep hits in two Mathlib revs): Komlós lemma,
   Skorokhod representation, martingale-problem machinery, Prokhorov compactness in the
   needed form (Portmanteau.lean has only `tendsto_of_forall_isCompact_of_isTightMeasureSet`,
   Mathlib/MeasureTheory/Measure/Portmanteau.lean:655). What *does* exist is
   everything around it: the Kolmogorov extension theorem (transitive dep of MathFin —
   see §1d), Ionescu–Tulcea trajectory measures (§1e), a fully constructed Brownian
   motion and Wiener measure (§1d), and Kolmogorov-continuity continuous modifications
   (§1b/§1d). Building the missing core is a research-scale project, not a queue item.
3. **Constructed-process mimicry / marginal-level Y: YES, in a gated sense — the honest
   deliverable.** The program already proves X's side of Thm 9.6 in full
   (`marginal_flow_weak_equation_constructed`, GyongyScratch.lean:1078). Item 11's
   landable content is (Route 1) upgrading the Ω-level conditional-expectation
   coefficients to genuine Borel coefficient *functions* via Doob–Dynkin, and (Route 2)
   assembling the mimicry theorem modulo an explicitly named flow-uniqueness gate —
   the item-19 `hestonTransform_expectation_gated` house pattern. This is exactly the
   boundary lesson 0038 records (:102–103: "Gated remainder: Y's existence with
   merely-measurable coefficients … and weak-uniqueness").

**Item-18 finding 4 (no pathwise-continuous Itô integral) does NOT block weak
existence — it blocks only the pointwise-all-ω shape of the current instance fields.**
Details and the refining discovery in §3.

---

## 1. Name inventory (verified, file:line)

### 1a. `builds/lean/GyongyScratch.lean` (1,147 lines; items 5/6 + dispatches 10–12 landed)

Namespace `Gyongy`. Imports `Mathlib` + `ItoContribution` (:6–7; the olean is built in
the AmericanPutConvexity clone, :8–10). What is proved, per the ask:

- The structure: `BoundedItoProcess` :249 (X, β, δ : ℝ → Ω → ℝ; filtration ℱ; bounds
  B, D; measurability/adaptedness/boundedness/**path-continuity fields** :259–273 —
  note `hXcont/hβcont/hδcont : ∀ ω, Continuous` are **all-ω**, and
  `hXadapted/hβadapted/hδadapted : ∀ t, StronglyMeasurable[ℱ t]` are **pointwise**).
- The conditioning σ-algebra and coefficients: `sigmaGen X t = Real.measurableSpace.comap (X t)` :306
  (literally the `mY.comap f` shape Doob–Dynkin consumes — no adapter needed);
  `sigmaGen_le` :310; `driftCoeff μ X β t := μ[β t | sigmaGen X t]` :317;
  `diffCoeffSq μ X δ t := μ[fun ω => δ t ω * δ t ω | sigmaGen X t]` :321.
- The engine: `tower_identity` :358 (`∫ h·g = ∫ h·μ[g | m]` for m-measurable h);
  `expectation_beta_eq_a` :406; `expectation_deltaSq_eq_b2` :416;
  `generatorIntegrand` :437; `continuous_marginal_integrand` :451 (the proved DCT
  interchange); `hasDerivAt_marginal_flow_core` :539 (private), `hasDerivAt_marginal_flow` :589;
  `time_derivative_marginals` :620; `marginal_flow_weak_equation` :645;
  `timeMeasure_Ioc_eq_interval` :680 (timeMeasure↔interval-integral bridge).
- The constructed instance: `reindexed` :752; `stronglyMeasurable_X_hXrel` :757;
  `constructedBoundedItoProcess` :781 (all structure fields derived from the assembly's
  data); `constructedGenIntegrandExp` :835 (+`_coe` :841, `private … _eq` :850);
  `hitoid_constructed_terminal` :924; `hitoid_constructed_band` :972 (dispatch-12
  discharged; needs only horizon-`T` pinning `hMeq`); **`marginal_flow_weak_equation_constructed`
  :1078** — for the constructed `X = c + ∫β + M` (reindexed to ℝ-time), on `t ∈ (0, ↑T)`:
  `d/dt 𝔼[f(X_{t⁺})] = 𝔼[f'(X_{t⁺})·a] + ½·𝔼[f''(X_{t⁺})·b²]` with `a = 𝔜[β_{⟨t⟩} | σ(X_{⟨t⟩})]`,
  `b² = 𝔜[δ²_{⟨t⟩} | σ(X_{⟨t⟩})]`. All `#print axioms`-audited at :1129–1146.
- **The gate itself** (:203–205): "Gated: the mimicking diffusion's *existence*
  (`dY = a(t,Y) dt + b(t,Y) dW` for merely measurable `a`, `b²`; MathFin's
  `SDEExistence.lean` Picard route needs Lipschitz coefficients, per
  `picardMap_contraction`) and the identification of `Y`'s marginals." What this gate
  *actually blocks* is only the second half of Thm 9.6 — producing/consuming a Y —
  **not** X's-side generator matching (fully landed). Note also the module docstring's
  uniqueness remark at :639–643: "uniqueness of the weak equation, not formalized here
  … that is the full content of Bagaria ch. 9 / Thm 9.6 modulo the *existence* of the
  mimicking diffusion".

### 1b. MathFin Itô-process construction chain (the "what can be constructed" inventory)

`mathfin/MathFin/Foundations/ItoIntegralProcessGeneral.lean` (at working HEAD b46e9b4):

- `itoProcessCLM (T t : ℝ≥0) (hBmeas) : Lp ℝ 2 (trimMeasure_T T) →L[ℝ] Lp ℝ 2 μ` :120 —
  the general adapted-integrand Itô integral as a CLM (`∫₀ᵗ φ dB` in L²).
- `itoProcessCLM_eq_condExpL2` :165 — `(φ●B)_t = condExpL2 𝓕_t (terminal)`: the process
  is the conditional-expectation projection of its terminal value.
- `itoProcessCLM_aeStronglyMeasurable` :188 — **a.e.**-adaptedness (not pointwise).
- `itoIntegralProcessGen_isMartingale` :200 — the L² martingale property.

`mathfin/MathFin/Foundations/ItoIntegralProcessContinuousModification.lean` —
**the refining discovery vs item-18 finding 4** (see §3):

- `itoContinuousMod` :235 — the pathwise-uniform limit of the approximating simple
  Itô integrals.
- `itoContinuousMod_tendsto` :244 — a.e. convergence, uniformly in `t ≤ T`.
- `itoContinuousMod_modification` :282 — for every `t ≤ T`,
  `itoContinuousMod φ t =ᵐ[μ] itoProcessCLM T t φ` (a genuine modification).
- `itoContinuousMod_continuousOn` :341 — `∀ᵐ ω, ContinuousOn (t ↦ itoContinuousMod φ t ω) (Icc 0 T)`.
- **`exists_continuous_modification_itoProcess`** :392 — ∃ a process that is a
  modification at every `t ≤ T` AND a.e. path-continuous on `[0,T]`.

`mathfin/MathFin/Foundations/SDEExistence.lean` (178 lines; the only SDE-solver in the
stack): `lipschitz_sub_const` :55, `lipComp` :64, `lipComp_sub_norm_le` :73,
`picardMap` :82 (autonomous Lipschitz `b σ : ℝ → ℝ` only), `picardMap_contraction` :95,
`picardMap_contractingWith` :140 (needs `T·L_b + √T·L_σ < 1`), `picardSolution` :156
(an Lp-class fixed point — not a path-level process),
`picardMap_exists_unique_fixedPoint` :167.

`AmericanPutConvexity/ItoContribution.lean` (6,702 lines) — the E-level identities the
Y-side mirror would reuse: `itoDrift_expectation_identity_adapted` :6039 (signature read:
hβadap/hβcont/hβbdd, hδ…, hMadap, hMeq, c, hXcont, hXrel, f-derivative chain + bounds ⇒
`∫ f(X_T) = ∫ f(X_0) + ∫_{(0,T]} (𝔼[f'·β] + ½𝔼[f''·δ²]) ∂timeMeasure`); the
cross-horizon block `itoProcessCLM_eq_terminal_of_ge` :1262, `itoIntegralCLM_cross_horizon`
:1285, `itoProcessCLM_consist` :1391, `mMeq_frozen` :1469; `driftPrim` :4155,
`driftPrim_adapted` :4209, `driftPrim_continuous` :4234. Port of the cross-horizon
block: `mathfin/MathFin/Foundations/ItoIntegralCrossHorizon.lean` (:172/:301).

### 1c. What Mathlib (both revs) has and lacks

Environment revs, verified read-only: workspace `mathlib4/` = master `2a88576`
(2026-09-30); mathfin's *packaged* mathlib (`.lake/packages/mathlib`, the one a
mathfin-rooted build sees) = `0434c03` (2026-07-24). Names below verified in **both**
unless marked.

Has (existence-adjacent):
- **Ionescu–Tulcea**: `ProbabilityTheory.trajMeasure (μ₀ : Measure (X 0))
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))` — a probability measure on
  `Π n, X n`, the infinite-trajectory law of a discrete-time process
  (`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:763` packaged / `:762` workspace
  clone). ℕ-indexed only — no continuous-time SDE consumption exists anywhere.
- **Kolmogorov continuity, definition level only**: `ProbabilityTheory.IsAEKolmogorovProcess`
  (`Mathlib/Probability/Process/Kolmogorov.lean:64`) + basic lemmas; the file is 185
  lines and contains **no continuous-modification existence theorem**.
- **Projective limits, definition level only**: `IsProjectiveMeasureFamily`
  (`Mathlib/MeasureTheory/Constructions/Projective.lean:45`), `IsProjectiveLimit` :115
  + uniqueness :150 — **no existence theorem** (`∃ μ, IsProjectiveLimit …` — zero grep
  hits). `Mathlib/Probability/BrownianMotion/GaussianProjectiveFamily.lean` builds the
  Brownian finite-dimensional family (`projectiveFamily` :81, projectivity :193) but
  constructs no limit.
- **Doob–Dynkin** (the Route-1 engine):
  `MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp [Nonempty Z]
  [TopologicalSpace Z] [IsCompletelyMetrizableSpace Z]
  (hg : StronglyMeasurable[mY.comap f] g) : ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f`
  (`Mathlib/MeasureTheory/Function/FactorsThrough.lean:56` workspace / `:57` packaged);
  `Measurable.exists_eq_measurable_comp` (Measurable/StandardBorel version)
  (`:77` workspace / `:78` packaged). Note `g = h ∘ f` is **pointwise**.
- `MeasureTheory.stronglyMeasurable_condExp : StronglyMeasurable[m] (μ[f | m])`
  (`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:187` both revs) —
  licenses applying Doob–Dynkin to `driftCoeff`/`diffCoeffSq` verbatim.
- `HasLaw` (`Mathlib/Probability/HasLaw.lean:39`, `map_eq : P.map X = μ`) and
  `IdentDistrib` (`Mathlib/Probability/IdentDistrib.lean:70`) — the vocabulary for the
  mimicry conclusion.
- Deterministic ODE existence: Picard–Lindelöf
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`
  (`Mathlib/Analysis/ODE/ExistUnique.lean:56`) — not SDE-relevant, listed for completeness.
- Weak-convergence vocabulary: `Mathlib/MeasureTheory/Measure/Portmanteau.lean`
  (`tendsto_of_forall_isCompact_of_isTightMeasureSet` :655);
  `LevyProkhorovMetric.lean`, `LevyConvergence.lean` exist (metric-level facts only).

Lacks (verified zero grep hits in both revs): Komlós lemma; Skorokhod representation;
martingale-problem machinery (`martingaleProblem` — 0 hits); measurable-selection
theorem of the Kuratowski–Ryll-Nardzewski shape (`measurableSelection` — 0 hits);
Wiener measure in Mathlib proper (`WienerMeasure` — 0 hits; lives in the clone, §1d);
any SDE existence (`stochastic differential` — 0 hits).

### 1d. The BrownianMotion clone — construction machinery *inside the mathfin build env*

MathFin's lakefile requires `BrownianMotion` from git at `314f04a` (2026-08-01,
lakefile.lean:82–84); that pinned copy sits materialized at
`mathfin/.lake/packages/BrownianMotion/` and is imported by the whole MathFin Itô chain
(`MathFin/Foundations/ItoIntegralL2.lean:10–12` imports
`BrownianMotion.Gaussian.BrownianMotion`). The workspace reference clone
`brownian-motion/` (`0d5b6eb`, 2026-09-22) is one commit-family ahead; line numbers
below are the **pinned package** (build-env truth), workspace-clone numbers in parens
where they differ:

- **`IsPreBrownianReal.exists_continuous_modification`** —
  `BrownianMotion/Gaussian/BrownianMotion.lean:230`: for ANY pre-Brownian process there
  exists a measurable, locally β-Hölder (β < 1/2) modification. The Kolmogorov-continuity
  payoff, available in-env.
- **A constructed Brownian motion exists**: `brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ` :562 :=
  `isPreBrownianReal_preBrownian.mk`; `isBrownianReal_brownian : IsBrownianReal brownian
  gaussianLimit` :580 — continuous paths (a.e.), all finite-dimensional laws.
- **`wienerMeasure : Measure C(ℝ≥0, ℝ)`** :804 (workspace clone :805) := the pushforward
  of `gaussianLimit` along the continuous-modification embedding — the Wiener measure on
  the path space, in-env.
- `gaussianLimit : Measure (ℝ≥0 → ℝ)` — `BrownianMotion/Gaussian/ProjectiveLimit.lean:181`,
  with `isProjectiveLimit_gaussianLimit` :188 — the law of the whole pre-Brownian path,
  **built via the Kolmogorov extension theorem**:
- which lives one dep deeper: `kolmogorov_extension4` (RemyDegenne; required by
  BrownianMotion's lakefile, present at `mathfin/.lake/packages/kolmogorov_extension4/`)
  — `KolmogorovExtension4.projectiveLimit` (KolmogorovExtension.lean:128) and
  `isProjectiveLimit_projectiveLimit (hP : IsProjectiveMeasureFamily P)` :139. **The
  Kolmogorov extension theorem is therefore transitively importable in the mathfin env**
  (Mathlib proper lacks it, §1c).
- Provenance note (verified): Mathlib's own `Probability/BrownianMotion/Basic.lean`
  (defines `IsPreBrownianReal`, packaged rev :76) is an **orphan file** — it is wired
  into no root import graph in either rev (zero importers), so the `IsPreBrownianReal`
  the builds resolve is the clone's; no name clash occurs in the env.

### 1e. Ch09 / lesson anchors (the statement's source)

- Thm 9.6 (Gyöngy): `resources/fixed-income-notes-chapters/scans/ch09-scan.md:42–45` —
  "for dX = βdt + δdW (bounded, adapted, not necessarily Markov), the Markov diffusion
  with a(t,x) = E[β_t | X_t=x], b²(t,x) = E[δ_t² | X_t=x] has the same one-time
  marginals; proof = tower property on E[f'(X_t)β_t]".
- Lesson 0038 (`mdbook/src/lessons/0038-tier3-gyongy-mimicry.md`): theorem statement
  :18–28; "No SDE-existence theory is needed — Y's SDE can be left weak (an expectation
  characterization suffices for the mimicry conclusion, which is distributional)" :61–65;
  build status :73–107; gated remainder :102–103.
- NOTES.md item-18 finding 4: `mdbook/src/NOTES.md:475–479`.
- Item-10 memo (`builds/lean/memos/item10-memo.md`): Route-C vacuity warning :335–341;
  Conflict 3 (no non-Gaussian density carrier; `SDEExistence.picardMap` :82 note)
  :357–365; §1b SDEExistence note :193–198.
- ROUTING.md escalation clause 1 (greenfield ⇒ glm exploration — this pass): :34–38;
  item-11 row QUEUE.md:40.

## 2. What item 18's finding blocks — refinement

NOTES.md:475–479 records: "No pathwise-continuous Itô-integral version exists at the pin
(`hXcont`/`hMadap` never discharged in-repo; continuity lemmas are L²-norm only) — so
continuous-path/natFiltration-adapted Itô-integral constructions are not landable."

**The first clause is imprecise; the conclusion needs re-scoping.** What exists in-repo
at mathfin working HEAD (§1b): `itoContinuousMod` with a.e. path-continuity
(`itoContinuousMod_continuousOn`, :341) and the packaged existence theorem
`exists_continuous_modification_itoProcess` (:392). What is genuinely true in the
finding: the **pointwise-all-ω** continuity fields (`hXcont : ∀ ω, Continuous`,
GyongyScratch.lean:271–273) and the **pointwise** adaptedness fields
(`hMadap : ∀ t, StronglyMeasurable[𝓕_t]`, :265–267) are never discharged in-repo —
the modification machinery delivers `∀ᵐ ω` continuity and a.e.-measurability only
(`itoProcessCLM_aeStronglyMeasurable` :188). Redefining on the null set restores all-ω
continuity but not pointwise `StronglyMeasurable`-ness against the uncompleted natural
filtration.

**Consequence for item 11:** weak-existence-shaped statements are NOT blocked — they
should simply be phrased at the a.e. level, exactly as `IsBrownianReal` is
(`cont : ∀ᵐ ω ∂P, Continuous (X · ω)`, clone Basic.lean :302–305 area; the
`exists_continuous_modification` :230 route). A Y-package stated with all-ω fields would
re-hit the same wall GyongyScratch's instance hypothesizes. This is a
statement-judgment input for the S-pass, not a blocker.

## 3. Candidate routes (through verified substrate only)

**Route 1 — coefficient-function upgrade (the Doob–Dynkin landing; small, fully proved,
no Y needed).**
Deliverable shape:
1. `gyongyDriftFn`-existence: `∀ t, ∃ a : ℝ → ℝ, Measurable a ∧
   driftCoeff μ P.X P.β t = fun ω => a (P.X t ω)` (and the `b²` twin) — via
   `stronglyMeasurable_condExp` (ConditionalExpectation/Basic.lean:187) +
   `StronglyMeasurable.exists_eq_measurable_comp` (FactorsThrough.lean:56) applied to
   `sigmaGen = comap` (GyongyScratch :306): the fit is exact, `Z := ℝ` is nonempty +
   completely metrizable, and the factorization is **pointwise** (`g = h ∘ f`), so the
   transfer into the proved identities is `funext`-level. Range-side bounds
   (`∀ x ∈ range (X t), |a x| ≤ B`) follow from the condExp's a.e. bound.
2. `marginal_flow_weak_equation_fn_constructed`: the headline :1078 with
   `driftCoeff`/`diffCoeffSq` replaced by the composed Borel functions
   `â(t, X_{t⁺})`, `b̂²(t, X_{t⁺})` — i.e. Thm 9.6's generator with **deterministic
   coefficient functions**, the first time the program states the (t,x)-form.
   Substrate reused: :317/:321, :358, :406/:416, :1078. Genuinely new: the two
   Doob–Dynkin instantiations + the congruence transfer. Zero new analytic inputs.

**Route 2 — gated constructed-process mimicry (the honest Thm 9.6; RECOMMENDED headline).**
Deliverable shape: `gyongy_mimicry_gated` — given
(i) the constructed X (as in :1078) with its Route-1 coefficient functions (â, b̂²);
(ii) a **mimicking-process package** Y carried as data: a `BoundedItoProcess`-shaped
Y (possibly on another space) with composed coefficients `β^Y_t = â(t, Y_t)`,
`δ^Y_t = b̂(t, Y_t)` (the "constructed-process mimicry" sense — Y's existence is the
data, exactly what the :203–205 gate isolates), the Y-side Itô-drift identity (hitoid^Y
shape — discharged via the `ItoContribution.itoDrift_expectation_identity_adapted`
:6039 chain if Y is constructed, carried as a field otherwise), and
`Y₀ =ᵐ X₀` (`HasLaw` form, HasLaw.lean:39);
(iii) the **flow-uniqueness gate** — uniqueness of measure-flow solutions of the
deterministic-coefficient weak forward equation `∂_t ∫f dν_t =
∫(f'·â(t,·) + ½f''·b̂²(t,·)) dν_t` from the same initial law (the test-function form of
martingale-problem uniqueness — the analytic core that is NOT in any clone, §1c);
conclude `∀ t ∈ (0, ↑T), ∀ f (C², bounded-derivative class), ∫ f(Y_t) = ∫ f(X_t)` —
the one-time-marginals mimicry of Thm 9.6, optionally packaged as `HasLaw (Y t)
(μ.map (X t))`.
The assembly step is honest work, not vacuity-echo: after Route 1, the generator RHS
depends only on the current one-time marginal, so both flows solve the *same*
measure-level equation and the gate converts two equal-derivative flows into equal
marginals (FTC assembly on `t ↦ ∫f dμ_t − ∫f dν_t`). Substrate reused: everything of
Route 1 + the Y-side mirror of the Matching/Flow sections (mechanical reuse of :358/:406/:416
against Y) + :1078. Genuinely new: the Y-side mirror, the flow-of-measures packaging,
and the gate⇒marginals theorem. Statement-judgment flags for S: (a) Y's t-sections —
the constructed-Y route via :6039 needs `t ↦ β^Y_t` path-continuous, i.e. continuous
t-sections of â (carried as data; the classical theorem has measurability in t and an
a.e.-t conclusion — the price of the pathwise DCT machinery, record honestly);
(b) a.e.-vs-pointwise field level per §2 — recommend a.e.-level Y fields.

**Route 3 — Euler-chain laws via Ionescu–Tulcea (partial construction; stretch/judgment).**
Deliverable shape: `eulerChain_measure_exists` — for each dyadic partition of [0,T],
construct the Euler-chain law as `ProbabilityTheory.trajMeasure ν₀ κ_n` (Traj.lean:763)
with Gaussian transition kernels frozen at (â(t_k,x), b̂²(t_k,x)) (measurable in x by
Route 1; Gaussian kernels from `gaussianReal`-machinery, cf. the clone's
`gaussianProjectiveFamily` :67) — a genuine, non-trivial (t,x)-dependent construction
at the discrete-process level; plus the per-step fourth-moment bound
`𝔼|ΔY|⁴ ≤ C·Δ²` (the Kolmogorov-continuity input; provable from Gaussian central
moments) recorded as the tightness evidence; plus the **gate**: weak convergence of the
Euler laws + martingale-problem identification ⇒ a weak solution Y exists (stated, not
proved — the identification core is absent from every clone, §1c).
Warning for S (item-10 Route-C precedent, item10-memo :335–341): the gate carries
essentially all the analytic difficulty; Route 3 is hypothesis-echo-prone. Its
non-vacuous core is the Euler-law construction itself — land it only if that object is
judged worth carrying; otherwise reject as gated-on-air.

**Recommendation:** build Route 1 as the engine + Route 2 as the headline (this is
"Thm 9.6 modulo the isolated analytic core" — matching lesson 0038's recorded boundary
and the item-19 gated-implication pattern); treat Route 3 as rejected-by-default unless
the S-pass explicitly wants the discrete construction.

## 4. Conflicts

1. **Item-18 finding 4 vs in-repo continuous-modification theorems.** NOTES.md:475–479
   ("continuity lemmas are L²-norm only", "not landable") is contradicted at mathfin
   HEAD by `itoContinuousMod_continuousOn` (:341) and
   `exists_continuous_modification_itoProcess` (:392), and in the pinned BrownianMotion
   package by `IsPreBrownianReal.exists_continuous_modification` (:230). Resolution
   offered in §2: the finding is correct for the pointwise-all-ω +
   pointwise-`StronglyMeasurable` field shape; incorrect as stated about a.e.
   modifications. The NOTES.md wording should be corrected at V-pass.
2. **Pin-status of the mathfin continuous-modification file.**
   `ItoIntegralProcessContinuousModification.lean` is verified at working HEAD b46e9b4
   only; its presence at pin 784a831 is unverified (read-only; no checkout).
   Circumstantial: QUEUE.md's pinned-rev map (:13–23) does not name it, and item-10's
   memo cites `SDEExistence.lean` (which `open`s its namespace, :48) without pin
   qualification. Any B-pass consuming it must pin-check first (or grow from GyongyScratch,
   which does not import it).
3. **Rev skew across the three Mathlib faces.** workspace `mathlib4/` (2a88576) ≠
   mathfin packaged mathlib (0434c03) ≠ the QUEUE "pin" convention. All Route-1/2 names
   were verified in BOTH mathlib revs (§1c); the clone-dependent names (§1d) are cited
   at the pinned package. Line numbers shift by ±1 between revs where noted.
4. **GyongyScratch import-root split (inherited from item 10, Conflict 6):** the file
   roots at the AmericanPutConvexity-built `ItoContribution` olean; a Route-2 file
   consuming BOTH GyongyScratch and MathFin-side machinery keeps that root; the
   BrownianMotion-package names (§1d) are transitively visible through MathFin's import
   of the clone — but NOT through `import Mathlib` alone (Mathlib's own
   Probability/BrownianMotion/Basic.lean is an orphan file, §1d).

## 5. Unknowns (not failures)

- Whether `ItoIntegralProcessContinuousModification.lean` and the whole §1d clone chain
  compile/resolve at the QUEUE pin 784a831 (only HEAD b46e9b4 / pinned package 314f04a
  verified by grep; no lake build was run in this pass — read-only E-pass).
- Whether the S-pass wants Y on the *same* space (strong-form data) or an abstract
  space (weak-form data) in Route 2 — a statement-judgment call flagged, not resolved
  here; the mathematics permits only the data-carried form either way at this pin.
- The exact `IsBrownianReal`-level SDE predicate a future weak-existence theorem would
  use (no existing shape to cite — greenfield); Route 2 deliberately avoids committing
  to one by carrying Y as `BoundedItoProcess`-shaped data.
- `kolmogorov_extension4`'s exact API surface beyond `projectiveLimit`/:139 (only the
  two Route-3-relevant declarations were read; the package is small but not fully
  swept).
- Whether any Brownian-motion-clone StochasticIntegral layer (beyond SimpleProcess/L2M,
  which MathFin already imports) contains an SDE-existence result — not swept beyond
  the Gaussian/ directory (Route 3's rejection does not depend on it, since the
  martingale-problem identification core is verified absent from Mathlib itself).

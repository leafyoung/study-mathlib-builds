# Stub 0054 memo — E-pass: can "The semigroup and the adjoint" flip?

E-pass (flash-explorer, read-only), 2026-10-14. Scope per dispatch: stub
`mdbook/src/lessons/0054-the-semigroup-and-the-adjoint.md`, scan ledger
`resources/fixed-income-notes-chapters/scans/ch03-scan.md`, the chapter PDF
(`ch03-the-generator.pdf` — note: the dispatch's filename
`ch03-the-generator-semigroup-adjoint.pdf` does not exist; the actual split file is
`ch03-the-generator.pdf`), and the landed substrate `builds/lean/ForwardEqScratch.lean`
(items 7/8/10) + `FeynmanKacHeatEquation.lean`. All names below grep-verified this
pass; **build face first** (`AmericanPutConvexity/.lake/packages/`), per the
name-verification convention.

---

## 1. Verdict: **full-with-scope-cut**

The stub's BLOCKED reason (:3–5, "the forward (adjoint / Fokker–Planck) side is
absent from the stack") is now **false**: the forward half of ch. 3 is landed as six
public theorems in `builds/lean/ForwardEqScratch.lean` (1,397 lines, zero `sorry`,
`#print axioms` audit block at :1380–1396; item 10 **DONE** per
`builds/lean/QUEUE.md:51`, "both new theorems standard-three, orchestrator
re-verified"; landing record `mdbook/src/NOTES.md:551–566`). The driftless backward
instance of eq. 3.6 is landed in `FeynmanKacHeatEquation.lean`. A FULL 0054 can teach
the forward/adjoint story spine-first from proved content.

But the semigroup-object half of the stub's blocker stands, freshly grep-confirmed:
**zero** hits for any semigroup/P_t-object/composition definition across the
build-face `MathFin/MathFin/`, `ForwardEqScratch.lean`, and `GyongyScratch.lean`
(grep `def .*[Ss]emigroup|semigroupProperty|Pt_comp|semigroup_prop`: no hits), and
zero hits for any `L*`/adjoint-of-generator/FokkerPlanck object in build-face MathFin
(grep `generatorAdjoint|Lstar|L_star|fokkerPlanck|FokkerPlanck`: no hits). QUEUE.md:51
says exactly this: "Lesson 0054 build-seed refreshed (**stub remains BLOCKED on the
semigroup object**)". So the flip carries a still-gated section (P_t object, semigroup
composition, operator-level parameter-differentiation assembly, genuinely (t,x)
coefficients) — a scope cut against the stub's own path-to-unblock (:80–90), which
wanted the composition *proved*, not merely taught.

Precedent for the shape: lesson 0053 (FULL) teaches Dynkin's formula as chapter math
while stating "Dynkin is absent from Mathlib — a small build to budget"
(`0053-the-generator-as-definition.md:96–97`). The same honesty pattern covers the
unproved halves here. If the orchestrator instead rules that chapter-math-only
coverage satisfies the item completely, the same skeleton supports full-now — the
difference is only whether §3.2's assembly sections are marked gated (registry row
stays ◐) or complete-as-chapter-math. Recommendation: full-with-scope-cut, registry
row 0054 stays ◐ with the blocker column rewritten to the residual gate.

## 2. Proved content the flipped lesson can teach (landed names, file:line)

### 2a. The forward equation — eq. 3.11 (∂_t p = L* p) and eq. 3.8's divergence form

All in `builds/lean/ForwardEqScratch.lean`, namespace `ForwardEqScratch`, imports
`Mathlib` + `MathFin.Foundations.FeynmanKacHeatEquation` (:1–2). **Line-number
corrections to the dispatch**: the flux-form theorems sit at **:1269** and **:1310**
(the dispatch's :1268/:1309 are their docstring lines; the other four match exactly).

| Landed theorem | Statement (verified this pass) | Chapter eq. |
|---|---|---|
| `heatKernel_heat` :132 | ∂_t K = ½ ∂²_y K for the heat kernel (deriv form) | the kernel PDE under eq. 3.11 driftless |
| `forward_eq_driftless` :247 | ∂_t p = (σ²/2)·∂²_x p for pden 0 σ x₀ | eq. 3.11, μ = 0 |
| `forward_eq_constant_drift` :229 | ∂_t p = −μ·∂_x p + (σ²/2)·∂²_x p, proved directly | eq. 3.11 with eq. 3.2's constant-coefficient L* read outside the derivatives |
| `forward_eq_timeDependent` :754 | same for p(t,x) = K(v t, x − m t), deterministic curves with m' = μ, v' = σ², v t > 0 | eq. 3.11, t-dependent coefficients |
| `forward_eq_timeDependent_flux` :1269 | ∂_t p = **−∂_x(μ(t)·p) + ½ ∂²_x(σ(t)²·p)** — coefficients *inside* the spatial derivatives | **eq. 3.8's RHS + eq. 3.11 combined** (Bagaria eq. 9.2's divergence shape; file's own stage-3 banner :1248–1261 cites it) |
| `forward_eq_convolution` :661 | the equation migrates through u(t,x) = ∫_{[a,b]} g(y)·p(t, x−y) dy (g continuous, \|g\| ≤ Cg) | eq. 3.11 at the level of the pairing ⟨g, p_t⟩ — the semigroup-smoothing move of ch. 3's domain discussion |
| `forward_eq_convolution_timeDependent` :1210 | migration lemma, time-dependent coefficients (hypotheses on the band Icc (t/2) (3t/2)) | as above |
| `forward_eq_convolution_timeDependent_flux` :1310 | migration lemma in the divergence form | eq. 3.11 + eq. 3.8, migrated |

Supporting public names (same file): `pden`/`pdenx`/`pdenxx` :162/:166/:171 with
`hasDerivAt_pden_t` :177, `hasDerivAt_pden_x` :195, `hasDerivAt_pdenx_x` :203;
`pden_zero_drift_eq_gaussianPDFReal` :256 (bridge to Mathlib's `gaussianPDFReal`);
`pdenGen` :705 with `hasDerivAt_pdenGen_t` :735; `convDen` :269 / `convDenGen` :790;
`forward_eq_timeDependent_constant` :773 (stage-2→stage-1 definitional collapse).

Honest scope markers the lesson must carry (from the file's own docstrings, :1263–1268
and :1301–1309, and the stage-3 banner :1253–1261): coefficients are **t-only**,
entering through their primitives m, v; the flux form is proved *from the non-flux
form via the constant-coefficient product rule* (`HasDerivAt.const_mul`, :1277–1288)
— algebraically equivalent at t-only coefficients, landing the *statement form* that a
genuine-(t,x) build generalizes.

### 2b. The driftless backward side — eq. 3.6's one proved instance

All in `AmericanPutConvexity/.lake/packages/MathFin/MathFin/Foundations/
FeynmanKacHeatEquation.lean` (module `MathFin.Foundations.FeynmanKacHeatEquation`).
**The build-face and working-clone copies are byte-identical** (md5
`025275e3f47fa3d8fe9a601f4b9e7ffd` both — checked this pass), so the stub's
mathfin-tree path cites are face-safe.

- `feynmanU` :828 — u(t,x) = ∫ h(z)·K(t, z−x) dz; `feynmanU_eq_integral_of_map` :852;
  **`feynmanU_eq_expectation` :888 — the (P_t g)(x) = E^x[g(X_t)] reading (eq. 3.5)
  for BM, as a kernel family**.
- `hasDerivAt_feynmanU_t` :1006, `hasDerivAt_feynmanU_x` :1057,
  `hasDerivAt_feynmanU_xx` :1113, `hasDerivAt_feynmanU_comp` :1194.
- `feynmanU_heat_equation` :1304 — with the three derivative lemmas this reads
  ∂_t u = ½ ∂²_x u: **eq. 3.6 proved for L = ½∂²_x, no Itô** (exactly how lesson 0053:127–134
  and lesson 0026 already present it).
- `heatConvolution_eq_add_integral_deriv` :768 — the driftless FK identity
  ∫f·K = f 0 + ∫₀ᵗ ½∫f″·K (the Duhamel/`P_t = I + ∫ L`-flavored identity, ch. 3's
  "evolve the function" reading).

Cite the heat-equation content as "the three `hasDerivAt_feynmanU_*` lemmas +
`feynmanU_heat_equation`" (the raw :1304 statement is the integral identity
∫h·K·((z−x)²−t)/(2t²) = ½∫h·K·((z−x)²−t)/t²; the PDE reading is the combination —
0053's precedent, do not overstate the single theorem).

### 2c. Backward infinitesimal side + Markov raw material (stub's own anchors, all live)

- `itoDrift` (`ItoLemma.lean:80`), `itoDrift2D` (`ItoLemma2D.lean:120`),
  `bsItoDrift` (`PDEFromIto.lean:103`), `bs_pde_from_no_arbitrage` (:117) — all in the
  build-face MathFin (lesson 0053's anchors).
- `shift_indep_natural` (`BrownianMarkov.lean:54`), `brownian_markov_property`
  (:67) — build-face MathFin; axiom-audited standard-three
  (`AxiomAuditGen.lean:242–243`). This is the proved raw material Prop 3.5's proof
  needs (tower + fresh shifted process) — the lesson can name what exists without
  claiming the composition.
- `lognormalTerminalPDF` (`BreedenLitzenberger.lean:66`), `breedenLitzenberger`,
  `lognormalTerminalPDF_nonneg` (build-face) — the one non-Gaussian-flavored density
  object (still lognormal, i.e. Gaussian in log-coordinates: reinforces the
  density-carrier gate).
- Hilbert-adjoint substrate `mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
  — exists in the build face (substrate only; L is unbounded).

### 2d. Adjacent chain (mention with a chain caveat, do not rest content on it)

`builds/lean/GyongyScratch.lean` (now 1,702 lines) has the **weak/test-function**
forward equation for the constructed Gyöngy process:
`marginal_flow_weak_equation_constructed` :1078 (plus the newer function-form
`exists_driftCoeff_fn` :1210, `exists_diffCoeffSq_fn` :1242,
`marginal_flow_weak_equation_fn_constructed` :1281, `gyongy_mimicry_gated` :1516).
This is the first half of Calculation 3.10's derivation (d/dt E[f(X_t)] tested against
f) — but it imports `ItoContribution` (AmericanPutConvexity-rooted olean), a different
build chain from ForwardEqScratch (item10-memo Conflict 6). A flipped 0054 should
cite it as the weak-form precedent, clearly marked as a separate root.

## 3. What stays gated (honest boundary, quoted)

1. **The P_t object and semigroup composition (eq. 3.5 as an operator, Prop 3.5).**
   QUEUE.md:51: "stub remains BLOCKED on the semigroup object". Stub :46–48: "No
   $P_t$ object exists: FeynmanKacHeatEquation proves one PDE for one $u$; it never
   defines the operator, composes it ($P_{t+s} = P_s P_t$), or differentiates in the
   start time". Freshly confirmed: zero semigroup/composition definitions in
   build-face MathFin + both scratch files (grep this pass).
2. **Operator-level parameter differentiation (eq. 3.6's two readings, ∂_t P_t f =
   L P_t f = P_t L f as operator statements).** Stub :48–49: "extracting ∂_t P_t f
   needs parameter differentiation under the expectation, the same missing assembly
   lesson 0021 flags for Dupire". Refinement the flip must state precisely:
   per-family parameter differentiation under the integral **is** proved
   (`hasDerivAt_integral_mul_kernelFamily`, FeynmanKacHeatEquation :595 — used by
   `hasDerivAt_feynmanU_t`; `hasDerivAt_integral_of_dominated_loc_of_deriv_le` — the
   ForwardEqScratch migration engine); what is gated is the *operator-level assembly*
   on a P_t object, and the x-parameter differentiation of a non-Gaussian density.
3. **The L* operator object (eq. 3.7 via integration by parts), boundary
   cancellation (eq. 3.9), the flux object J (eq. 3.10) as a defined Lean object.**
   Zero hits for any generator-adjoint/FokkerPlanck object in build-face MathFin
   (grep this pass). The divergence-form *conclusion* is proved (:1269/:1310); the
   pairing-and-IBP *derivation* is not.
4. **Genuinely (t,x)-dependent coefficients — full Dupire.** Stub :74–77: "gated on a
   non-Gaussian density carrier, which no clone has; see
   `builds/lean/memos/item10-memo.md`, Route C verdict". Item10-memo Route C
   (:339–341): "without a construction of u the statement is in danger of being
   vacuous (hypothesis-echo)". Item10-memo Conflict 3: "the only density objects in
   the program are Gaussian (`pden` :162, `pdenGen` :705 = shifted heat kernels); a
   (t,x)-dependent diffusion's density is not Gaussian … and no density-existence
   machinery for non-Gaussian laws exists in any clone". NOTES.md:564–566: "Route A's
   weak-form equation already landed (`Gyongy.marginal_flow_weak_equation_constructed`).
   Full Dupire (Thm 9.5's derivation, pointwise in x) stays gated behind item-11-class
   Y-existence/density work."
5. **Hille–Yosida resolvent, contraction, duality (eq. 3.12), mass balance /
   first passage** — chapter math only; scan ledger :86–87 already records
   "semigroup e^{tL} / Hille–Yosida, Fokker–Planck / flux — none found in the clones"
   (still true for the operator-theory half; the FP equation half of that sentence is
   now outdated, see §6).

## 4. Chapter anchors (PDF pp.; printed page = PDF page, offset +0)

From `pdftotext resources/fixed-income-notes-chapters/ch03-the-generator.pdf` (run
this pass; page boundaries located via the running headers in the text stream):

- §3.2 The Semigroup, pp. 53–55: Def 3.4 (Markov property, time-homogeneous form
  E[f(X_t)|F_s] = (P_{t−s}f)(X_s)) p. 53; **eq. 3.5 (P_t f)(x) = E^x[f(X_t)]** p. 53;
  **Prop 3.5** (P_{t+s} = P_s P_t) statement p. 53, proof + "not a consequence … it is
  what being Markov says" pp. 53–54; contraction ‖P_t g‖_∞ ≤ ‖g‖_∞ p. 54;
  **Prop 3.6 / eq. 3.6** (∂_t P_t f = L P_t f = P_t L f) p. 54; P_t = e^{tL} p. 54;
  Hille–Yosida + resolvent-as-perpetuity (Laplace transform formula) p. 55.
- §3.3 The Adjoint, pp. 55–59: **Def 3.7 / eq. 3.7** (⟨Lf, p⟩ = ⟨f, L*p⟩ under
  ⟨f,p⟩ = ∫ f p dx) p. 56; **Calc 3.8 / eq. 3.8** (L*p = −∂_x[μp] + ½∂²_x[σ²p], by
  IBP with boundary terms kept) p. 56; **eq. 3.9** (boundary cancellation, −f·J[p]
  bracket) p. 56; **Def 3.9 / eq. 3.10** (J[p] = μp − ∂_x[½σ²p], L*p = −∂_x J[p]) p. 56;
  mass balance d/dt ∫₀^∞ p dx = J(t, 0), reflecting J = 0 / absorbing J < 0 /
  first-passage reading p. 57; "inside or outside is the whole difference"
  (products rule: ∂_x[μp] = μ∂_x p + p ∂_x μ) pp. 57–58; **Calc 3.10 / eq. 3.11**
  (∂_t p = L*p, "in two lines") p. 58; backward/forward table p. 58;
  **eq. 3.12** (⟨f, p_T⟩ = ⟨P_T f, p_0⟩) p. 58; **Fig 3.1** (duality numerical,
  0.4437028414 both ways) p. 59.
- §3.4 What to Carry Forward, p. 60.

The stub's equation numbering is accurate against the PDF (eqs. 3.5–3.12 all match;
no stale equation references). Note the PDF uses two counters: Calculation 3.10
contains equation (3.11); Definition 3.9 contains equation (3.10).

## 5. Skeleton for the flipped lesson (0053-style FULL)

Format per conventions: H1 → **Goal:** → Motivate → Establish sections →
ask-your-tutor admonish → Connect → Primary source → Exercises → Answers. Style
model: `0053` (this lesson's sibling; same chapter, adjacent equations).

1. **H1 + Goal** — verify Bagaria ch. 3.2–3.3's pair: one operator seen from two
   sides — backward on functions of the state (the semigroup, eq. 3.5/3.6), forward
   on densities (the adjoint, eqs. 3.7–3.11) — and map each piece onto the proved
   forward-equation build and the driftless backward instance.
2. **Motivate** — 0053 left the generator as a definition ("the drift of f(X)");
   this lesson runs it both directions and shows integration by parts is the only
   thing separating the two (chapter's own framing, p. 50, 58). Feeds 0021's Dupire
   (forward side) and 0058's sequencing (coverage-map row).
3. **Establish — the semigroup is the Markov property written with operators**
   (eq. 3.5 p. 53; Prop 3.5 pp. 53–54; Def 3.4). Chapter math for the object and the
   composition proof; stack anchors: `brownian_markov_property`/`shift_indep_natural`
   (BrownianMarkov.lean:67/:54, axiom-audited) as the proved Markov raw material, and
   `feynmanU` + `feynmanU_eq_expectation` (FeynmanKacHeatEquation.lean:828/:888) as
   the driftless kernel realization of (P_t g)(x) = E[g(x+B_t)]. Honest marker: no
   P_t operator object exists; P_{t+s} = P_s∘P_t is not formalized (gate §3.1 above;
   keep the stub's attempt-exercise as an Exercise).
4. **Establish — the backward equation, one proved instance** (eq. 3.6 p. 54;
   P_t = e^{tL} p. 54; contraction p. 54; resolvent-as-perpetuity p. 55). Proved:
   ∂_t u = ½∂²_x u for u = feynmanU via `hasDerivAt_feynmanU_t/_xx` (:1006/:1113) +
   `feynmanU_heat_equation` (:1304) — eq. 3.6 for L = ½∂²_x, no Itô (0053's reading).
   Chapter math: both readings (evolve the function vs the starting point), the
   exponential notation, Hille–Yosida. Honest marker: no operator-level statement;
   contraction/resolvent not in the stack.
5. **Establish — the adjoint: the coefficients move inside** (eq. 3.7 p. 56; Calc
   3.8/eq. 3.8 p. 56; eq. 3.9; Def 3.9/eq. 3.10 p. 56; the ∂_x[μp] = μ∂_x p + p ∂_x μ
   remark pp. 57–58). Chapter derivation by IBP with boundary terms kept; the flux
   reading L*p = −∂_x J[p] and the boundary dictionary (reflecting = J = 0 =
   insulated wall; absorbing = Dirichlet = sink; 0026's Dirichlet/Neumann half-line
   uniqueness as the formal precedent). Stack anchor: the proved divergence-form
   conclusion −∂_x(μ(t)·p) + ½∂²_x(σ(t)²·p) in `forward_eq_timeDependent_flux`
   (:1269) is eq. 3.8-inside-eq. 3.11's shape for the Gaussian family. Honest
   markers: no ⟨·,·⟩-pairing adjoint theorem, no J object, no IBP-derived L*.
6. **Establish — the forward equation, proved for the Gaussian family** (Calc
   3.10/eq. 3.11 p. 58). The six-theorem ladder as the spine:
   `heatKernel_heat` :132 → `forward_eq_driftless` :247 →
   `forward_eq_constant_drift` :229 (transport + heat) → `forward_eq_timeDependent`
   :754 (deterministic mean/variance curves) → `forward_eq_timeDependent_flux`
   :1269 (coefficients inside — eq. 3.8's shape); migration lemmas
   `forward_eq_convolution` :661 / `forward_eq_convolution_timeDependent` :1210 /
   `forward_eq_convolution_timeDependent_flux` :1310 — the equation survives
   convolution against any continuous bounded compactly-supported g, i.e. it holds at
   the level of the pairings the duality uses. DCT engine named:
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with explicit Gaussian-polynomial
   domination. Honest markers: t-only coefficients through primitives m, v; flux form
   proved from the product rule (equivalent at t-only coefficients); genuine (t,x)
   coefficients gated (quote §3.4 above). Optional pointer: the weak/test-function
   form d/dt E[f(X_t)] = E[a f' + ½ b² f''] exists in the separate Gyöngy chain
   (`marginal_flow_weak_equation_constructed`, GyongyScratch.lean:1078 — different
   import root).
7. **Establish — the duality and mass balance: what they would need** (eq. 3.12 p.
   58; Fig 3.1 p. 59; mass balance p. 57). Chapter math, desk framing (one payoff /
   many starts → backward; many payoffs / one start → forward — why Dupire lives in
   L*). Honest column: duality theorem not formalized; mass balance/first-passage
   nothing landed; the missing pieces are exactly the gated §3 items.
8. **Ask-your-tutor admonish** — e.g.: open `ForwardEqScratch.lean` :1263–1299 beside
   eq. 3.8/3.11; the proof moves μ(t), σ(t)² *back out* of ∂_x by the product rule to
   reuse stage 2 — ask: which chapter remark (pp. 57–58, "inside or outside") tells
   you this escape hatch closes exactly when σ depends on x, and what that has to do
   with Dupire?
9. **Connect** — depends on 0053 (the generator), 0026 (heat/parabolic layer, boundary
   dictionary), 0051; feeds 0021 (Dupire numerator's forward equation — now proved at
   t-only coefficients), 0058 (density moves; coverage-map row names 0054's
   sequencing), 0060. Remaining build: the P_t object + composition (the attempt
   exercise), the IBP-built L*, general FK with drift/killing (shared with 0021's
   prerequisites).
10. **Primary source** — Bagaria ch. 3 §§3.2–3.3, eqs. (3.5)–(3.12), Prop 3.5/3.6,
    Def 3.4/3.7/3.9, Calc 3.8/3.10 (chapter PDF path as in 0053). Stack:
    `builds/lean/ForwardEqScratch.lean`,
    `mathfin/MathFin/Foundations/{FeynmanKacHeatEquation,BrownianMarkov}.lean`.
11. **Exercises/Answers** — keep the stub's attempt exercise (two-line proof of
    P_{t+s} = P_t∘P_s; the measurable-section transfer lemma as the closing gap);
    add: coefficient-relocation drill (∂_x[μp] expansion, why flux form conserves
    probability), migration-lemma reading (what does u(t,x) = ∫g·p mean on a desk?),
    an eq. 3.12-in-words exercise anchored on Fig 3.1's 0.4437028414.

## 6. Stale references in the current stub text

The stub's *names* are all live (checked against the build face this pass — unlike
lesson 0021's `integral_deriv_mul_derivWithin`, nothing in 0054 is a dead name):
`feynmanU_heat_equation` + `hasDerivAt_feynmanU_t/_x/_xx` (:1304/:1006/:1057/:1113),
`itoDrift`/`itoDrift2D`/`bsItoDrift`/`bs_pde_from_no_arbitrage`,
`shift_indep_natural`/`brownian_markov_property`,
`lognormalTerminalPDF_*`, `Adjoint.lean` — all exist. The staleness is in
*premises*, not names:

1. **Status line (:3–5) — premise false.** "the forward (adjoint / Fokker–Planck)
   side is absent from the stack" — refuted by the six ForwardEqScratch theorems
   (item 10 DONE, QUEUE.md:51).
2. **Line count (:57) — stale and self-contradictory.** "(1,273 lines after the
   stage-2 landing)" — the file is **1,397 lines** (`wc -l`, this pass); the stub's
   own :70–74 paragraph documents stage 3 as landed, so the header count contradicts
   the stub's body. (QUEUE.md:98's "705 → 1273 lines" is a historical stage-2 report,
   fine where dated; NOTES.md:553 has the current 1,397.)
3. **"What's blocked and why" (:50–53) — half false.** "On the forward side
   everything is absent …: no $\mathcal{L}^*$, no flux form, no duality, no forward
   equation for anything but the checked GBM density." Now false: flux form
   (`forward_eq_timeDependent_flux` :1269) and the forward equation for five density
   families beyond the GBM-shaped one (constant-drift :229, driftless :247,
   convolution :661, time-dependent :754, convolution :1210 + both flux forms).
   Still true: no L* operator object, no duality theorem.
4. **Path to unblock (:85–88), step (2) — partially consumed.** "derive the forward
   equation for the heat kernel, flux form included" — done (heat-kernel PDE
   `heatKernel_heat` :132 + `forward_eq_timeDependent_flux` :1269), though by
   chain-rule/product-rule calculus, **not** via the IBP-built L* the step names; the
   IBP-built adjoint remains open. Steps (1) and (3) stand as written.
5. **Registry rows to refresh in the same edit** (flip convention): 
   `model-coverage-map.md:40` ("the forward equation [is] not formalized — clean
   build target" — stale) and `:125` (blocker column "no $P_t$ object, no adjoint, no
   parameter differentiation" — the forward-equation unblock path named there has
   landed; rewrite to the residual gate: P_t object/composition, IBP-adjoint,
   operator-level parameter-differentiation assembly, (t,x) coefficients).
6. **Dispatch-side line-number offset (not a stub defect):** the ask's
   `forward_eq_timeDependent_flux :1268` / `forward_eq_convolution_timeDependent_flux
   :1309` are each off by one — the theorem keywords sit at **:1269** / **:1310**;
   :1268/:1309 are docstring lines.

## 7. Checks run / not run

Ran this pass: `pdftotext` on the chapter (690 lines extracted; page anchors mapped
from running headers); `grep -n` inventories of `ForwardEqScratch.lean` (1,397 lines,
`grep -c sorry` = 0, axiom-audit tail :1380–1396 read), build-face
`FeynmanKacHeatEquation.lean`, `BrownianMarkov.lean`, `ItoLemma(.2D).lean`,
`PDEFromIto.lean`, `BreedenLitzenberger.lean`; md5 comparison build-face vs
working-clone `FeynmanKacHeatEquation.lean` (identical); negative greps for
semigroup/composition objects and generator-adjoint objects (zero hits both); reads
of QUEUE.md:51, NOTES.md:551–578, item10-memo.md, coverage-map rows 40/125, lesson
0053 (full), stub 0054 (full), ch03 scan ledger (full).

Not run: the Lean compilation (`lake env lean`) — not part of this E-pass's named
checks; last verified at the stage-3 landing per NOTES.md:553–554 ("zero sorry, both
new theorems standard-three axioms (orchestrator re-ran the bar: exit 0)") and
QUEUE.md:51, and the file is unchanged since (mtime 2026-10-13 19:01, the landing
date). `mdbook build` / `check_links.py` — builder's verification bar at flip time,
not run here.

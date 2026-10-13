# BUILD QUEUE — sequential build program (one subagent at a time, max thinking)

*The resumable state of the Lean build program. Read top-down. `IN FLIGHT` = the
task to (re-)dispatch now; its prompt is stored verbatim below. Land, verify
(`lake env lean`, zero sorry, `#print axioms` standard-three), archive to
`builds/lean/`, update this file, commit — then promote the next item.*
*AGENTS.md "Resume protocol" governs recovery after quota outages.*

**STATUS: ACTIVE (2026-10-13)** — resumed from the PAUSED banner per the session
handoff. Item 10's E-pass (pinned `flash-explorer`) is dispatching now.


## Revision environment map (updated 2026-10-14 — supersedes the 2026-10-05 pinned-rev map)

**Three Mathlib faces exist; only the BUILD FACE decides compilability** (AGENTS.md
§Name-verification convention). Current revs, all grep-verified 2026-10-14:

| Face | Rev | Role |
|---|---|---|
| `AmericanPutConvexity/.lake/packages/mathlib` | **81a5d257** (toolchain v4.32.0) | **THE BUILD FACE** — every `builds/lean/*.lean` compiles here via `cd AmericanPutConvexity && lake env lean ../builds/lean/<file>.lean` |
| `mathfin/.lake/packages/mathlib` | 0434c03 | mathfin's CI face (v4.33.0-rc1 toolchain); secondary context |
| workspace `mathlib4/` clone | 2a88576 (2026-09-30) | reference only; never decides compilability |

MathFin sides: **AC's packaged MathFin = 784a831** (the historical "pin"; its missing-modules
list still applies THERE — e.g. no `Foundations/Bisection.lean`); **mathfin working clone =
HEAD `4d82234`** (PR-2..6 promotions committed 2026-10-14; fork remote `leafyoung/formal-mathfin`
at `b46e9b4` pending push). Modules that exist at mathfin HEAD but NOT at 784a831:
`Foundations/Bisection.lean`, `Foundations/DerivOfDeriv.lean`, `Foundations/ProductMeasure.lean`
(broken), `Probability/` dir, `Foundations/HullWhiteCalibration.lean`,
`Foundations/MonteCarloPricer.lean`, the Itô batch (`ItoDriftExpectation`,
`ItoFormulaAdaptedDrift`, `ItoIntegralCrossHorizon`).

Rule: agents import only modules verified on the face they compile against; for
modules present at mathfin HEAD but absent on the AC face (784a831), either grow the
lemma privately in the build file (house-lemma pattern) or target mathfin CI directly
(promotion vehicle — see PUBLISHING.md status block).

## Queue

| # | Build | Lesson | Status |
|---|---|---|---|
| 1 | Affine engine stages 1–4 (OU+CIR invariance, Riccati flows, CIR bond) | 0033 | DONE |
| 2 | Capstone: parity + put-strike convexity | 0017 | DONE |
| 3 | Greeks signs (14 theorems) | 0029 | DONE |
| 4 | Hull–White steps 1–3 (deterministic, Gaussian law, affine bond) | 0020 | DONE |
| 5 | Gyöngy core (tower identity, marginal-flow theorem) | 0038 | DONE |
| 6 | Gyöngy stage 2 (hucont + hf″meas removed) | 0038 | DONE |
| 7 | Forward equation stage 1 (constant-coefficient + migration lemma) | 0054 seed | DONE |
| 8 | Forward equation stage 2 (time-dependent coefficients) | 0054 | DONE |
| 9 | **MathFin Itô contribution: adapted-integrand drift identity** | 0038/0048 | **DONE (closed 2026-10-13)** — the full assembly `itoDrift_expectation_identity_adapted` landed in `AmericanPutConvexity/ItoContribution.lean` (6,700 lines, zero sorry, standard-three axioms; all stage-5c dying blocks + `driftBlock_tendsto` + the E-level identity); hitoid DROPPED for the constructed process (GyongyScratch 1,146 lines, `hitoid_constructed_terminal` unconditional); CrossHorizon (dispatch 12: `hMconsist` resolved — consistency for t ≤ τ) PORTED to MathFin (dispatch 13) as `MathFin/Foundations/ItoIntegralCrossHorizon.lean` (394 lines, port-test verified, root import). Remaining MathFin port of the ItoFormulaAdaptedDrift monolith split is a PUBLISHING (PR-1) item, not a build item — tracked in `builds/lean/PUBLISHING.md` **|
| 10 | Forward-eq stage 3: (t, x)-dependent coefficients (full Dupire form) | 0021/0054 | **DONE (2026-10-13)** — `ForwardEqScratch.lean` → 1,397 lines (+124, stage 1–2 byte-stable), zero sorry, both new theorems standard-three, orchestrator re-verified. Landed (Route B, flux/divergence form with t-only coefficients): `forward_eq_timeDependent_flux` + `forward_eq_convolution_timeDependent_flux` (eq. 9.2's coefficients-inside form, proved from stage 2 via the constant-coefficient product rule). Route C (genuine (t,x)) REJECTED as hypothesis-echo — gated on a non-Gaussian density carrier (`memos/item10-memo.md`). Built via ZCode **workflow** (first workflow dispatch): B = GLM-5.3 max, V-fidelity = GLM-5.3 high, deterministic lake/sorry gates. Contract had a typo (σ² double-count + ill-typed nesting) caught by builder escalation; corrected form verified in the orchestrator V-pass. Lesson 0054 build-seed refreshed (stub remains BLOCKED on the semigroup object) |
| 11 | Gyöngy full Thm 9.6: Y-existence (weak, non-Lipschitz) | 0038 | **DONE (2026-10-13)** — `GyongyScratch.lean` → 1,702 lines (+555, prefix byte-stable), zero sorry, all four contracted theorems standard-three, orchestrator V-pass PASSED (bar re-run + term-by-term fidelity diff). Landed: `exists_driftCoeff_fn`, `exists_diffCoeffSq_fn` (Doob–Dynkin Borel coefficient functions — first (t,x)-form coefficients in the program), `marginal_flow_weak_equation_fn_constructed`, `gyongy_mimicry_gated` (Thm 9.6 modulo the named flow-uniqueness gate; Y as data). Route 3 rejected as gated-on-air; strong existence for merely-Borel coefficients false in general; Skorokhod/martingale-problem core absent from every clone. Item-18 finding 4 CORRECTED in NOTES.md. Two-workflow dispatch (E'/judge `dwfrun-689d1d66`, B `dwfrun-9152c50d`, glm-5.3 max; elaboration-first skeleton per the item-10 lesson) |
| 12 | Tier-1: MC pricer theorem (0023 spec) | 0023 | **DONE — `builds/lean/mc_pricer.lean` (488 lines, 8 theorems: pairwise-SLLN consistency, CLT with identified variance, closed-form second moments, BS-put bridge)** |
| 13 | Tier-1: curve bootstrapping (0030 spec) | 0030 | **DONE — `builds/lean/hw_bootstrap.lean` (658 lines, 45 decls: private bisection engine, FRA/swap threshold bridges, affine bootstrap step with ⌈log₂⌉ budget, the repricing induction, flat-curve capstone)** |
| 14 | Tier-1: CMS convexity adjustment (0031 spec) | 0031 | **DONE — `builds/lean/cms_scratch.lean` (499 lines, 11 theorems: par-rate functional + S″, convexity via hand-proved convexOn_inv_shift, annuity measure = numéraire engine's third execution, cms_adjustment_nonneg via ConvexOn.map_integral_le, Carr–Madan replication seed)** |
| 15 | Tier-1: Cox-intensity credit (0032 spec) | 0032 | **DONE — `builds/lean/cox_scratch.lean` (697 lines, 20 theorems: constant-λ legs, deterministic λ(t) bridge with the novel a.e. set-equality mechanism, stochastic CDS spread headline, restricted-Cox mixing stretch landed; enlargement out of scope)** |
| 16 | HW calibration (θ from curve) + repricing identity | 0020 step 4 | **DONE — `builds/lean/hw_scratch.lean` → 767 lines (hwTheta = verified addendum formula; hwCalibMean/hwCalibMean_eq_forward mean identity; hw_reprices_curve — the repricing is EXACT; hwVar_eq_interval). Toolchain notes recorded** |
| 17 | Jamshidian swaption decomposition | 0034/0066 | **DONE — `builds/lean/jamshidian_scratch.lean` (606 lines, 18 theorems: Bond–Swap reduction keyed to payerSwapValue/annuity, monotone machinery + IVT + unique par state, the headline pointwise decomposition + put direction, HW single-state instance, Black-76 pricing corollaries; the forward-measure bridge is the honest remaining research step)** |
| 18 | **Tier-2: CIR existence slice (explicit squared-OU, Feller-borderline)** | 0033/0060 | **DONE (2026-10-13)** — `builds/lean/cir_existence_scratch.lean` (515 lines, 15 theorems, zero sorry, 15/15 standard-three axioms, orchestrator re-verified). Explicit no-solver OU construction + exact Gaussian laws + headline `cirVariance_mean`: E[V_t] = θ(1−e^{−kt}) + v₀e^{−kt}. Four substrate findings in NOTES.md (identity engine needs globally bounded drift — inapplicable to OU; deterministic-b shape inconsistent with hMeq; constructor is `WienerIntegralL2.wienerIntegralLp`; no pathwise-continuous Itô integral at the pin ⇒ process-level CIR existence stays gated) |
| 19 | Tier-2: Heston characteristic function (2D affine exponent) | 0033/0059 | **DONE (2026-10-13)** — `builds/lean/heston_scratch.lean` (794 lines, 41 decls / 29 public, zero sorry, 29/29 standard-three axioms). 2D exp-affine calculus + `hestonGenerator` invariance (x-coeff ≡ 0) + ρ-shifted Riccati flows (`hestonGamma` = √((κ−ρξu)²+ξ²(u−u²))) + PDE headline (`hestonTransform_pde` closed form + terminal) + gated expectation as a PROVED implication. V-pass fidelity diff PASSED: the 0<u<1 strip is Bagaria Thm 14.7's necessary moment strip (numerically verified outside it the closed form fails), loudly documented. Bv-flow re-derived; 5 substrate findings in NOTES.md. 6.35M tokens / 42 min |

Standing rule: after every landing, re-run the audit (`tools/ProofDependencyAudit.lean`
--replay) and the axiom checks; record the build in `builds/lean/README.md`; landings
that change lesson status update the lesson + the stub registry. Dispatches route
per `builds/lean/ROUTING.md` (E-flash-explore → S/B-glm → V-verify incl. statement-
fidelity diff); queued items' routes are mapped there (item 10 hybrid, item 11
glm-only, PR-2..7 E-flash dep-mapping).

---

## (no item IN FLIGHT at build level — items 1–19 all DONE; PR-2..6 promotions BUILT+STAGED+pushed 2026-10-14 (fork main @ 5708258, upstream #244 awaiting review — see AGENTS.md §Upstream-PR discipline); NEXT: the 12 stub lessons per the model-coverage-map registry, reusing the now-landed forward-eq/Gyöngy substrate)
The item-19 dispatch prompt is preserved verbatim in git history (builds/lean/dispatch-item19.prompt, commit 5427c37).
Item 10 was the first dispatch through a ZCode **workflow** (script archived at
`AmericanPutConvexity/.zcode/workflow-drafts/Item-10-build-forward-eq-stage-3-BgateV.dwf.ts`); per-run
model tiering (B=glm-5.3 max, V-diff=glm-5.3 high, gates=world.run) replaces the pinned-agent/manual-switch
mechanism when the user asks for workflow dispatch.

---

## DONE-log (details in builds/lean/README.md + mdbook/src/NOTES.md)

- Itô contribution (item 9, dispatches 3–13): `ItoContribution.lean` 6,700 lines
  (adapted E-level Itô–drift identity, zero sorry) + `GyongyScratch.lean` 1,146
  lines (constructed-process route, hitoid dropped) + MathFin port of CrossHorizon
  (`ItoIntegralCrossHorizon.lean`, 394 lines, upstream-ready). Closed 2026-10-13.
- Affine engine: 906 lines — invariance lemmas, Riccati flows, CIR bond closed form
  (`cirBondPrice_pde` + terminal). Stage 2 corrected spec (minus-form Riccati);
  stage 3 corrected spec (discounted calendar-time PDE); stage 4 corrected handoff
  (B(0)=0). Archived + git `0ca80b3`.
- Capstone: `scratch.lean` — parity + strike convexity, axioms clean, git-noted.
- Greeks: `greeks_signs.lean` — 14 theorems; pinned-rev find: no DerivOfDeriv at
  784a831 (workspace clone HEAD newer). Archived.
- HW: `hw_scratch.lean` — 33 declarations; `vasicekBondB` reused verbatim;
  no-Fubini antiderivative bypass discovered. Archived.
- Gyöngy: `GyongyScratch.lean` — tower identity, marginal-flow theorem; stage 2
  removed hucont (filter-generic DCT) + hf″meas (ContDiff route); Doob–Dynkin EXISTS
  (`exists_eq_measurable_comp`). Archived + git `36445e0`.
- Forward-eq: `ForwardEqScratch.lean` 705 → 1273 lines — constant + time-dependent
  Fokker–Planck + migration lemmas (DCT-dominated). Archived + git `3246e7b`.

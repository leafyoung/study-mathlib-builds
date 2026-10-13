# PR-3 memo — E-pass dependency map: MC pricer → MathFin

E-pass (flash-explorer, read-only), 2026-10-13. Source: `builds/lean/mc_pricer.lean`
(1,169 lines). Proposed upstream home per `builds/lean/PUBLISHING.md:65-70`:
"`MathFin/Probability/MonteCarloPricer.lean`-shaped". Upstream rules read from
`mathfin/CONTRIBUTING.md`; style model: the closest existing mathfin probability
module, `mathfin/MathFin/Foundations/MonteCarloPricer.lean` (see headline). All names
below are grep-verified in this session on the faces stated; line numbers are current
file states. No lake build, no docker, no git was run; nothing in `mathfin/` was
modified.

## Headline finding (changes the PR-3 shape)

**The proposed module already exists upstream — but only as the put-only half.**
`mathfin/MathFin/Foundations/MonteCarloPricer.lean` (487 lines) is in the mathfin
tree, root-imported at `mathfin/MathFin.lean:228`, in namespace
`MathFin.MonteCarlo` (`MonteCarloPricer.lean:76`), with the full house wrapper
(copyright header :1-5, `module` :6, `public import` :8-10, `@[expose] public
section` :74). It is a renamed, house-styled promotion of the *old* 488-line /
8-theorem `mc_pricer.lean` recorded in `builds/lean/QUEUE.md:41` ("488 lines, 8
theorems"): `payoff`/`estimator`/`payoff_le`/`integrable_payoff`/`memLp2_payoff`/
`mean_eq_bsPut`/`consistency`/`consistency_iid`/`clt_library`/`clt`/
`secondMoment_payoff`/`secondMoment`/`variance` — i.e. PUBLISHING.md's PR-3 put-layer
scope, byte-for-byte the same math as the current scratch's put half
(`builds/lean/mc_pricer.lean:76-503`), modulo naming.

Consequences:

1. **mathfin has no `Probability/` dir** (dir listing of `mathfin/MathFin/`:
   Actuarial, Binomial, BlackScholes, Blueprint, Bridges, Contracts, DeFi,
   Execution, FixedIncome, Foundations, Futures, Performance, Portfolio,
   RiskMeasures). `CONTRIBUTING.md:44-45` puts probability primitives in
   `Foundations/` — which is where the shipped module already lives. PR-3's home is
   therefore `MathFin/Foundations/MonteCarloPricer.lean`, and the realistic PR-3
   shape is **extend the existing module** (or add a sibling module), not create a
   new file. PUBLISHING.md's PR-3 row is stale on this point.
2. **PR-3's actual delta** = the call-variant layer (`mc_pricer.lean:505-1031`:
   `mcCallPayoff`, integrability by domination `0 ≤ C ≤ e^{-rT}·S_T`, the
   discounted-forward identity `E[e^{-rT}·S_T] = S₀`, call consistency/CLT/variance)
   + the multi-D seed (`mc_pricer.lean:1033-1140`: `multiGauss`, joint law bridge,
   Etemadi consistency for vector draws) + the two terminal-moment cross-checks
   (`:490-501`, candidates for dropping — see Flags).
3. The AC-packaged mathfin
   (`AmericanPutConvexity/.lake/packages/MathFin/`) does **not** contain
   `MonteCarloPricer.lean` — the shipped module is newer than the AC pin; the
   scratch's content-level verification at the AC pin does not cover the module
   wrapper (which only compiles in mathfin's own v4.33.0-rc1 env).
4. Committed-vs-uncommitted of the shipped put module: **unresolved this pass** (git
   is out of my scope). Evidence: bare root-import line (`MathFin.lean:228`, no
   explanatory comment — unlike this program's PR-1 imports at `MathFin.lean:222-227`
   which carry comments), zero references in `docs/coverage.md`,
   `verification_ledger.json` (`grep -c MonteCarlo` = 0), `tests/`, `benchmarks/`,
   `tools/`; header author "Raphael Coelho" (upstream convention). PUBLISHING.md
   enumerates the uncommitted working-tree content as exactly the three Itô modules
   and does not mention this file. S-pass must resolve with one `git -C mathfin
   status --short` / `git log --oneline -- MathFin/Foundations/MonteCarloPricer.lean`
   before shaping the PR.

## 1. External deps (every non-file name, with verification face)

Face key — **AC-M**: `AmericanPutConvexity/.lake/packages/mathlib` (81a5d257, the
compilation face per AGENTS.md; the scratch compiles here — recorded at
`PUBLISHING.md:38-39`, not re-run this pass); **MF-M**: `mathfin/.lake/packages/
mathlib` (0434c03, the actual PR compile face); **MF-F**: `mathfin/MathFin/` working
tree; **AC-F**: `AmericanPutConvexity/.lake/packages/MathFin/MathFin/`. Where one
line number is given it was confirmed identical on both faces checked.

Mathlib atoms (all load-bearing ones grep-hit on both MF-M and AC-M):

| Name | Where (MF-M = AC-M unless noted) |
|---|---|
| `strong_law_ae_real` | `Mathlib/Probability/StrongLaw.lean:598` (both) |
| `tendstoInDistribution_inv_sqrt_mul_sum_sub` | `Mathlib/Probability/CentralLimitTheorem.lean:124` (both) |
| `TendstoInDistribution.congr` | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean:89` (MF-M) |
| `MemLp.of_bound` (needs `[IsFiniteMeasure μ]`) | `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:549` (both) |
| `memLp_one_iff_integrable` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:65` (MF-M) |
| `memLp_two_iff_integrable_sq_norm` | `Mathlib/MeasureTheory/Function/L2Space.lean:45` (both) |
| `variance_eq_sub` (+ `Var[·;·]` notation) | `Mathlib/Probability/Moments/Variance.lean:226` AC-M / `:224` MF-M |
| `gaussianReal`, `gaussianPDFReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:222, :49` (AC-M) |
| `integrable_gaussianPDFReal` | same file `:91` (both) |
| `integrable_exp_mul_gaussianReal` | same file `:516` AC-M / `:517` MF-M |
| `integral_gaussianReal_eq_integral_smul` | same file `:275` (AC-M) |
| `integrable_map_measure` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:355` (both) |
| `HasLaw.comp` | `Mathlib/Probability/HasLaw.lean:108` (AC-M) |
| `HasLaw.identDistrib` | `Mathlib/Probability/IdentDistrib.lean:145` (MF-M) |
| `iIndepFun.hasLaw_pi`, `iIndepFun_iff_hasLaw_pi_pi` | `Mathlib/Probability/HasLaw.lean:231, :239` (both) |
| `Measure.pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:210` (`protected irreducible_def pi`, AC-M) |
| `Measure.map_id`, `integral_map`, `integral_congr_ae`, `setIntegral_congr_fun`, `integral_indicator`, `integral_const_mul`, `IntegrableOn.{const_mul, sub, mono', congr_fun, integrableOn}`, `Measurable.aemeasurable`, `IsProbabilityMeasure`, `Tendsto`, `𝓝`, `atTop`, `Real.{exp, sqrt, sq_sqrt, sqrt_pos, sqrt_ne_zero', norm_eq_abs}`, `sq_abs`, `sq_le_sq`, `mul_pow`, `pow_two`, `Filter.Eventually.of_forall` | core Mathlib; on AC-M attested by the scratch's recorded AC-pin compile (`PUBLISHING.md:38-39`); `integrable_map_measure`/`memLp_one_iff_integrable` re-grep-hit on MF-M (above) — the two faces are near-identical (all sampled decl lines agree within ±2) |

MathFin atoms (all grep-hit at identical lines on MF-F and AC-F):

| Name | Where |
|---|---|
| `BSCallHyp` | `MathFin/BlackScholes/Call.lean:88` |
| `bsd1`, `bsd2` | `Call.lean:98, :102`; `bsTerminal_gt_K_iff` statement `Call.lean:124` |
| `bs_call_formula` | `Call.lean:178` |
| `bs_put_formula` | `BlackScholes/Put.lean:99` |
| `integral_exp_mul_gaussianPDFReal_Iic` | **`BlackScholes/Put.lean:46`** — NOT in `Foundations/StandardNormal.lean` as the scratch header claims (`mc_pricer.lean:42-44` mis-attributes it); correction belongs in the promoted docstring |
| `Phi`, `Phi_def` | `Foundations/StandardNormal.lean:53, :56` |
| `setIntegral_gaussianPDFReal_eq_toReal` | `StandardNormal.lean:64` |
| `gaussianReal_Ioi_toReal` | `StandardNormal.lean:139` |
| `exp_mul_gaussianPDFReal_zero_one` | `StandardNormal.lean:153` |
| `integral_exp_mul_gaussianPDFReal_Ioi` | `StandardNormal.lean:173` |
| `integral_exp_mul_gaussianPDFReal_univ` | `StandardNormal.lean:202` (MF-F) |
| `secondMoment_terminal`, `variance_terminal` | `BlackScholes/LognormalMoments.lean:47, :67` (consumed only by the two cross-check theorems `mc_terminal_secondMoment`/`mc_terminal_variance`) |

AC-clone names: **none** — the scratch imports only `Mathlib` + three MathFin
modules (`mc_pricer.lean:1-4`). Note `integral_exp_mul_gaussianPDFReal_Ioi` reaches
the scratch through `MathFin.BlackScholes.Put` transitively? No — it lives in
`StandardNormal.lean`, which the module already `public import`s; the `Iic` atom
rides the `Put` import. Both imports the shipped module already declares.

## 2. Private helpers that must ship

House rule: "Helper lemmas can live in the same file as `private`"
(`CONTRIBUTING.md:101-102`). The shipped put module's precedent: every supporting
lemma is `private` (`MonteCarloPricer.lean:88, 94, 109, 119, 161, 172, 180, 189,
261, 303`); only the 8 API theorems + 2 defs are public.

If PR-3 **extends** the existing module, the put-layer privates
(`terminal_nonneg`, `payoff_nonneg`, `measurable_payoff`,
`aestronglyMeasurable_payoff`, `hasLaw_payoff`, `identDistrib_payoff`,
`iIndepFun_payoff`, `pairwise_payoff`, `inv_sqrt_mul_sub_eq`, `integral_lin_comb3`)
are already there and are reused, not re-declared. The delta must ship these as
`private` (mirror of the put module's public/private split):

- `measurable_mcCallPayoff` (scratch:544) — mirror of private `measurable_payoff`
- `mcCallPayoff_nonneg` (scratch:531) — mirror of private `payoff_nonneg`
- `mcCallPayoff_le_terminal` (scratch:537) — used only inside public proofs; the
  put's public analog `payoff_le` is public because it is the module's boundedness
  statement; the call has no boundedness statement, so this one is private
- `aestronglyMeasurable_mcCallPayoff` (scratch:564) — mirror of private
  `aestronglyMeasurable_payoff`
- `aestronglyMeasurable_comp_of_hasLaw` (scratch:555) — already `private` in the
  scratch (the only one that is)
- `integrable_exp_of_hasLaw` (scratch:573) — recommend private (module-internal
  engine); if judged of independent law-transfer interest it can stay public —
  S-pass call
- `integrable_sq_terminal` (scratch:584) — private (L² envelope engine)
- `hasLaw_mcCallPayoff`, `identDistrib_mcCallPayoff`, `iIndepFun_mcCallPayoff`,
  `pairwise_mcCallPayoff` (scratch:743, 754, 761, 769) — mirrors of the put's four
  private transfer lemmas
- `multiGauss_instIsProbabilityMeasure` (scratch:1053) — currently a named
  `instance`; house-cleanest is folding it into the `multiGauss` def block or
  keeping one named public instance (instances shouldn't be `private`); S-pass call

Public (API) in the delta: `mcCallPayoff` (:527), `integrable_mcCallPayoff` (:683),
`memLp2_mcCallPayoff` (:693), `integrable_discountedTerminal` (:623),
`integral_discountedTerminal_eq` (:650), `mean_mcCallPayoff_eq_bsCall` (:727),
`mcCallMean` (:779), `mc_call_consistency` (:788), `mc_call_consistency_iid`
(:805), `mc_call_clt_library` (:820), `mc_call_clt` (:838),
`secondMoment_callPayoff` (:874), `secondMoment_mcCallPayoff` (:992),
`mc_call_variance` (:1016), `multiGauss` (:1050), `multiGauss_hasLaw_joint`
(:1067), `multiD_consistency` (:1085), `multiD_consistency_iid` (:1121),
`multiD_integrable_of_bounded` (:1135).

## 3. Name conflicts against the existing mathfin tree

Grepped `\b<name>\b` over `mathfin/MathFin/**.lean` (excluding the existing
MonteCarloPricer itself): `mcPayoff`, `mcMean`, `mc_put_variance`,
`mcCallPayoff`, `mcCallMean`, `mc_call_consistency`, `mc_call_clt`,
`mc_call_variance`, `secondMoment_callPayoff`, `secondMoment_mcCallPayoff`,
`multiGauss`, `multiD_consistency`, `multiD_integrable_of_bounded`,
`integrable_discountedTerminal`, `integral_discountedTerminal_eq`,
`integrable_sq_terminal`, `integrable_exp_of_hasLaw` — **all NONE (zero conflicts)**.
`secondMoment_terminal`/`variance_terminal` exist only where they should
(`LognormalMoments.lean` + the two axiom-audit files + `PowerOption.lean`).

- Namespace `namespace MathFin.MonteCarlo` is used by exactly one file
  (`Foundations/MonteCarloPricer.lean:76`). No other claimant.
- Proposed path: `MathFin/Probability/…` does not exist as a directory **and** the
  exact home `MathFin/Foundations/MonteCarloPricer.lean` **already exists** (see
  headline). The one in-namespace collision to design around is a *name* one: the
  put module already owns `secondMoment` and `estimator`, so call-side names must
  not reuse them (e.g. `secondMoment_callPayoff` is fine as `callSecondMoment_*`,
  `mcCallMean` should not become plain `estimator`).
- No `MathFin.Probability` namespace anywhere in `mathfin/MathFin/*.lean` or
  `MathFin.lean` (PUBLISHING.md's "broken phantom" `Probability.ProductMeasure` is
  absent from the tree — consistent with the scratch's honest-scoping note).

## 4. House-style deltas (concrete, per item)

Style model: `mathfin/MathFin/Foundations/MonteCarloPricer.lean` (a shipped,
in-style probability module) + `CONTRIBUTING.md:99-110` + `docs/patterns.md:941`.

1. **Header** (CONTRIBUTING.md:106-107): scratch has a 66-line teaching banner
   (`mc_pricer.lean:6-71`). Replace with the house header — copyright/license/
   authors block + `module` + `public import`s + short docstring + `## Result`
   listing the public API. Copy the shape of `MonteCarloPricer.lean:1-72`; the
   delta's `## Result` list appends the call + multi-D entries.
2. **Module system**: add `module` (:6), `public import Mathlib` +
   `public import MathFin.Foundations.StandardNormal` + `public import
   MathFin.BlackScholes.Put` (+ `Call`/`LognormalMoments` only if not transitive —
   the shipped module gets `BSCallHyp` through `Put`'s imports; keep the shipped
   module's exact import set) and `@[expose] public section` (:74). This is
   CI-enforced: `tests/test_router.py:106`
   (`test_mathfin_module_files_expose_public_section`). Note the wrapper only
   compiles under mathfin's toolchain `leanprover/lean4:v4.33.0-rc1`
   (`mathfin/lean-toolchain`), not at the AC pin v4.32.0.
3. **Namespace**: everything under `namespace MathFin.MonteCarlo` (:76) with the
   `open` lines inside (:78-79); the scratch is root-namespace (`mc_pricer.lean:73`).
4. **Naming**: follow the shipped module's de-`mc` scheme: `mcCallPayoff →
   callPayoff`, `mcCallMean → callEstimator`, `mc_call_consistency →
   callConsistency`, `mc_call_consistency_iid → callConsistency_iid`,
   `mc_call_clt_library → callClt_library`, `mc_call_clt → callClt`,
   `mc_call_variance → callVariance` (mirroring `clt`/`variance`), call-side second
   moments per put precedent (`secondMoment_payoff → secondMoment`; call side needs
   distinct names, e.g. `callSecondMoment_payoff` / `secondMoment_callPayoff` —
   S-pass fixes the exact scheme; constraint: `secondMoment` and `estimator` are
   taken). Multi-D names are already clean (`multiGauss`, `multiD_consistency` —
   keep or camelCase per module precedent `consistency_iid`).
5. **Private helpers**: apply §2's private list (CONTRIBUTING.md:101-102; module
   precedent cited there).
6. **Comments** (CONTRIBUTING.md:103-105, "default to no comments; the why only"):
   strip all course apparatus — lesson-0023 references (:9, 203-209, 238-243, 466...),
   "deliverable N" labels, "the moment of the course: audit" (:1142), the
   substrate-consumption inventory (:31-51). Keep the mathematical docstrings and
   the step comments inside long proofs only where the move is non-obvious (the
   shipped module kept e.g. the `_root_.Pairwise` shadowing note :186-188 and the
   Step 8 ring note :429 — same policy). The honest-scoping paragraph compresses to
   1-2 docstring sentences (model: `MonteCarloPricer.lean:43-47`).
7. **Drop the `#print axioms` audit block** (`mc_pricer.lean:1144-1168`): not house
   style; the shipped module has none and CI re-verifies axioms via byte-fresh
   `AxiomAuditGen.lean` (CONTRIBUTING.md:63-69, 93).
8. **Fix the `_Iic` attribution** in any carried-over docstring: the atom is
   `BlackScholes/Put.lean:46`, not `Foundations/StandardNormal.lean`
   (scratch:42-44 vs grep fact).
9. **Tactic style**: already conforms — `field_simp; ring` close-outs (scratch:344,
   889...), `linear_combination (norm := ring_nf)` endgames (:440, 986), `fun_prop`
   for measurability (:108, 544), `simpa only [payoff] using bs_put_formula h`
   bridges. No `bs_identity` needed (nothing derives the BS formula here; the
   bridges are direct applications).
10. **One-theorem-per-file** (CONTRIBUTING.md:101): the rule carves out
    feature-module bundling, and the shipped precedent settles it for this family —
    `MonteCarloPricer.lean` bundles 15 decls; the tree has 6,189-line modules.
    Extending the existing module needs **no** `MathFin.lean` edit (safer next to
    PR-1's uncommitted import lines at `MathFin.lean:222-227`); a sibling-module
    choice would need a new root-import line + `@[expose]` + coverage rows.

## 5. Local compile-verification feasibility (before opening the PR)

**Not feasible locally for the promoted module, read-only. Facts (checked this
pass):**

- mathfin's own oleans are **not built**: `mathfin/.lake/build` does not exist
  (only `.lake/config` and `.lake/packages`). `lake env lean
  MathFin/Foundations/MonteCarloPricer.lean` in the clone cannot resolve
  `import MathFin.*` until MathFin (and its deps) build at least once.
- Package oleans: `mathfin/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
  **exists** (Mathlib is built); `BrownianMotion/.lake/build` **absent** (another
  required MathFin dep, unbuilt).
- Toolchain is present: `elan toolchain list` shows `leanprover/lean4:v4.33.0-rc1`
  (with v4.32.0 and v4.35.0-rc3), so nothing needs downloading — only building.
- Building would mean a real `lake build` in mathfin: forbidden for this pass
  (read-only; uncommitted PR-1 content in the tree), and governed by the host-safety
  doctrine (`mathfin/CLAUDE.md:224-234` via `mathfin/AGENTS.md`: one Lean-loaded
  process; the heavy verification runs in the verify container).
- **Sanctioned verification path = the CI trio in the verify container**:
  `docker compose -f docker/docker-compose.yml pull verify` then
  `docker compose ... run --rm verify` (`CLAUDE.md:27, 42`) running
  `pytest tests/ -q` → `python3 -m tools.verify.ledger status` → `lake build`
  (`CONTRIBUTING.md:39-40`); the lean-repl daemon + `./scripts/lean-check.sh`
  (`CONTRIBUTING.md:56-62`) is the fast per-file loop inside that doctrine. This
  must be executed by the orchestrator/build session, not by this explorer.
- **Content-level local proxy that IS already in hand**: the math (as opposed to
  the module wrapper) is verified at the AC pin — the scratch itself is the
  port-test: it compiles standalone at v4.32.0 with zero sorry and standard-three
  axioms (recorded `PUBLISHING.md:38-39`; not re-run this pass — no lake was run
  here). The wrapper delta (module syntax, namespace, privates, renames) is
  mechanical but only machine-checks in mathfin's env ⇒ it rides the container.

## 6. coverage.md rows to add

Format per `docs/coverage.md:900-905`: `> (N) `mf-id` (`Path.decl`): math
description …`; tier vocabulary at `docs/coverage.md:9-25` (`full` /
`library_wrapper` / `reduced_core` / `placeholder`; placeholder must be 0).
**Discovery: the shipped put module has NO coverage rows at all** (grep
MonteCarlo/mc_put/estimator over `docs/coverage.md`: zero hits) — PR-3 should
backfill them alongside the delta rows.

Delta rows (theorem-shaped, ≈19, all `full` — real derivations, honest hypotheses;
nothing is a projection-rfl target):

- Call layer (15): `callPayoff` integrability (`integrable_mcCallPayoff`), `L²`
  membership, a.s.-measurability engine (if kept public), `integrable_exp_of_hasLaw`
  + `integrable_sq_terminal` (if kept public), `integrable_discountedTerminal`,
  `integral_discountedTerminal_eq` (the discounted-forward identity), 
  `mean_mcCallPayoff_eq_bsCall`, call consistency (pairwise + iid forms),
  call CLT (library + desk forms), `secondMoment_callPayoff`,
  `secondMoment_mcCallPayoff`, `mc_call_variance`.
- Multi-D (4): `multiGauss_hasLaw_joint`, `multiD_consistency`,
  `multiD_consistency_iid`, `multiD_integrable_of_bounded`.
- Backfill (≈12): the shipped module's public decls (`payoff`, `estimator`,
  `payoff_le`, `integrable_payoff`, `memLp2_payoff`, `mean_eq_bsPut`,
  `consistency`, `consistency_iid`, `clt_library`, `clt`, `secondMoment_payoff`,
  `secondMoment`, `variance`) — same `full` tiers.
- **PR-4's known exception does NOT apply here**: `cdsFairSpread_TV_balances`
  (`PUBLISHING.md:86-92`) belongs to the Cox module (PR-4). PR-3 has no
  `library_wrapper` candidate under CONTRIBUTING.md's definition (Mathlib/
  BrownianMotion re-exports) — with one judgment call: `mc_terminal_secondMoment`
  / `mc_terminal_variance` (scratch:490-501) are direct re-applications of
  MathFin's own `secondMoment_terminal`/`variance_terminal`. Recommendation: drop
  them from the upstream module (course-facing cross-checks; the theorems already
  live in `LognormalMoments.lean`); if the S-pass keeps them, their rows are the
  module's only `library_wrapper`-shaped entries and would need the
  `UPSTREAM_CITATIONS` treatment (`CONTRIBUTING.md:92-97`).

## 7. Flags for the S-pass

1. **Resolve committed-vs-uncommitted of the shipped put module first** (one git
   command, orchestrator-side): PR shape = extend-in-place vs rebase-on-HEAD differ
   if the file is local-only. Do not touch PR-1's uncommitted files/lines either way.
2. **Stale plan**: `PUBLISHING.md:18` ("MC pricer … 490 lines, 8 theorems … new MC
   module") and `:65-70` describe the put-only promotion as future work; both need
   updating after PR-3 lands (the module exists; delta landed).
3. **Naming scheme** for the call layer (`callPayoff`/`callEstimator`/`callClt`/
   `callVariance`/second-moment names) and the `multiGauss` instance shape — fix
   before dispatching B; `secondMoment`/`estimator` are taken in-namespace.
4. **Drop-or-keep the two terminal cross-checks** (`mc_terminal_secondMoment`,
   `mc_terminal_variance`) — drop recommended (see §6).
5. **`integrable_exp_of_hasLaw` public-or-private** — genuinely reusable
   law-transfer lemma; default private per house style.
6. **Extend vs sibling module**: extension recommended (no `MathFin.lean` edit next
   to PR-1's lines; one namespace; reuse of privates). Sibling needs root-import +
   `@[expose]` + its own rows.
7. **The `_Iic` doc mis-attribution** (scratch:42-44) must not be carried into the
   upstream docstring (`Put.lean:46` is the home).
8. **Verification budget**: content is AC-pin-verified (recorded); wrapper is not
   locally checkable — plan the B-pass to end at the verify-container trio, and
   expect the first `lake build` in a fresh mathfin checkout to also build
   BrownianMotion (unbuilt) — budget accordingly.
9. **Coverage backfill** of the shipped module's missing rows rides PR-3 (keeps
   CONTRIBUTING step 5 honest without a separate docs PR).

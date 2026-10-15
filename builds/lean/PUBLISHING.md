# PUBLISHING.md — how to publish the Lean builds

*The publication plan for the workspace's Lean builds (2026-10-05 → 10-11 program:
12 build files in `builds/lean/`, ~14,100 lines, ~380 theorem/lemma declarations, all
sorry-free, standard-three axioms; plus 3 modules already live in the MathFin tree,
~6,900 lines, ~88 more). Read with `builds/lean/QUEUE.md` (what exists) and
`mathfin/CONTRIBUTING.md` (the target repo's requirements).*

## The inventory (what exists, where)

| Build | Workspace file | Lines | Theorems | Natural upstream home |
|---|---|---|---|---|
| Affine engine (stages 1–4) | `builds/lean/AffineEngineScratch.lean` (+ live copy in AC) | 906 | ~30 | MathFin `Foundations/` (engine) + CIR application |
| Capstone (parity + strike convexity) | `builds/lean/scratch.lean` (+ live in AC) | 48 | 2 | MathFin `BlackScholes/` (likely already covered — diff first) |
| Greeks signs | `builds/lean/greeks_signs.lean` (+ live in AC) | 300 | 14 | MathFin `BlackScholes/GreekSigns.lean` (diff: ours are `_mine` variants — the delta is the upstream content) |
| HW core + calibration + exact repricing | `builds/lean/hw_scratch.lean` (+ live in AC) | 767 | ~33 | MathFin `FixedIncome/` (new HullWhite module) |
| Curve bootstrapping | `builds/lean/hw_bootstrap.lean` (+ live in AC) | 662 | 45 | MathFin `FixedIncome/` (new Bootstrapping module; includes the private bisection engine rebuild) |
| MC pricer | `builds/lean/mc_pricer.lean` (+ live in AC) | 490 | 8 | MathFin `Probability/` or `BlackScholes/` (new MC module) |
| CMS convexity adjustment | `builds/lean/cms_scratch.lean` (+ live in AC) | 499 | 11 | MathFin `FixedIncome/` (new CMS module) |
| Cox-intensity credit | `builds/lean/cox_scratch.lean` (+ live in AC) | 709 | 20 | MathFin `FixedIncome/` (new Cox module) |
| Jamshidian swaption decomposition | `builds/lean/jamshidian_scratch.lean` (+ live in AC) | 607 | 18 | MathFin `FixedIncome/` (HullWhite swaption module; the forward-measure bridge is the honest remaining research step) |
| Forward equations (2 stages) | `builds/lean/ForwardEqScratch.lean` (+ live in AC) | 1,273 | 22 audited | MathFin `Foundations/` (new ForwardEq module) |
| Gyöngy core + hitoid drop | `builds/lean/GyongyScratch.lean` (+ live in AC) | 1,146 | 18 | MathFin `Foundations/` (new Gyongy/mimicry module) |
| Itô contribution (stages 1–5d + CrossHorizon) | `builds/lean/ItoContribution.lean` (+ live in AC) | 6,702 | 27 | MathFin `Foundations/` — **already ported**: `mathfin/MathFin/Foundations/ItoFormulaAdaptedDrift.lean` (6,189 lines, root-imported, uncommitted in the mathfin working tree) |
| CrossHorizon consistency | `mathfin/MathFin/Foundations/ItoIntegralCrossHorizon.lean` (ported, verified at the pin; archive `builds/lean/itointegral-crosshorizon-port-test.lean`) | 394 | 6 | **already in the mathfin tree, uncommitted** |
| MathFin Itô-drift port (stage 1) | `mathfin/MathFin/Foundations/ItoDriftExpectation.lean` (in the mathfin tree, root-imported at MathFin.lean:219) | — | 2 | **already in the mathfin tree, uncommitted** |

**Also in `builds/lean/` — snapshots, drafts, and port-tests (not promotion targets):**
`ItoContribution-stage5a.lean` and `itocontribution-stage5d.lean` (stage snapshots of the
Itô build), `itocontribution-stage5b-wip.lean` + `itocontribution-stage5b-fix.lean` (the
known-incomplete stage-5b drafts — the WIP copy that briefly lived in the AC clone was
removed; the archive copy here is canonical), `itoformula-adapteddrift-port-test.lean` and
`itointegral-crosshorizon-port-test.lean` (byte-fresh port-test copies of the two MathFin
modules, verified at the AC pin), and `hw_bootstrap-axioms.log` (the axiom-audit
transcript). `hw_calibration.lean` was removed from the archive (byte-identical duplicate
of `hw_scratch.lean`, verified with `cmp` before deletion).

All files: zero `sorry`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
only. Verification rev (updated 2026-10-14): the **AC build face** —
`AmericanPutConvexity/.lake/packages/mathlib` @ 81a5d257, toolchain v4.32.0, via
`lake env lean <file>` in AmericanPutConvexity (see AGENTS.md §Name-verification
convention; the historical "pin 784a831" referred to AC's packaged MathFin, which is
the same face's MathFin side — items 1–19 all compile there; the promoted modules'
canonical gate is mathfin's CI trio at v4.33.0-rc1).

## Path A — MathFin upstream PRs (the primary venue)

> **STATUS UPDATE (2026-10-14, promotion session — supersedes the series text below where they
> disagree; the original text is kept as the historical plan):**
> - **PR-1 is COMMITTED AND PUSHED** (verified by read-only `.git` decodes: mathfin branch
>   `ito-drift-expectation`, HEAD `b46e9b4` = `refs/remotes/fork/ito-drift-expectation`; fork =
>   `leafyoung/formal-mathfin`). The "3 modules in the working tree, uncommitted" premise is stale.
>   Remaining: open the PR on GitHub (user credentials).
> - **PR-2/PR-3 scope CORRECTED**: the proposed homes already exist as committed, root-imported
>   modules (`Foundations/HullWhiteCalibration.lean`, `Foundations/MonteCarloPricer.lean` — put-only).
>   PR-2 = 3-lemma delta + calibMean refactor; PR-3 = call-variant layer + multi-D seed + terminal
>   cross-checks. Both BUILT, V-passed, and STAGED in the mathfin working tree
>   (`builds/lean/promotions/pr{2,3}-*.patch` + PR descriptions).
> - **PR-4 (Cox), PR-5 (CMS), PR-6 (Bootstrapping)**: new `FixedIncome/` modules — BUILT, V-passed,
>   STAGED (`Cox.lean`, `CMS.lean`, `Bootstrapping.lean` + three `MathFin.lean` root-import lines;
>   patches + descriptions in `builds/lean/promotions/`). PR-6 ships self-contained (private
>   bisection engine, shadow-free under `MathFin.Bootstrapping`) with the public-`Bisection`
>   switch disclosed as follow-up — `Foundations/Bisection.lean` EXISTS at mathfin HEAD (the
>   pinned-rev map in QUEUE.md is stale on this).
> - **Blocker for the commit step**: the Mimosa hook hard-blocks commits (workspace AND mathfin)
>   on two PRE-EXISTING path-traversal flags in mathfin's own third-party tooling
>   (`tools/formalization_yaml.py:432`, `scripts/hammer_lakefile_patch.py:56`) — user disposition
>   needed; a full rescan (seal `sha256:7cea9e8c…`) does not clear it. All work is preserved as
>   working-tree changes + patches; nothing lost.
> - Local verification vehicle throughout: the AC build face (v4.32.0/mathlib 81a5d257) port-test
>   compiles, all axiom-clean; the canonical gate remains the CI trio (v4.33.0-rc1) per PR.
> - **Path C (2026-10-14)**: (a) DONE — public artifact repo
>   [`leafyoung/study-mathlib-builds`](https://github.com/leafyoung/study-mathlib-builds),
>   tag + release `v1.0.0` (tracked `builds/lean/` content + provenance README +
>   Apache-2.0 + tarball; deliberately EXCLUDES the workspace's copyrighted Bagaria
>   PDFs). (b) DONE — **Zenodo DOI: `10.5281/zenodo.23355884`**
>   ([zenodo.org/record/23355884](https://zenodo.org/record/23355884)); deposit
>   23355884 published 2026-10-14 (user token via `.env`; checksum-verified tarball,
>   metadata: software/Apache-2.0/open, related to the artifact repo + mathfin fork).
>   Path C is COMPLETE.

The mathfin tree (`github.com/formal-applied-math/formal-mathfin`) accepts PRs through
its documented pipeline (`CONTRIBUTING.md`): PR template, CI gates
(`pytest tests/ -q` → `tools.verify.ledger status` → `lake build`), coverage.md rows
with faithfulness status (`full`/`library_wrapper`/`reduced_core`/`placeholder`;
placeholder must be 0), axioms audits (byte-fresh `AxiomAuditGen.lean`), house style
(one theorem per file for non-trivial, helpers `private`, minimal comments, Mathlib
headers, `field_simp; ring` algebra close-outs, `bs_identity` for BS derivations).

**PR series (in dependency order):**

- **PR-1 (ready now, 3 modules already in the mathfin working tree):**
  `ItoDriftExpectation.lean` + `ItoFormulaAdaptedDrift.lean` +
  `ItoIntegralCrossHorizon.lean` + the two root-import lines. Verification already
  done (port-test compiles at the pin; docker commands recorded in QUEUE.md).
  Remaining: commit the three modules + root import on a branch from mathfin HEAD
  (3559d7a), run the CI trio in docker, open the PR against
  formal-applied-math/formal-mathfin referencing MathFin issue #175's thread if the
  maintainers prefer bundling.
- **PR-2 (short work): Hull–White module** — promote `hw_scratch.lean` →
  `MathFin/Foundations/HullWhite.lean` (or `FixedIncome/HullWhite.lean`): house header,
  `namespace MathFin.HullWhite`, the 14 audited theorems (deterministic part, Gaussian
  law, exponential-Gaussian bond moment, calibration identity, exact repricing).
- **PR-3 (short work): MC pricer module** — promote `mc_pricer.lean` →
  `MathFin/Probability/MonteCarloPricer.lean`-shaped: the 8 theorems (pairwise-SLLN
  consistency — the Etemadi strengthening — CLT with identified variance, closed-form
  second moments, the BS-put bridge). Note the environment constraint: the i.i.d.
  ensemble is hypothesized (the pin's `MathFin.Probability.ProductMeasure` is a broken
  phantom; Mathlib's product-measure construction is the future substrate — recorded).
- **PR-4 (medium): Cox credit module** — promote `cox_scratch.lean` (20 theorems,
  deterministic + restricted-Cox scoping).
- **PR-5 (medium): CMS module** — promote `cms_scratch.lean` (11 theorems).
- **PR-6 (medium): bootstrapping module** — promote `hw_bootstrap.lean` (45 decls;
  includes the private bisection engine rebuild — flag in the PR that the pin lacks
  `Foundations/Bisection.lean` and the module is self-contained for that reason).
- **PR-7+ (research-gated): Y-existence, Heston exponent, variable-coefficient
  forward equation** — the coverage map's gated items.

**Per-PR checklist (from mathfin/CONTRIBUTING.md):**

1. Fork formal-applied-math/formal-mathfin, branch, copy the module(s) + root-import
   lines, `docker compose pull verify` + `lake build` in the verify container.
2. The CI trio: `pytest tests/ -q`, `python3 -m tools.verify.ledger status`,
   `lake build` — all green.
3. `docs/coverage.md` row per theorem, faithfulness `full` — with **one disclosed
   exception**: `cox_scratch.lean`'s `cdsFairSpread_TV_balances` is `library_wrapper`-
   shaped (its proof is a direct instantiation of the pin's
   `cdsFairSpread_TV_cash_flow_balance` cash-flow balance, with annuity-positivity
   discharged — its own docstring discloses this), so its coverage row takes
   `library_wrapper` + an `UPSTREAM_CITATIONS` entry. All other theorems across the
   builds are `full`.
4. Axiom audit: byte-fresh `AxiomAuditGen.lean` regeneration (CI-checkable).
5. House style pass: headers, one-theorem-per-file for non-trivial theorems,
   `private` helpers, minimal comments, tactic style (`field_simp; ring`,
   `bs_identity` for BS-family).
6. PR description: statement, the honest hypothesis list, the verification transcript,
   and the course/QUEUE reference for provenance.

## Path B — AmericanPutConvexity upstream

The AC repo (robertmartin8/AmericanPutConvexity) has no CONTRIBUTING.md or PR
template — contributions are ordinary GitHub PRs to the repo owner. The builds are
AC-external (standalone files importing MathFin), so the natural AC contribution
would be an `examples/`-style folder or a docs pointer, not the files themselves.
Recommendation: keep the builds in the mathfin PR series (Path A) and cite them from
AC issues/discussions if the owner wants them.

## Path C — Versioned archive (Zenodo/DOI)

`builds/lean/` is the complete reproducible artifact (11 files + QUEUE.md +
PUBLISHING.md; regeneration: elan 4.32.0 + the AmericanPutConvexity clone, each file
checks with `lake env lean <file>`). A GitHub release tag on this workspace repo (if
published) or a Zenodo upload of a `builds/lean/` zip gives a citable snapshot per
milestone. Do this at each Tier-1 completion (it is now due for the current state).

## Path D — The course documents it

The mdbook course (76 lessons) is the prose layer: lessons 0020/0030/0031/0032/0034/
0047-spec are the build narratives; lesson 0038's build-status sections and the
coverage map are the living ledger. Keep them in sync as PRs land (flip QUEUE.md
statuses, add "landed upstream" notes).

## The immediate next actions (in order)

1. **Commit the current builds/lean state** (Jamshidian + the publishing plan).
2. **PR-1**: the three MathFin modules are already in the mathfin working tree,
   port-verified — branch + commit + docker verify + PR. (Needs the user's GitHub
   credentials/fork; the files and commands are ready.)
3. **PR-2/3/4/5/6/7 promotions**: module-ize each scratch file per the checklist
   (one short session each).
4. **Audit re-run** (tools/ProofDependencyAudit.lean --replay) after the AC-tree
   additions, if any scratch file is ever promoted into the AC lib target.

# Stub E-pass memo — lesson 0062 (rank 2–3, constraint cost, §12.6 calibration)

Date: 2026-10-14 · E-pass by flash-explorer (read-only; grep + pdftotext verification, no
compile run, no lesson edits). Follows the flip register of 0054/0058/0068
(proved core + explicit gated boundary).

## Verdict: **full-with-scope-cut**

Lesson 0062 can flip STUB → FULL **now**, teaching the proved core and gating the rank
theory loudly. The stub's BLOCKED reason had two conjuncts; exactly one has since been
discharged:

1. ~~"the affine engine (lesson 0033) … [has no] machine-checked home"~~ — **discharged**.
   Build-queue item 1 (`builds/lean/QUEUE.md:42`): "Affine engine stages 1–4 (OU+CIR
   invariance, Riccati flows, CIR bond) | 0033 | DONE" → `builds/lean/AffineEngineScratch.lean`
   (906 lines). Extended by items 18/19 (`QUEUE.md:59-60`): `cir_existence_scratch.lean`
   (CIR existence) and `heston_scratch.lean` (794 lines, 2D affine exponent, zero sorry,
   29/29 standard-three axioms per the item-19 record).
2. "the rank table, the several-levels theorem" need lesson 0035's finite-rank build —
   **still true**. No shift-space / dim-span-of-translates / quasi-exponential
   classification exists in any clone (re-checked this pass: nothing in `builds/lean/`,
   nothing in `mathfin/`; the ch12 scan ledger's "none found" still holds), and lesson
   0035's build was never queued — `QUEUE.md` tail: "no item IN FLIGHT at build level —
   items 1–19 all DONE … NEXT: the 12 stub lessons per the model-coverage-map registry".

The remaining gate is NOT a small build: shift representations `S_a S_{a'} = S_{a+a'}`,
the Cayley–Hamilton argument on the shift-invariant space (Thm 12.5), the Cauchy
exponential equation (Prop 12.3), Lemma 12.6's smoothing lemma, and Ex 12.2's
partial-fractions pole argument together are a full Tier-2 item. So this is not
needs-build; it is a scope cut: teach what landed, gate §12.2.6-as-theorem /
§12.2.7 / Thm 12.8 / general Thm 12.10, exactly as 0068 taught stochastic survival and
gated intensity-option pricing.

## Proved content (landed names, file:line, matched to chapter equations)

Build-face rule respected: `builds/lean/*.lean` names below are cited from the landed
files themselves (they compile only against `AmericanPutConvexity/.lake/packages/mathlib`);
mathfin names grepped in `mathfin/`; Mathlib names grepped on the build face.

### §12.3 — the affine engine and the two corners (strongest attachment)

| Landed name | Where | Chapter content |
|---|---|---|
| `ouGenerator_expAffine` | `builds/lean/AffineEngineScratch.lean:90` | §12.3's generator view, verbatim 1D: applying the generator to `e^{φ+ψx}` returns `(c₀ + c₁x)·e^{φ+ψx}` with the bracket affine in x — the chapter's "$Le^{ψx} = (bψ + ½aψ²) + x(βψ + ½αψ²)e^{ψx}$" (p. 222), here `c₁ = −κψ`, `c₀ = aψ + σ²ψ²/2` |
| `ouBracket_affine` | `AffineEngineScratch.lean:106` | "Riccati is the shadow of a two-dimensional invariant family" (p. 222) — the bracket `(c₀, c₁)` map is the Riccati system's right-hand side |
| `bondSlope`, `bondSlope_ode`, `bondSlope_at_zero` | `AffineEngineScratch.lean:129,152,161` | Ex 12.4 (Vasicek Riccati solved by hand): `B(τ) = (1−e^{−κτ})/κ` solves the B-Riccati ODE with `B(0)=0` (chapter works with `−B`; scan ledger: "Vasicek — the Riccati equations solved by hand; B(τ) = −G") |
| `bondSlope_eq_vasicekBondB` | `AffineEngineScratch.lean:312` | ties the engine to the rank-one anchor `vasicekBondB` (`mathfin/MathFin/FixedIncome/VasicekBondPrice.lean:73`) |
| `bondProfile`, `bondProfile_pde` | `AffineEngineScratch.lean:230,250` | the affine ansatz substituted into the pricing PDE and matched powers of x — Thm 12.10's proof mechanism (p. 220–221), 1D Gaussian |
| `riccatiFlow` (`hasDerivAt_riccatiFlow`) | `AffineEngineScratch.lean:176,191` | the ψ-Riccati flow consumed by the bond profile |
| `cirGenerator_expAffine`, `cirBracket_affine` | `AffineEngineScratch.lean:346,359` | square-root corner invariance — §12.3: "the tractable models are the Gaussian ones (Σ const) and the square-root ones (Σ ∝ √x)" (p. 221) |
| `cirBondB`, `cirBondLogA`, `cirBondPrice_affine` | `AffineEngineScratch.lean:609,700,843` | **Def 12.9 instantiated**: an affine term structure `P = exp(A + B·v)` with both Riccati functions verified by ODE, on the square-root corner (p. 220) |
| `cirBondPrice_pde` | `AffineEngineScratch.lean:881` | the discounted-PDE check behind Thm 12.10's proof |
| `hestonGenerator_expAffine2`, `hestonBracket_affine` | `builds/lean/heston_scratch.lean:258,276` | the 2D engine: generator on the exp-affine family `e^{A+B_x x+B_v v}`; x-coefficient ≡ 0 — the chapter's "Heston's … closed-form characteristic function is Theorem 12.10 applied to the log-price rather than to a bond" (p. 221) |
| `hestonTransform_pde`, `hestonTransform_terminal` | `heston_scratch.lean:702,715` | closed-form 2D affine transform + terminal data (item 19 headline) |

### §12.6 — calibration anchors (the model class whose κ-invisibility is taught)

| Landed name | Where | Chapter content |
|---|---|---|
| `hw_reprices_curve` | `builds/lean/hw_scratch.lean:788` | §12.6 bullet 1: "The initial curve is matched exactly and for free, by (12.15)" (p. 230) — the repricing is EXACT, machine-checked |
| `hwBondPrice_affine` | `hw_scratch.lean:575` | affine bond `P(0,T) = A(T)·e^{−B(T)r₀}` with the κ-dependent `vasicekBondB` verbatim — the HW rung of the chapter's ladder (Ex 12.3, p. ~223) |
| `hwVar_eq_interval`, `hwKernel_integral_sq` | `hw_scratch.lean:705,248` | the state spread (Calc 12.11: σ√T = state spread, p. 227): integrated-rate variance = ∫B(τ)²dτ |
| `blackPayerSwaption`, `blackReceiverSwaption`, `swaption_payer_receiver_parity` | `mathfin/MathFin/Futures/Black76.lean:91,96,101` | the European swaption strip that §12.6 bootstraps σ(t) to (p. 230); re-exported by `Futures/Swaption.lean` |
| `jamshidian_decomposition`, `receiverSwaption_hwStateBond_decomposition`, `receiverSwaption_black76` | `builds/lean/jamshidian_scratch.lean:171,424,520` | European exercise priced exactly in the one-factor instance — the instruments κ is invisible to; `vasicekBondB_pos` (`:258`) supplies the sign hygiene |
| `meanReversionHalfLife` | `mathfin/MathFin/FixedIncome/Vasicek.lean:102` (now also re-exported by `FixedIncome/MeanReversionHalfLife.lean:19`) | reading κ off the curve |
| `vasicekBondPrice_eq`, `vasicekBondPrice_affine` | `VasicekBondPrice.lean:230,267` | the rank-one affine anchor (lesson 0035's spine, already taught) |

### §12.2.6 — eq 12.12 as algebra (enablers verified on the build face, lemma not landed)

Eq 12.12 itself — `(a+b)^k e^{−κ(a+b)} = Σⱼ C(k,j) a^{k−j}e^{−κa} b^j e^{−κb}` (p. 213,
"This is an identity per increment rather than in a limit, so it holds pathwise and
exactly") — is a one-line consequence of two names **verified on the build face this
pass**:

- `add_pow (h : Commute x y) (n : ℕ)` — `AmericanPutConvexity/.lake/packages/mathlib/Mathlib/Data/Nat/Choose/Sum.lean:34` (`Commute` is automatic on ℝ);
- `Real.exp_add : exp (x + y) = exp x * exp y` — `AmericanPutConvexity/.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:209` (this face moved it out of the old ExpLog files); also evidenced in use by landed, compile-verified code at `hw_scratch.lean:578` (`← Real.exp_add`).

Also verified on the build face: `Matrix.aeval_self_charpoly`
(`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:211`) — the Cayley–Hamilton engine the
stub cites for Thm 12.5 (still correct); `Real.continuous_sqrt` and `Continuous.sqrt`
(`Mathlib/Analysis/Real/Sqrt.lean:95,476`) — eq 12.23's limit, should the optional
micro-build be run.

## Gated boundary (teach as chapter math, page-verified; no Lean attachment claimed)

1. **The rank reading of the profile table** (§12.2.6, p. 213): "x e^{−κx} ↦ 2 states"
   etc. is a theorem about `dim span{shifts}` — lesson 0035's shift-space build, unbuilt.
   The differential-equation column (`(D+κ)²g = 0`, …) is calculus and may be taught, but
   the "states" column must be presented as the 0035 build's payoff, not as landed.
2. **Ex 12.2 as a theorem** (p. 214): distinct simple poles ⟹ all λⱼ = 0. The
   partial-fractions/limit argument is not formalized; keep chapter-sourced.
3. **Lemma 12.6 / Thm 12.7** (§12.2.7, pp. 215–216): smoothing + several-levels
   quasi-exponential classification — pure 0035-build content.
4. **Cheyette (x, y) state, Thm 12.8** (eq 12.14/12.15): still absent from every clone
   (re-checked).
5. **General n-dimensional Duffie–Kan Thm 12.10** (pp. 220–221): the n-dim statement and
   its polynomial-identification step are not landed; the lesson teaches the machinery
   through the three landed instances (1D Gaussian, 1D square-root, 2D Heston) and says so.
6. **Calc 12.13 / eq 12.23 as Lean** (p. 229): spread vol √(σ1²+σ2²−2ρσ1σ2) → σ1−σ2 and
   its minimality over ρ — elementary, taught as chapter arithmetic with the verified
   numbers (2s10s 11% vs 44% at ρ=0.9, ratio 4.0; 2s30s 32% vs 49%, ratio 1.5, at
   κ = 3%, β(n) = (1−e^{−κn})/(κn)); not landed. See optional micro-build below.
7. **PCA** (eq 12.21/12.22, p. 229) and the **quadratic-growth / Feller aside**
   (§12.5, p. 230): nothing landed; the scan already routes Feller to reinforcement.

## Chapter anchors (pdftotext of `resources/fixed-income-notes-chapters/ch12-markovian-term-structure-models.pdf`; PDF page = printed page, offset +0)

- p. 213, §12.2.6: eq 12.12 + "pathwise and exactly" + the profile table
  (e^{−κx}→1, xe^{−κx}→2, x²e^{−κx}→3, two roots→2, cosine→2, 1/(1+x) and e^{−κ√x} → none).
- p. 214, Ex 12.2: pole argument; "one state as a calendar shape, infinitely many as a
  tenor shape"; ch. 14 structure remark.
- pp. 214–216, §12.2.7: eq 12.13; Lemma 12.6 (p. 215); Thm 12.7 statement + converse (pp. 215–216).
- pp. 220–222, §12.3: Def 12.9; Thm 12.10 + Riccati system; the two-corners remark
  (p. 221); Heston-CF-as-Thm-12.10 (p. 221); generator view `Le^{ψx}` (p. 222).
- pp. 227–229, §12.5: Calc 12.11/12.12 context; eq 12.21/12.22; **Calc 12.13 (p. 229)**:
  eq 12.23, the κ=3% table, "the model has not assumed a view on decorrelation so much as
  assumed it away".
- pp. 230–231, §12.6: calibration bullets; "κ is the single largest model risk in a
  callable book"; the four setting methods (correlations/PCA/CMS spread options/Bermudan
  ratio); β (ch. 10) and mixing weight (ch. 11) parallel; ch-12-vs-ch-13 remark
  (cross-link to lesson 0063).

## Section skeleton (each section names what it teaches / attaches to)

1. `# Lesson 0062 — Rank, cost, and the parameter nobody can see` + Goal line
   (successor to 0035's rank-one spine; links 0033/0035).
2. Motivate — the two questions: what does a second factor cost, and which parameter
   does the fitting never see (pp. 213, 229, 230).
3. `## Establish — eq 12.12, pathwise and exact` — the binomial split taught as algebra:
   enablers `add_pow` (build face `Data/Nat/Choose/Sum.lean:34`) + `Real.exp_add`
   (build face `Analysis/Complex/Exponential.lean:209`); the hump = HW's state plus one
   (p. 213). Rank reading flagged → gated boundary.
4. `## Establish — the engine the Riccati machinery runs on` — `ouGenerator_expAffine`
   (`AffineEngineScratch.lean:90`) = the chapter's generator identity; `bondSlope_ode` +
   `bondSlope_eq_vasicekBondB` (`:152,312`) = Ex 12.4; `cirBondPrice_affine` (`:843`) =
   Def 12.9 on the square-root corner; `hestonGenerator_expAffine2` /
   `hestonTransform_pde` (`heston_scratch.lean:258,702`) = Thm 12.10 applied to the
   log-price. General Thm 12.10 stated as chapter math → gated boundary.
5. `## Establish — what a factor costs (Calc 12.13)` — eq 12.23 as chapter arithmetic
   with the verified table (p. 229); anchored at the model level by `hwVar_eq_interval`
   (`hw_scratch.lean:705`, the state spread) and the one-factor `jamshidian_scratch`
   instance; "no dial" (p. 229) cross-links ch. 20 / lesson 0070.
6. `## Establish — the parameter nobody can see (§12.6)` — κ-invisibility as chapter
   teaching; anchored: `hw_reprices_curve` (`hw_scratch.lean:788`, bullet 1's exactness),
   `hwBondPrice_affine` (`:575`), the Black swaption strip (`Black76.lean:91,96,101`),
   `receiverSwaption_black76` (`jamshidian_scratch.lean:520`); the β/λ parallel →
   lessons 0059/0061; the ch-13 remark → lesson 0063.
7. `## The gated boundary — stated plainly` — items 1–7 of the gated list above.
8. Connect — ch. 13/14 structure remarks (pp. 214, 231); `hw_bootstrap.lean` /
   `mc_pricer.lean` pointers for how the calibration would actually run.
9. ask-your-tutor admonish → `## Primary source` (ch. 12, pp. 206–232) →
   `## Exercises` → `## Answers` (keep/refine the stub's binomial exercise, now
   answerable from §3's enablers).

## Stale references in the current stub text (mdbook/src/lessons/0062-rank-cost-calibration.md)

1. Lines 3–6 (BLOCKED header): "the affine engine (lesson 0033) … [has] no machine-checked
   home" — STALE: `AffineEngineScratch.lean` landed (QUEUE item 1 DONE), plus
   `heston_scratch.lean` (item 19).
2. Lines 36–37: `meanReversionHalfLife (Vasicek.lean)` — still correct
   (`Vasicek.lean:102`), but the module now also lives as
   `mathfin/MathFin/FixedIncome/MeanReversionHalfLife.lean` (re-export); cite either.
3. Lines 38–39: "Duffie–Kan … none found in the clones" — needs nuance: the general
   theorem is still absent, but three concrete affine-bond instances (Vasicek, CIR,
   Heston 2D) are landed; Cheyette (x, y) and shift-space remain absent (re-verified).
4. Lines 43–46 ("What's blocked"): "the cost calculation (12.23) and the κ-invisibility
   discussion presuppose the lesson-0033 affine engine" — STALE on two counts: the
   engine is landed, and eq 12.23 is ρ-σ arithmetic independent of any engine; §12.6's
   anchors (`hw_reprices_curve`, Black swaptions, Jamshidian) did not exist when the
   stub was written.
5. Lines 49–53 ("Path to unblock"): step (2) "Land lesson 0033's affine engine" is DONE;
   the flip no longer waits on step (1) — the rank theory becomes the lesson's gated
   boundary instead of its blocker.

## Optional micro-build (NOT required for the flip; would upgrade two taught claims)

A ~50-line `builds/lean/rank23_scratch.lean` could land:
- `expBinomSplit` (eq 12.12) from `add_pow` + `Real.exp_add`;
- `spreadVol_ge` (eq 12.23's minimality: ρ ≤ 1, σ1,σ2 ≥ 0 ⟹ √(σ1²+σ2²−2ρσ1σ2) ≥ σ1−σ2)
  and `spreadVol_tendsto` (ρ → 1) from `Real.continuous_sqrt` / `Continuous.sqrt`
  (build face `Analysis/Real/Sqrt.lean:95,476`) plus a sq-monotonicity step.
Closest existing substrate for style/hygiene: `AffineEngineScratch.lean` (pure-Mathlib
deterministic core) and `jamshidian_scratch.lean:258` (`vasicekBondB_pos`). Note: a
monotone-sqrt lemma name (`sqrt_le_sqrt`-class) was NOT located on the build face in this
pass — the builder must pin it first. Compiles against the AmericanPutConvexity face per
AGENTS.md.

## Checks run / not run

- Ran: `pdftotext resources/fixed-income-notes-chapters/ch12-markovian-term-structure-models.pdf /tmp/ch12.txt`
  (1,773 lines) and read §12.2.6 (pp. 213–214), §12.2.7 (pp. 214–216), §12.3 (pp. 220–222),
  §12.5 Calc 12.13 (p. 229), §12.6 (pp. 230–231) in the extraction.
- Ran: grep inventories of `builds/lean/{AffineEngineScratch,heston_scratch,hw_scratch,cms_scratch,jamshidian_scratch}.lean`,
  `mathfin/MathFin/FixedIncome/*.lean`, `mathfin/MathFin/Futures/{Black76,Swaption}.lean`,
  `mathfin/MathFin/Foundations/{MarketMakingRiccati,ItoIntegralCovariation}.lean`;
  every name reported above was found at the cited line this session.
- Ran: build-face greps into `AmericanPutConvexity/.lake/packages/mathlib/` for
  `add_pow`, `Real.exp_add`, `Matrix.aeval_self_charpoly`, `Real.continuous_sqrt`,
  `Continuous.sqrt` (cited above); `sqrt_le_sqrt` NOT found in the paths searched.
- Not run: `lake env lean` on any file (E-pass is grep/pdftotext-only per the
  name-verification convention; the builder re-verifies on the compilation face).
  Substrate compile status is taken from `QUEUE.md` items 1–19 (all DONE, V-passed) —
  not re-verified by compilation here.

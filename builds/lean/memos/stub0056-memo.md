# Memo — E-pass for flipping stub lesson 0056 (two curves and curve risk)

**Date**: 2026-10-14. **Dispatcher**: build-queue stub-flip pass (E-pass on flash, per
ROUTING.md; subject from the stub registry — 9 stubs remain after 0068's flip).
**Subject**: `mdbook/src/lessons/0056-two-curves-curve-risk.md` (STUB; registered
SUMMARY.md:132; registry rows model-coverage-map.md:49 and :126).

**Read this ask**: the stub in full (39 lines); `resources/fixed-income-notes-chapters/scans/ch07-scan.md`
in full; `pdftotext resources/fixed-income-notes-chapters/ch07-curve-construction-linear-products.pdf`
→ /tmp/ch07.txt (1572 lines; §7.5–7.9 = extraction lines 672–1572, read in full; printed
page = PDF page, offset +0, page markers matched at extraction lines 733/863/1015/1111/1223/1327/1419/1516);
the sibling memo `builds/lean/memos/stub0068-memo.md` (format/register); lesson files
0029/0030/0040/0042 confirmed present. Modules opened line-by-line this ask:
`mathfin/MathFin/FixedIncome/{FRA,InterestRateSwap,YieldCurve,DurationSensitivity,ForwardMeasure,CMS,HazardCurve,ZCB,ForwardRate,Bootstrapping}.lean`,
`mathfin/MathFin/Foundations/Numeraire.lean`, `builds/lean/{hw_bootstrap,cms_scratch,mc_pricer}.lean`,
`builds/lean/QUEUE.md` (items 13–19), `builds/lean/promotions/` listing.

---

## 1. Verdict: **full-with-scope-cut**

The stub's blocker — "little provable mathematics the stack can yet anchor on"
(0056:3–5) — is **half dead**. The stub predates the Tier-1 completion: since it was
written, the stack landed (i) the **change-of-numéraire engine** with two concrete
executions (the machinery of eq. 7.13's static content), (ii) the **sensitivity layer**
it explicitly called "assembleable but not assembled" (DurationSensitivity, CMS
derivatives), and (iii) **bootstrapping as a proved algorithm** (hw_bootstrap, item 13).
What remains without substrate is real but delimitable: the **Gaussian-posterior layer**
(§7.5), the **meeting-step front end** (§7.6), the **two-curve floating-leg object**
(§7.7's headline formula), and the **conditional form** of eq. 7.13.

The flip teaches the proved spine — the curve dictionary held *abstractly* (which *is*
the chapter's "P^proj is bookkeeping" thesis, proved), collateral-discounting as a
numéraire-seat choice, and curve risk as proved derivatives w.r.t. curve inputs — and
gates the four gaps above in an explicit honest-boundary section, chapter-sourced only.
No build is required for an honest flip. (If the orchestrator prefers a build-first
flip, the smallest unlock is named in §7 — it is one scratch file, est. 100–150 lines.)

---

## 2. Blocker audit — the stub's three blocked items, re-verified one by one

1. **"Two-curve pricing needs a second discounting object … so every `zero_iff` lemma
   doubles and couples" (0056:27–29) — FALSE in this form.** The landed zero_iff layer
   is *abstract*: `payerSwapValue_eq_zero_iff` holds for any `A ≠ 0` with P0, Pn, K
   free (InterestRateSwap.lean:53, both faces), and `fraValue_forwardRate_eq_discount_difference`
   holds for arbitrary P1, P2 (FRA.lean:53). Nothing couples. The two-curve par/FRA
   identities are *instances* of landed algebra; what is missing is only the floating-leg
   *object* (the ΣδF^proj·P^disc sum) and its single-curve telescoping collapse — a small
   definitional build, not a doubling of the zero_iff layer.
2. **"Curve as posterior … needs the statistical layer (lesson 0040's frontier)"
   (0056:31–32) — STILL TRUE, and heavier than the stub implies.** §7.5 needs
   joint-Gaussian conditioning (eqs. 7.8/7.9). This ask grepped the AC-pin mathlib:
   Gaussian laws/processes are materialized
   (`Mathlib/Probability/Distributions/Gaussian/` incl. `Multivariate.lean`,
   `IsGaussianProcess/`), but **no conditioning/posterior API** — grep for cond-API in
   the Gaussian tree and GaussianProjectiveFamily.lean returned nothing materialized.
   No builds/lean or mathfin file touches GP regression (grep-verified). Research-gated
   heavy build, not a "smallest build".
3. **"Curve risk needs the sensitivity layer … assembleable but not assembled"
   (0056:29–31) — STALE.** It is assembled: `hasDerivAt_bondPriceDisc`
   (DurationSensitivity.lean:83 AC face) is the price-derivative layer; and CMS's
   `hasDerivAt_cmsCurveRate`/`hasDerivAt_cmsCurveRate'` (cms_scratch.lean:154/:180,
   AC-face-compiled; CMS.lean:164/:190 at mathfin HEAD) are literally **derivatives of a
   par rate with respect to a curve input** — §7.9's mathematics for exactly the input
   kind the chapter names. Plus the rebuild-and-reprice loop of §7.9 ("shift the quote,
   rebuild the entire curve, reprice") is hw_bootstrap's proved repricing theorem
   (QUEUE.md:54, item 13 DONE; `boot_reprices_all`, axiom log standard-three).

The stub's *absence* claims re-verified TRUE this ask: `grep -rn -i "multicurve|projection.*curve|collateral|two.curve|tenor.basis|cross.currency" mathfin/MathFin/ --include="*.lean" -l`
→ **zero files**; posterior/GP/meeting/OIS greps over FixedIncome → only false positives
(VasicekSDE:45 "Gaussian", Cox's Poisson "survival" chain). No meeting-step, OIS, or
posterior object exists anywhere in the clone.

---

## 3. Proved content the flipped lesson can teach (lemma ↔ chapter equation)

Face discipline: MathFin build face = AC's packaged copy (Foundations/Numeraire.lean,
FixedIncome/{FRA,InterestRateSwap,ForwardMeasure,YieldCurve,DurationSensitivity,ZCB,
ForwardRate,HazardCurve}.lean verified present there this ask; **CMS.lean and
Cox.lean are absent at the AC pin** — verified by directory listing — so CMS names are
cited from the AC-face-**compiled scratch** `builds/lean/cms_scratch.lean` (zero sorry:
the only "sorry" hit is header text at :15; item 14 DONE, QUEUE.md:55) with mathfin-HEAD
line numbers as the promoted-home cross-reference, exactly the 0068-memo pattern.

### 3a. The curve dictionary is landed *abstractly* — which proves §7.7's thesis

- eq. 7.1 (forward from the curve) = **`MathFin.fraForwardRate`** (FRA.lean:46, both
  faces): `(P1 / P2 - 1) / δ`.
- **`fraValue_forwardRate_eq_discount_difference`** (FRA.lean:53): substituting the
  curve forward into the FRA value gives the discount algebra — **arbitrary P1, P2**.
  Read with P := projection-bookkeeping, this is the two-curve FRA's value identity;
  the code never asks what P "is". This is the proved form of the chapter's §7.7
  remark "P^proj is bookkeeping … not the price of anything" (p. 133): the landed
  algebra holds for *any* positive inputs.
- **`fraValue_zcb_eq_zero_iff`** (FRA.lean:67): the single-curve instantiation — the
  special case where the bookkeeping happens to be a price.
- eq. 7.3 (par swap rate) = **`MathFin.parSwapRate`** (InterestRateSwap.lean:43):
  `(P0 - Pn) / A` — the *general ratio* the chapter says survives the two-curve world.
- **`payerSwapValue_eq_zero_iff`** (InterestRateSwap.lean:53, hypothesis `A ≠ 0` only)
  and **`payerSwapValue_zcb_eq_zero_iff`** (:62); **`annuity`** (:35), **`annuity_pos`**
  (:47) — the annuity-positivity seed the numéraire step consumes (module docstring:23
  already names the annuity "the numéraire `A`").

### 3b. Collateral sets the discount (eq. 7.13's static content) — the engine is landed

Chapter (p. 134, Calc 7.26): `V_t = E^P[e^{−∫_t^T c(s)ds} V_T | F_t]`; "the collateral
account is the numeraire" (p. 134, :1421–1430 of the extraction).

- **`MathFin.numeraireMeasure`** (Foundations/Numeraire.lean:86, both faces),
  **`numeraireMeasure_isProbabilityMeasure`** (:97, normalization
  `𝔼^Q[N_T/B_T] = N₀/B₀` — "where the martingale content enters", taken as an explicit
  hypothesis), **`MathFin.changeOfNumeraire`** (:124): price invariance
  `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]` with **arbitrary positive `BT NT : Ω → ℝ`** —
  a collateral account slots into the seat directly; no new theorem exists to prove.
- **`forwardMeasure`/`forwardMeasure_isProbabilityMeasure`/`forwardMeasure_price`**
  (ForwardMeasure.lean:65/:71/:83, both faces): the T-bond execution
  `e^{−rT}·𝔼^{Q^T}[X] = 𝔼^Q[e^{−rT}·X]` — **eq. 7.13 with c ≡ r constant is this
  identity's shape**; the collateral-account execution (deterministic c) is the same
  instantiation with `BT := e^{∫₀ᵀ c}`.
- **`annuityMeasure`/`annuityMeasure_isProbabilityMeasure`/`annuityMeasure_price`**
  (cms_scratch.lean:292/:301/:325; CMS.lean:303/:312/:336): the annuity execution —
  the engine's third run, after stock and T-bond (cms_scratch header :30–37). §7.3's
  "swap rates are martingales in the annuity measure" in static form, plus
  **`cms_adjustment_nonneg`** (scratch:362) as the worked consequence.
- Honest gate kept visible: the engine's dynamic half
  **`changeOfNumeraire_setIntegral_eq`** (Numeraire.lean:171) is a set-integral
  martingale statement, **not** a conditional-expectation pricing object — the
  `E[·|F_t]` form of eq. 7.13 stays behind the same σ-algebra fence recorded for the
  Cox build (`cox_scratch.lean:88–90`, "Fubini-not-condExp").

### 3c. Curve risk (§7.9) — the sensitivity layer is landed

- **`hasDerivAt_cmsCurveRate`** (cms_scratch.lean:154 / CMS.lean:164):
  `S'(x) = −(P₀+C)/(δ(C+x)²)` — **the par rate's sensitivity to a curve input**;
  **`hasDerivAt_cmsCurveRate'`** (:180/:190) the second derivative; the CMS rate
  functional's input x *is* a discount-curve input — "risk is a property of the
  construction" (p. 137) made precise: change the construction, change the functional.
- **`cmsCurveRate_convexOn`** (scratch:256 / CMS.lean:266) and
  **`payerSwapValue_update_eq_zero_iff`** (scratch:127 / CMS.lean:137) — the par
  identity transported to curve form.
- **`hasDerivAt_bondPriceDisc`** (DurationSensitivity.lean:83) +
  **`bondPriceDisc_deriv_eq_neg_modified_duration_times_price`** (:102): the yield-side
  DV01/duration layer (Def 7.20) — the *yield-DV01* half of the chapter's
  yield-DV01 ≠ curve-DV01 distinction, proved.
- **The rebuild-and-reprice loop is a proved algorithm**: `builds/lean/hw_bootstrap.lean`
  (item 13, QUEUE.md:54; 45 decls; private bisection engine, FRA/swap threshold bridges
  `fraRoot_parForward` :356 / `fraRoot_agrees_with_pin` :366 / `swapRoot_is_par` :435,
  indexed step theorem `boot_step_err` :529, repricing theorems `boot_reprices_all` /
  `boot_reprices_range`, flat-curve capstone; axiom log
  `builds/lean/hw_bootstrap-axioms.log` records standard-three for the capstones).
  §7.9's "shift the quote of one calibrating instrument, rebuild the entire curve, and
  reprice" is machine-checked end to end on the single-curve stack.
- Triangular bootstrap backbone: **`couponBondPricingEq`** (YieldCurve.lean:50),
  **`bootstrap_solve`** (:56 AC / :63 HEAD), **`bootstrap_solve_first`** (:66/:72),
  **`bootstrap_solve_second`** (:75/:82), **`bootstrap_consistency`** (:84/:90).

---

## 4. What stays gated (honest boundary — quoted/verified absences)

1. **§7.5 curve-as-posterior (eqs. 7.5–7.10, Calc 7.21/7.22, the ±2bp…±287bp bands,
   empirical kernel, Marchenko–Pastur)**: research-gated. Needs joint-Gaussian
   conditioning; the AC pin materializes Gaussian laws (Multivariate.lean,
   GaussianProjectiveFamily.lean) but no conditioning/posterior API; no stack file
   touches GP regression (grep-verified this ask). Teach chapter-sourced only — the
   *remarks* (bands independent of the quotes' values; σₑ→0 recovers the bootstrap;
   Nelson–Siegel as infinitely strong prior) are stated as chapter claims, never as
   stack facts.
2. **The two-curve floating-leg object** `Float(0) = Σ_j δ^p_j F^proj P^disc` (p. 133)
   and its single-curve telescoping collapse: **not landed** (no floatingLeg/telescope
   lemma in FixedIncome — grep-verified; `payerSwapValue` bakes the telescoped form
   P0 − Pn into its *definition*, InterestRateSwap.lean:37–39). The formula is taught
   chapter-sourced; the "nothing cancels" contrast is the honest boundary's sharpest
   example. (Smallest-build item 1, §7.)
3. **§7.6 the front end is a step function (eq. 7.11 forward substitution, eq. 7.12
   sensitivity (T−m)/T, Calc 7.24/7.25 meeting risk + butterfly)**: nothing landed
   (grep-verified). The arithmetic is elementary (finite sums; one division per
   meeting; the bump sensitivity is a finite difference), so this is the natural
   *next build*, not research — until then, chapter-sourced.
4. **eq. 7.13's conditional/process form**: gated at the conditional-expectation fence
   (same as the Cox build's recorded fence, cox_scratch.lean:88–90); only the static
   time-0 content is teachable from the engine (§3b). The time-varying deterministic-c
   execution is likewise not instantiated (constant-c = `forwardMeasure_price` shape
   only).
5. **§7.8 objects** (tenor basis, Def 7.27 cross-currency basis swap, Def 7.28 OAS):
   contract definitions and diagnostics; no basis/OAS object in the stack
   (grep-verified). Teach chapter-sourced per the lesson-0067 precedent (FULL lesson
   teaching unbuilt contract math, noted in stub0068-memo.md §5).
6. **"Summing the buckets recovers the parallel number"** (§7.9): linearity remark,
   not landed; chapter-sourced. Key-rate-duration objects: not landed.
7. Do **not** overclaim: no "collateral measure", no "projection curve", no "basis
   swap", no "OAS" object exists in any clone — every such formula in the flipped
   lesson must carry its chapter anchor (§5) and, where algebra is claimed, route
   through the §3 landed names.

---

## 5. Chapter anchors (ch07-curve-construction-linear-products.pdf; printed = PDF page, offset +0)

All from this ask's pdftotext (/tmp/ch07.txt; line refs are extraction lines):

- p. 122–123: §7.5 opens (:672–731); Figure 7.2, four interpolation schemes, forwards
  3.2%–6.6% vs monotone convex 3.8%–6.4% (:715–729).
- p. 123: eq. 7.5 z = average of forwards (:747–753); Calc 7.21, prior eq. 7.6,
  observation eq. 7.7, posterior eqs. 7.8/7.9 (:756–804).
- p. 124: reading the formulae; σₑ→0 recovers the bootstrap; H·Var[f|z]·Hᵀ = 0
  (:809–830); three constructions, one prior; Nelson–Siegel loadings (:831–847).
- p. 125: empirical kernel eq. 7.10, Marchenko–Pastur edge (:848–900).
- p. 126: Calc 7.22, the bands table ±2bp…±110bp…±287bp (:945–998); "What the band is
  for" — cheapness-as-z-score, covariance enters at aggregation (:1004–1099).
- p. 128: §7.6 opens (:1101–1115); Calc 7.23, eq. 7.11, one division per meeting
  (:1116–1151).
- p. 129–131: Calc 7.24, eq. 7.12 ∂q/∂step = (T−m)/T (:1162–1246); Calc 7.25, exposure
  matrix E_ik = (T_i−m_k)⁺, 1:−2:1 butterfly, factor-of-60 instrument choice
  (:1247–1280); block-prior remark (:1292–1310).
- p. 132–133: §7.7 opens (:1312–1331); projection/discount bullets (:1332–1341);
  "what P^proj(0,T) is not"; three numbers at six months (:1344–1363).
- p. 134: **Calc 7.26, eq. 7.13** (:1371–1392); r drops out; rehypothecation step,
  VM vs IM / MVA (:1401–1415); "the collateral account is the numeraire" (:1421–1430);
  basis swaps traded in their own right (:1431–1434).
- p. 135–136: §7.8 opens (:1436–1444); tenor basis (:1446–1466); Def 7.27 cross-currency
  basis swap, negative b (:1477–1505).
- p. 136–137: Def 7.28 OAS; "a property of a model, not of a bond"; OAS-tracks-vol
  diagnostic (:1509–1541).
- p. 137–138: §7.9 curve risk; parallel DV01 = annuity for a single swap; key-rate
  durations; "risk is a property of the construction" (:1543–1560); references
  Hagan–West / Piterbarg / Bianchetti (:1566–1572).

Precedent check: lesson 0067 (FULL) teaches unbuilt contract math (eq. 16.6, Defs
16.8/16.9) with chapter anchors — recorded in stub0068-memo.md §5. This flip has a
*larger* proved fraction (§3a–3c) than 0067's.

---

## 6. Section-by-section skeleton for the flipped lesson

**H1**: Lesson 0056 — Two curves and curve risk. **Goal**: ch. 7 §7.5–7.9 — the curve
is a construction (posterior, step function, two-curve stack), and risk is a property
of the construction; proved substrate: the abstract swap/FRA algebra, the numéraire
engine and its executions, the sensitivity layer, bootstrapping-as-algorithm; honestly
gated: the posterior, the meeting curve, the floating-leg object, conditional eq. 7.13.

1. **Motivate** — "linear products are just discounting" held until it didn't: 2008
   opened the basis (p. 132–133); everything below is what the single-curve dictionary
   of 0042 and the bootstrap of 0030 silently assumed.
2. **Establish A — the dictionary is abstract (eqs. 7.1/7.3).** Teaches
   **`fraForwardRate`**, **`parSwapRate`**, **`payerSwapValue_eq_zero_iff`**,
   **`annuity_pos`**: the landed algebra holds for *arbitrary* discount inputs — the
   single-curve instantiations (`fraValue_zcb_eq_zero_iff`,
   `payerSwapValue_zcb_eq_zero_iff`) are special cases. The code already treats P as
   bookkeeping.
3. **Establish B — two curves (§7.7, p. 132–134).** The floating-leg formula
   Float(0) = ΣδF^proj·P^disc and "nothing cancels" — chapter-sourced, gate flagged
   (§4.2). The proved half: the par rate is the *general ratio* eq. 7.3 and every
   zero_iff survives unchanged because it never coupled — rerun of §3a's point in
   market terms.
4. **Establish C — collateral sets the discount (Calc 7.26, eq. 7.13 static).**
   Teaches **`changeOfNumeraire`** + **`numeraireMeasure_isProbabilityMeasure`** +
   **`forwardMeasure_price`** (constant-c case) + **`annuityMeasure_price`** as the
   pattern's third execution: which account sits in the numéraire seat is which rate
   discounts; r drops out because the collateral account funds the trade (chapter
   derivation quoted); honest gate: the conditional form (§4.4). VM-vs-IM/MVA remark
   chapter-sourced.
5. **Establish D — the front end is a step function (§7.6, p. 128–131,
   chapter-sourced).** Eq. 7.11's forward substitution and eq. 7.12's (T−m)/T done by
   hand as arithmetic; the meeting butterfly and the block-prior reading; gate note
   (§4.3): elementary but unbuilt — the natural next build.
6. **Establish E — curve risk (§7.9, p. 137–138).** Teaches
   **`hasDerivAt_cmsCurveRate`/`'`** (sensitivity to a curve input, closed form),
   **`cmsCurveRate_convexOn`** (the construction determines the functional),
   **`hasDerivAt_bondPriceDisc`** (yield side), **`boot_reprices_all`** (shift a
   quote, rebuild, reprice — proved); risk against calibrating instruments as the
   chapter's principle, with the proved single-instrument DV01 facts as its anchors.
7. **Establish F — the rest of the stack (§7.8, chapter-sourced, short).** Tenor
   basis, cross-currency basis (Def 7.27), OAS-as-residual (Def 7.28) and the
   OAS-tracks-vol diagnostic; nothing in the stack (§4.5).
8. **Honest-boundary paragraph** (the posterior, §7.5): why eqs. 7.8/7.9 are the
   chapter's deepest computation and the one thing the pin cannot yet say —
   Gaussian conditioning absent (§4.1); the bands table quoted as chapter content.
9. **Connect.** 0030 (bootstrap landed), 0042 (dictionaries), 0031/0065 (CMS
   convexity — the same functional), 0034/0066 (annuity numéraire at work),
   0063 (Jamshidian's numeraire — another seat change), 0075 hook (covariance enters
   at aggregation, §7.5's structure, p. 126), 0069 forward link (cross-currency
   basis is ch. 17's FX machinery).
10. **ask-your-tutor admonish** (include): e.g. "Ask which seat each number sits in:
    today's lesson has exactly one theorem-shaped fact per curve choice — the
    numéraire engine's normalization hypothesis. Ask what it would take to *prove*
    the annuity reprices (§ C's honest out) and why no model-free proof exists."
11. **Primary source**: ch. 7 PDF §7.5–7.9 (pp. 122–138); FRA.lean,
    InterestRateSwap.lean, YieldCurve.lean, DurationSensitivity.lean,
    ForwardMeasure.lean, Foundations/Numeraire.lean, CMS.lean (HEAD) /
    cms_scratch.lean (AC-compiled); builds/lean/hw_bootstrap.lean.
12. **Exercises + Answers** (carry the stub's unblock items forward):
    1. Two-curve FRA: show `fraValue δ P₂^disc (fraForwardRate P₁^proj P₂^proj δ) K`
       has a unique zero — from the landed algebra (Answer: the FRA.lean:70–78 proof
       needs only δ·P₂ ≠ 0).
    2. Verbatim-name: which landed lemma is eq. 7.3? (`parSwapRate`.)
    3. Constant-c eq. 7.13: match it to `forwardMeasure_price`'s identity shape.
    4. Why does P^proj price nothing? Argue from the arbitrariness of
       `fraValue_forwardRate_eq_discount_difference`'s hypotheses.
    5. By hand: bump the meeting-m step by 1bp in eq. 7.11; recover (T−m)/T.
    6. Scope fence: name the one §7.5 object the pin lacks (joint-Gaussian
       conditioning / the posterior formulas) and state it chapter-sourced only.

SUMMARY.md:132 registration already exists; the flip edits the lesson file + registry
rows (§8) in the same edit.

---

## 7. If the orchestrator prefers a build-first flip — the smallest honest build

**Not required for the verdict above.** But the smallest unlock, one scratch file
`builds/lean/twocurve_scratch.lean` on the AC face (imports
`MathFin.FixedIncome.FRA`, `MathFin.FixedIncome.InterestRateSwap`,
`MathFin.Foundations.Numeraire`, `MathFin.FixedIncome.ForwardMeasure` — all present at
the AC pin; the import pattern is proven by hw_bootstrap.lean:2–5 and
cms_scratch.lean:2–6), landing:

1. `twoCurveFloatLeg` — def: `∑ j, δ * (Pproj τ_{j−1} / Pproj τ_j - 1) * Pdisc τ_j`
   over a `Fin` schedule (§4.2's object).
2. `twoCurveFloatLeg_singleCurve_telescopes` — Pproj = Pdisc = P ⟹ the sum is
   `P τ₀ − P τ_N` (Finset-range induction; closest substrate: `payerSwapValue`'s
   P0 − Pn form, InterestRateSwap.lean:39).
3. `twoCurveParSwapValue_eq_zero_iff` — via landed `payerSwapValue_eq_zero_iff`,
   `A ≠ 0` discharged by `annuity_pos`.
4. `twoCurveFRA_eq_zero_iff` — three lines from FRA.lean:70–78's proof with
   P2 := P^disc (needs only `δ * P2disc ≠ 0`).
5. (Optional §7.6) `meetingQuote` (eq. 7.11 as a `Finset.sum` over segments),
   `meetingStep_solve` (the one-division closed form), `meetingBump_linear`
   (q_i under a 1bp bump at meeting k moves by (T_i − m_k)/T_i · 1bp — pure algebra,
   no calculus).
6. (Optional §7.7) `collateralMeasure Q c T` + `collateralMeasure_price` — the
   deterministic-c execution, template `forwardMeasure_price`
   (ForwardMeasure.lean:65–95).

Estimated 100–150 lines, zero sorry; standard-three audit per the WIP-checkpoint rule.

---

## 8. Stale references in the current stub text

| Stub location | Text | Status |
|---|---|---|
| 0056:3–5 (banner) | "little provable mathematics the stack can yet anchor on" | **STALE** — numéraire engine, sensitivity layer, bootstrap-as-algorithm all landed post-stub (§2, §3). Replace. |
| 0056:17–23 ("What the stack has") | "all lesson 0030/0042 substrate" | **Stale by omission** — no mention of Numeraire.lean, ForwardMeasure.lean, DurationSensitivity.lean, CMS/PR-5, hw_bootstrap (item 13), Bootstrapping.lean (PR-6). The cited names themselves re-verified present (AC face): `fraValue_zcb_eq_zero_iff` FRA.lean:67, `payerSwapValue_eq_zero_iff` IRS:53, `annuity_pos` IRS:47, `couponBondPricingEq` YieldCurve:50, `bootstrap_solve` YieldCurve:56, `zcb` ZCB.lean:39, HazardCurve defs :45/:51. |
| 0056:27–29 | "every `zero_iff` lemma doubles and couples" | **FALSE** — the layer is abstract; nothing couples (§2.1). Rewrite, don't delete. |
| 0056:29–31 | "curve risk needs the sensitivity layer … assembleable but not assembled" | **STALE** — assembled (DurationSensitivity:83/:102; cms_scratch:154/:180/:256) (§2.3). |
| 0056:35–38 ("Path to unblock") | (1) two-curve zero_iff duplication; (2) per-input hasDerivAt; (3) posterior gated on 0040 | (1) still open but now *instance-of-landed-algebra + one def* (§7); (2) **largely DONE** — per-*curve-input* version landed, per-*instrument* (key-rate) version open; (3) still TRUE (§4.1). Renumber. |

**Also stale outside the lesson file** (update in the flip's same edit):
`model-coverage-map.md:126` ("sensitivity layer unassembled" — false now; "two-curve
`zero_iff` duplication + lesson 0029 bridges" — rewrite per §7) and
`model-coverage-map.md:49` (row 7: keep "projection/discount two-curve world not
built" — still true (§4.2) — but augment with the landed engine/entries).

---

## 9. Verification record

Commands run this ask (all outputs quoted/summarized above):

- `pdftotext resources/fixed-income-notes-chapters/ch07-curve-construction-linear-products.pdf /tmp/ch07.txt` (1572 lines; §7.5–7.9 read in full).
- Absence greps over `mathfin/MathFin/`: multicurve/projection/collateral/tenor-basis/cross-currency → **zero files**; posterior/GP and meeting/OIS/step-curve → only false positives (VasicekSDE:45, Cox Poisson chain).
- Declaration greps on the **AC face** (`AmericanPutConvexity/.lake/packages/MathFin/`): FRA.lean:46/:53/:67; InterestRateSwap.lean:35/:39/:43/:47/:53/:62; ForwardMeasure.lean:65/:71/:83; DurationSensitivity.lean:83/:102; Foundations/Numeraire.lean:86/:97/:124/:171; YieldCurve.lean:50/:56/:66/:75/:84; ZCB.lean:39; HazardCurve.lean:45/:51. Directory check: **CMS.lean and Cox.lean absent at the AC pin** (listing verified).
- Declaration greps at **mathfin HEAD** for the three absent modules: CMS.lean:108/:137/:164/:190/:266/:287/:303/:312/:336/:375; Bootstrapping.lean inventory; FRA/IRS line-identity with the AC face confirmed (same line numbers).
- AC-face-compiled scratch evidence: `builds/lean/cms_scratch.lean` (:98/:127/:154/:180/:256/:277/:292/:301/:325/:362/:418; zero real sorry — only header text at :15) and `builds/lean/hw_bootstrap.lean` (:356/:366/:435/:529 + capstones; zero real sorry — header at :72; axiom log `hw_bootstrap-axioms.log` records standard-three for `boot_reprices_all`/`fraBootstrap_flatCurve` etc.). QUEUE.md items 13/14 **DONE** rows read (:54–55).
- AC-face mathlib greps for §4.1: `Mathlib/Probability/Distributions/Gaussian/` listing (Basic/CharFun/Fernique/Multivariate/HasGaussianLaw/IsGaussianProcess — no conditioning/posterior file); cond-grep in GaussianProjectiveFamily.lean → nothing. Caveat (per stub0068-memo §8): the AC face materializes a *partial* mathlib source tree, so source-grep negatives there are suggestive, not conclusive — stated as such.
- Registry/SUMMARY: model-coverage-map.md:49 and :126 read; SUMMARY.md:132 read.

**Not run this ask** (reported as such): no compile gates — `cd AmericanPutConvexity && lake env lean …` was not executed (E-pass is read-only; the builder re-verifies on the compilation face as backstop per AGENTS.md §Name-verification). The compile status of hw_bootstrap/cms_scratch is **recorded** (QUEUE.md:54–55 + axiom logs), not re-executed. `mdbook build`/`check_links.py` not run (no lesson file was edited).

**Verdict restated**: **full-with-scope-cut.** Flip 0056 to FULL on the §3 substrate
with the §4 gates quoted in the honest-boundary paragraph and the §6 skeleton; apply
the §8 registry corrections in the same edit. The §7 build is optional enrichment, not
a precondition.

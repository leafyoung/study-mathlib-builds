# Memo — E-pass for flipping stub lesson 0068 (options on credit)

**Date**: 2026-10-14. **Dispatcher**: build-queue stub-flip pass (QUEUE.md footer, line 71:
"NEXT: the 12 stub lessons per the model-coverage-map registry").
**Subject**: `mdbook/src/lessons/0068-options-on-credit.md` (STUB; registered SUMMARY.md:144).

**Read this ask**: the stub in full; `resources/fixed-income-notes-chapters/scans/ch16-scan.md`
in full; `pdftotext` of `resources/fixed-income-notes-chapters/ch16-credit.pdf` (10 pp.,
printed page = PDF page, offset +0 — extraction to /tmp/ch16.txt succeeded, 509 lines);
`builds/lean/cox_scratch.lean` in full (697 lines); the promoted
`mathfin/MathFin/FixedIncome/Cox.lean` in full (653 lines); `builds/lean/QUEUE.md`;
`builds/lean/promotions/pr4-description.md`; `builds/lean/port-test-cox.lean` (header);
lesson 0032 (`0032-tier1-cox-intensity-credit.md`) in full; lesson 0067 (opening, 40 lines);
`mdbook/src/reference/model-coverage-map.md` (ch16 rows); `mdbook/src/SUMMARY.md` (143–144);
Black76 / Credit / HazardCurve / CDSTimeVarying / PoissonInterarrival declarations on both
faces (greps quoted below).

---

## 1. Verdict: **full-with-scope-cut**

The stub's blocker — "stochastic intensity not yet built" — is dead: the Cox-intensity
build landed (item 15, QUEUE.md:56) and was promoted to MathFin (PR-4). A FULL lesson 0068
can now teach, with proved substrate: *why* credit options need random intensity (§16.7's
determinism complaint), the stochastic survival identity **eq. (16.7)** (proved at the
Fubini level), the payoff algebra `RiskyAnn(T)(s(T)−K)+` from the landed leg definitions,
and the annuity-positivity fact the numeraire argument consumes.

The **scope cut**: the chapter's actual pricing step — Black's formula *under the
risky-annuity numeraire measure*, plus the knockout conditioning that rescues it — has **no
substrate** and stays gated, taught as chapter-sourced contract logic, never as
stack-verified mathematics. The course already pre-gated exactly this in lesson 0032
(Answer 4, quoted in §4 below). Note the chapter's own thesis — "what makes the pricing
work is a clause, not a theorem" (p. 287) — means the lesson's *point* is teachable
precisely because the theorem-sized part is the gated part.

---

## 2. Blocker audit — both halves of the stub's blocker are now false

Stub status banner (`0068-options-on-credit.md:3-6`):

> "BLOCKED — pricing a CDS option needs the forward spread to be a martingale under the
> risky-annuity numeraire; the risky annuity does not exist in the stack (grep-verified),
> and the stochastic-intensity build (lesson 0032) it rests on has not landed."

1. **"the stochastic-intensity build (lesson 0032) it rests on has not landed" — FALSE.**
   `builds/lean/cox_scratch.lean` landed (QUEUE.md:56, item 15 **DONE**: "697 lines, 20
   theorems: constant-λ legs, deterministic λ(t) bridge with the novel a.e. set-equality
   mechanism, stochastic CDS spread headline, restricted-Cox mixing stretch landed;
   enlargement out of scope") and was promoted as `mathfin/MathFin/FixedIncome/Cox.lean`
   (PR-4; `promotions/pr4-description.md`; fork main @ 5708258 per QUEUE.md:71). Lesson
   0032 itself carries the banner "**Build status**: LANDED" (0032:7), and the registry
   already records it ("Random intensity (Cox) **LANDED in the workspace**",
   model-coverage-map.md:63).
2. **"the risky annuity does not exist in the stack (grep-verified)" — FALSE.** It now
   exists twice over, with the positivity lemma the stub's own unblock step (2) asked for:
   - `MathFin.Cox.riskyAnnuity` (constant λ; `mathfin/MathFin/FixedIncome/Cox.lean:135`),
     closed form `riskyAnnuity_eq` (:139), **positivity** `riskyAnnuity_pos` (:165);
   - `MathFin.Cox.cdsAnnuity` under deterministic λ(t) (`Cox.lean:432`),
     **positivity** `cdsAnnuity_pos` (:453, "hazardSurvival_pos" discharged).
   Grep re-run this ask: `grep -rn -i "riskyann\|risky annuity\|cdsOption\|cds option\|
   annuity measure\|forward spread" mathfin/MathFin/` — every hit is the deterministic
   Cox module; **no** CDS-option object, no annuity measure, no forward-spread process
   exists anywhere in the clone (so the stub's *remaining* two absences, quoted at
   0068:34-35, are still true).
3. Therefore the true residual blocker is different from the stub's: not "λ isn't random"
   but "**no risky-annuity measure change / no forward-spread random variable / no
   conditioning-on-survival machinery**" — a strictly smaller, precisely delimited gap
   (§4).

---

## 3. Proved content the flipped lesson can teach (lemma ↔ chapter equation)

Face discipline: **MathFin build face = AC's packaged MathFin, pin 784a831**
(`AmericanPutConvexity/.lake/packages/MathFin/`), per QUEUE.md:24-36. Names below were
grepped on the **AC face first**; `Cox.lean` itself exists only at mathfin HEAD (4d82234;
verified: `ls AmericanPutConvexity/.lake/packages/MathFin/MathFin/FixedIncome/ | grep -i
"cox|hazard"` returns only `HazardCurve.lean`) — its content is verified on the AC face via
the recorded port-test (`promotions/pr4-description.md:36-39`: `cd AmericanPutConvexity &&
lake env lean ../builds/lean/port-test-cox.lean` → exit 0, 29/29 public declarations
standard-three axioms, zero sorry; **not re-run in this E-pass** — see §8).

### 3a. Stochastic survival = eq. (16.7) — the headline the flip is built on

Chapter (p. 285): $Q(0,T) = E[\exp(-\int_0^T \lambda_s\,ds)]$.

- **`MathFin.Cox.cox_mixing_survival`** (`mathfin/MathFin/FixedIncome/Cox.lean:599`):
  on the product of an intensity-path space with the unit-exponential-clock space,
  `(μ₁.prod (expMeasure 1)) {p | Λ t p.1 < p.2} = ∫⁻ ω, e^{−Λ t ω} ∂μ₁` —
  `P(τ > t) = E[e^{−Λ_t}]` with **Λ a random cumulative process** (only time-section
  measurability + pathwise nonnegativity hypotheses). This *is* eq. (16.7) for the
  survival probability, at the Fubini (iterated-integral) level.
- **`MathFin.Cox.cox_mixed_survival`** (`Cox.lean:638`): same for a default time `τ` on
  the product space whose survival event is pointwise `{Λ t p.1 < p.2}` — packaged as
  `P(τ > t) = E[e^{−Λ_t}]`; the per-path inverse construction is the documented scoping
  fence (docstring :636-637).
- **`MathFin.Cox.cox_mixing_survival_le`** (`Cox.lean:618`): the mixed survival is ≤ 1.
- Deterministic layer (the bridge the chapter takes in §16.1): `cox_survival_timeVarying`
  (`Cox.lean:389`, `P(τ > t) = e^{−Λ(t)} = hazardSurvival h t`), `cox_cdf_timeVarying`
  (:403), with `cumHazard_strictMono` (:245) and `cumHazard_surjOn_Ici` (:251) — the
  clock-inversion mechanism. This is eq. (16.1) with λ deterministic (p. 279).

### 3b. Legs, par spread, and positivity under λ(t) = eqs. (16.2)/(16.3) + the numeraire seed

- `MathFin.Cox.cdsAnnuity` (`Cox.lean:432`) = `∫₀ᵀ e^{−rs} S(s) ds` — the RiskyAnn kernel;
  `cdsLosses` (:437) = `∫₀ᵀ e^{−rs} h(s) S(s) ds` — the eq. (16.2) protection kernel;
  `premiumLeg` (:441), `protectionLeg` (:444); `cdsFairSpread_TV` (:448) = eq. (16.3)
  `s = Prot / RiskyAnn` as `(1−R)·losses/annuity`.
- **`MathFin.Cox.cdsFairSpread_TV_balances`** (`Cox.lean:511`): premium leg = protection
  leg ↔ `c = cdsFairSpread_TV r h R T` — direct instantiation of the AC-face
  `cdsFairSpread_TV_cash_flow_balance` (`.../MathFin/FixedIncome/CDSTimeVarying.lean:69`,
  verified on the AC face), annuity positivity discharged via `cdsAnnuity_pos`. This is
  the landed fact that makes the marking algebra (eq. 16.6) one line: a contract struck
  at `K` has value `K·Ann − s·Ann = −(s−K)·Ann` from the two leg definitions.
- **`MathFin.Cox.cdsAnnuity_pos`** (`Cox.lean:453`) and `riskyAnnuity_pos` (:165): the
  risky annuity is **strictly positive** — precisely the property the chapter's numeraire
  step consumes ("The risky annuity is a positive traded portfolio, so it is an admissible
  numeraire", p. 286). Proved on deterministic curves; the stochastic-annuity version is
  gated (§4).
- Density pricing at zero discount: `cox_defaultProb_density` (`Cox.lean:571`,
  `P(τ ≤ a) = ∫₀^a h·S`), via `defaultDensity_antideriv` (:466) and
  `clockTail_eq_defaultDensity` (:486) — eq. (16.2)'s density-against-survival structure
  (the `r > 0` case is a recorded gap, §4).
- Constant-λ regression: `cdsFairSpread_TV_const` (`Cox.lean:557`) collapses to
  `cdsFairSpread lam R = λ(1−R)` (`Credit.lean:86`, verified on the AC face at the same
  line) — Thm 16.5 / eq. (16.4), already lesson 0046's; `cdsLegs_balance_const` (:195)
  realizes the AC-face `cds_leg_equality` (`Credit.lean:94`, AC face verified) at the
  concrete integral.

### 3c. The rate-side Black pattern (the thing to lift — exists, on the AC face)

`MathFin/Futures/Black76.lean` (identical line numbers on both faces — grep-verified on
the AC face): `blackPayerSwaption` (:91), `blackReceiverSwaption` (:96),
`swaption_payer_receiver_parity` (:101), **`blackPayerSwaption_eq_bsVGarman`** (:114,
hypothesis `hA : 0 < A` — the annuity in the discount slot, `F·A` the asset). Honest
reading of the statement: these are **formula identities**; the martingale content sits in
the hypothesis `BSCallHyp Q F K 0 σ T Z` ("the futures price has zero drift under Q",
Black76.lean:41). A CDS-option lift must *prove* the risky-annuity-measure drift theorem
for the forward spread — that theorem does not exist (§4). The rate-side annuity-measure
execution the pattern follows is the CMS module's numéraire engine (QUEUE.md:55, item 14:
"annuity measure = numéraire engine's third execution").

### 3d. Teachable-from-landing: §16.7's determinism complaint

With deterministic `h`, the spread is the *known number* `cdsFairSpread_TV r h R T`; there
is no `s(T)` distribution, so `(s(T)−K)+` is a deterministic max and an "option" is its
intrinsic value. This chapter argument (p. 285, lines 378-383 of the extraction) is now
anchored: the landed definitions make "the whole future spread curve is known today"
literally true in the code. CIR cross-link for §16.7: `cirVariance_mean`
(`builds/lean/cir_existence_scratch.lean:487`, item 18) and `cirBondPrice_pde`
(`builds/lean/AffineEngineScratch.lean:881`, item 1) — but process-level CIR existence
stays gated (QUEUE.md:59).

---

## 4. What stays gated (honest boundary — quoted gate language)

1. **Conditioning on survival — the knockout clause's mathematical content — is
   pre-gated by the landed build itself.** `builds/lean/cox_scratch.lean:86-87` (Scope
   fences): *"**Filtration enlargement is out of scope**: in restricted Cox the *same*
   filtration carries the intensity and the compensator; the general Cox case (τ's own
   information entering F) is Tier-2. **Nothing here conditions on survival.**"* And
   lesson 0032, Answer 4 (`0032-tier1-cox-intensity-credit.md:128-130`): *"Anything
   conditioning on **default survival itself** (**CDS options**, counterparty exposure
   conditional on no-default) — needs enlargement of filtrations / the semimartingale
   decomposition of τ (Tier-3)."* The flipped lesson must present Black-on-surviving-paths
   as chapter-sourced contract logic, not stack math.
2. **The conditional-expectation object** (`cox_scratch.lean:88-90`): *"The
   conditional-expectation σ-algebra statement — `E[1{τ>t} | σ(path)]` as a `condExp`
   object — is replaced by its Fubini (iterated-integral) content, which is what pricing
   consumes. The Doob–Dynkin upgrade needs the per-path inverse construction on the
   product space."* So even the *statement* "the spread is a martingale in the
   annuity measure" has no home: no σ-algebra conditioning object, no annuity process.
3. **The discounted density identity** (`cox_scratch.lean:94-97`): *"The discounted
   density identity `E[e^{−rτ}1{τ≤T}] = ∫₀ᵀ e^{−rs} h S ds` for `r > 0` needs
   generalized-inverse continuity … the `r = 0` case needs no inverse and is landed."*
4. **The measure-change layer** (`cox_scratch.lean:98-102`): the
   `GirsanovAdaptedTheta`/`GirsanovPredictableTheta` machinery (both files verified
   present on the AC face, `Foundations/GirsanovPredictableTheta.lean`) is *"the proved
   predictable-θ Girsanov machinery the driven-intensity case consumes; **not exercised
   in this build**."* Promotion gate, same content (`pr4-description.md:30-32`): *"the
   stochastic headline is restricted to the constructed-process scoping recorded in the
   course (enlargement out of scope)."*
5. **Grep-verified absences (this ask)**: no `RiskyAnn(T)` as a random variable (all
   annuity definitions are deterministic-time integrals, `Cox.lean:135/:432`); no forward
   spread `s(T)` random variable; no risky-annuity measure or numeraire-change theorem
   (the only measure-change objects on the credit side are none; `ForwardMeasure.lean` is
   the bond-numeraire T-forward measure, `FixedIncome/ForwardMeasure.lean:65-71`); no
   index-option front-end-protection term; no CMCDS / recovery-lock / digital objects.
6. **"Stochastic CDS spread headline" — do not overclaim the phrase.** QUEUE.md:56 and
   pr4-description.md:19-20 use it for the mixing layer (`Cox.lean:599-648`): a
   *stochastic survival/leg identity* on the product space. **No module defines a spread
   process `s(t)` or prices anything under stochastic intensity.** The flipped lesson must
   not cite the phrase as if a stochastic spread object existed.
7. **Face note for the flip's B-pass**: `MathFin.Cox` names are verified at mathfin HEAD
   (4d82234, materialized) + recorded AC-face port-test; a future build *extending* Cox
   either targets mathfin CI directly (promotion vehicle) or grows house lemmas privately —
   QUEUE.md:33-36 rule. `Cox.lean` is absent at the AC-face pin 784a831 (verified by
   directory listing, §3 preamble).
8. Minor §16.7 gate: process-level CIR intensity existence (QUEUE.md:59, item 18 finding:
   "process-level CIR existence stays gated") — the SDE `dλ = κ(θ−λ)dt + η√λ dZ` as a
   process is not built; only the explicit squared-OU slice and its mean identity.

---

## 5. Chapter anchors (ch16-credit.pdf; printed page = PDF page, offset +0)

All verified from this ask's pdftotext (/tmp/ch16.txt; line refs are extraction lines):

- p. 279: eq. (16.1) survival as discount factor (lines 15-22).
- p. 280: Calc 16.2 protection leg, eq. (16.2) (lines 46-55); Calc 16.3 premium leg +
  accrual (lines 56-73); Def 16.4 par spread, eq. (16.3) (lines 74-86).
- p. 280-281: Thm 16.5 credit triangle, eq. (16.4) (lines 97-101); Ex 16.1 (125-138).
- p. 284: Calc 16.7 off-market value, eq. (16.6) (lines 321-327) — **lesson 0067 owns**.
- p. 285: Def 16.8 CS01, Def 16.9 jump-to-default (lines 363-367) — **lesson 0067 owns**;
  §16.7 begins (line 374); eq. (16.7) (lines 384-393); Hull-White inadmissible + CIR
  square-root process (lines 407-414).
- p. 286: Calc 16.10 Jensen direction (lines 419-428); §16.8 begins (line 430);
  **Def 16.11** payer/receiver CDS swaptions (lines 436-437); payoff
  `RiskyAnn(T)(s(T)−K)+` + numeraire + "prices by Black" (lines 438-443); lognormal
  convention (lines 444-445); **numeraire-can-vanish remark begins** (lines 446-459).
- p. 287: knockout single-name vs index option with front-end protection (lines 460-465);
  "what makes the pricing work is a clause, not a theorem" (lines 466-468); CMCDS
  (lines 469-472); recovery locks and digitals (lines 473-477).
- p. 287-288: §16.9 marginals-vs-joint doorway to ch. 18 (lines 479-498) — reinforcement,
  cross-link to 0070.

Precedent check: the house pattern for teaching chapter math without a dedicated Lean
build is lesson 0067 (FULL; teaches eq. 16.6 + Defs 16.8-16.9 with the scan noting "the
off-market value and CS01/JTD split must be built", ch16-scan.md:133-137) — the flip
follows the same discipline, with a *larger* proved fraction (§3a-3b).

---

## 6. Section-by-section skeleton for the flipped lesson

**H1**: Lesson 0068 — Options on credit · **Goal**: ch. 16 §16.8 (Def 16.11) — why credit
options exist only under random intensity, what the risky annuity does as numeraire, why
the knockout clause (not a theorem) carries the Black argument; proved substrate: eq. (16.7)
as `cox_mixing_survival`, the legs/positivity layer, the rate-side Black pattern; honestly
gated: pricing *under* the risky-annuity measure.

1. **Motivate — the deterministic market has no options.** §16.7's complaint (p. 285):
   with λ deterministic the spread *is* `cdsFairSpread_TV r h R T` — a known function —
   so `(s(T)−K)+` is a deterministic max (intrinsic only). Ch. 9's deterministic-vol
   complaint in a new market. Links: 0032 (Cox build landed), 0046 (triangle), 0067
   (marking).
2. **Establish A — randomness arrives, and survival is its price (eq. 16.7).**
   Teaches **`Cox.cox_mixing_survival`** (+ `cox_mixed_survival`,
   `cox_survival_timeVarying` as the deterministic bridge): `P(τ>t) = E[e^{−Λ_t}]` with
   random Λ — eq. (16.7) proved at the Fubini level. State the scoping fence (restricted
   Cox; Fubini-not-condExp) with the 0032 tip.
3. **Establish B — the payoff is an annuity times an option (eq. 16.6 → Def 16.11).**
   From the landed defs (`premiumLeg`, `protectionLeg`, `cdsFairSpread_TV_balances`):
   struck-at-K value is `−(s−K)·Ann`, so the payer's payoff at T is
   `RiskyAnn(T)(s(T)−K)+` (chapter p. 286). Teaches **`cdsFairSpread_TV_balances`** and
   **`cdsAnnuity_pos`/`riskyAnnuity_pos`** — positivity is the property that makes the
   annuity a numeraire candidate.
4. **Establish C — the numeraire argument, and the hole in it (chapter-sourced,
   p. 286-287).** Positive traded portfolio → numeraire; forward spread = traded value /
   annuity → martingale in its measure; Black exactly as a swaption. The rate-side
   pattern: **`blackPayerSwaption_eq_bsVGarman`** (annuity in the discount slot,
   `hA : 0 < A`) + `swaption_payer_receiver_parity`. The hole: the annuity *can vanish*
   (default before T) — a numeraire that can vanish is not a numeraire on that event.
   Honest-boundary paragraph: no stochastic annuity, no `s(T)`, no measure change exists
   in the stack (§4.5); the drift hypothesis `BSCallHyp` would have to be *proved* for
   the forward spread and is not.
5. **Establish D — the clause carries it (chapter-sourced, p. 287).** Knockout
   single-name: Black holds on surviving paths, "the only paths that matter"; index
   option: no knockout, carries front-end protection → Black term + forward-starting
   jump exposure (§16.6) — "not an option at all"; "what makes the pricing work is a
   clause, not a theorem." Quote the 0032 Answer-4 gate (§4.1) as the stack's own
   statement that this conditioning is Tier-3.
6. **Connect.** CMCDS = ch. 15's convexity problem in credit (link 0059/0065); recovery
   locks/digitals = 0046's λ(1−R) degeneracy resolved by a market; marginals-pinned-
   dependence-free → 0070/ch. 18 doorway; CS01/JTD from 0067 are the two legs of an
   option's risk report. CIR intensity cross-link: `cirVariance_mean` landed,
   process existence gated (§4.8).
7. **ask-your-tutor admonish** (required: Part X lesson citing style models; optional per
   conventions — include it): e.g. "Ask where exactly the Black argument breaks on the
   default paths: the annuity is zero there, so the ratio defining the forward spread is
   0/0 — undefined, not merely volatile. Seeing the division break is understanding the
   clause."
8. **Primary source**: ch. 16 PDF (§16.7-16.8, pp. 285-287); `MathFin/FixedIncome/Cox.lean`,
   `Credit.lean`, `HazardCurve.lean`, `CDSTimeVarying.lean`, `Futures/Black76.lean`;
   `builds/lean/cox_scratch.lean`.
9. **Exercises + Answers** (carry the stub's attempt exercise forward as Ex 1):
   1. Payoff algebra from eq. (16.6) → `RiskyAnn(T)(s(T)−K)+` (chapter + landed legs).
   2. Verbatim-name: which proved lemma gives survival under *random* intensity?
      (`cox_mixing_survival`.)
   3. Constant-λ regression: which lemma collapses the time-varying spread to the
      triangle? (`cdsFairSpread_TV_const` → `cdsFairSpread λ R`.)
   4. Why is a vanishing numeraire not a numeraire on the default event, and which
      clause rescues single-name options? (knockout.)
   5. Index vs single-name: same units, not the same instrument — what is the extra term
      and why is it "not an option"? (front-end protection.)
   6. Scope fence: state one pricing question the landed restricted-Cox build cannot
      answer and name the theory it needs (conditioning on survival; enlargement of
      filtrations — per 0032 Answer 4).

Register in SUMMARY.md is already done (SUMMARY.md:144); the flip edits only the lesson
file + the registry blocker line (§7 below) — same-edit discipline per AGENTS.md.

---

## 7. Stale references in the current stub text

| Stub location | Text | Status |
|---|---|---|
| 0068:3-6 (status banner) | "the stochastic-intensity build (lesson 0032) it rests on has not landed" | **FALSE now** — landed (QUEUE.md:56; promoted PR-4; lesson banner 0032:7; registry :63). Banner must be replaced. |
| 0068:4-5 | "the risky annuity does not exist in the stack (grep-verified)" | **FALSE now** — `Cox.riskyAnnuity`/`cdsAnnuity` + `_pos` (§2.2). |
| 0068:34-35 | "No risky annuity, no CDS-option numeraire argument, no vanishing-numeraire handling anywhere in the clones" | First clause **stale**; the other two re-verified TRUE this ask (grep §2.2). |
| 0068:39-42 ("What's blocked") | "the object to price does not exist until λ is random (lesson 0032)" | Premise stale: λ-random survival *is* built; the option still doesn't exist but for the narrower reason (§4). Rewrite, don't delete. |
| 0068:44-50 ("Path to unblock") | steps (1) land Cox, (2) risky annuity + positivity | Both **DONE** (step 1 = item 15; step 2 = `cdsAnnuity_pos`/`riskyAnnuity_pos`). Steps (3) lift Black through the risky-annuity measure and (4) knockout-as-event-restriction remain the real (open) path — renumber. |

**Not stale** (all re-verified this ask, AC face where materialized): `survival_eq`
(PoissonInterarrival.lean:50), `survival_factorizes` (:71), `map_firstArrival_eq_expMeasure`
(:99); `GirsanovPredictableTheta.lean` (present both faces); `blackPayerSwaption_eq_bsVGarman`
(Black76.lean:114), `swaption_payer_receiver_parity` (:101); `cdsFairSpread`
(Credit.lean:86), `cds_leg_equality` (Credit.lean:94). No lesson-0021-style stale integral
lemma here — the stub cites no integral lemma. Also stale outside the lesson file:
`model-coverage-map.md:132` still lists 0068's blocker as "stochastic intensity not yet
built / lesson 0032's build" — update in the flip's same edit.

---

## 8. Verification record

Commands run this ask (all greps/reads executed; outputs quoted above):

- `pdftotext …/ch16-credit.pdf /tmp/ch16.txt` (+ `pdfinfo`: 10 pages) — chapter read.
- Declaration greps on **mathfin HEAD**: `Credit.lean`, `HazardCurve.lean`,
  `CDSTimeVarying.lean`, `Futures/Black76.lean`, `Foundations/PoissonInterarrival.lean`,
  Foundations Girsanov listing, ForwardMeasure.lean.
- Declaration greps on the **AC build face**
  (`AmericanPutConvexity/.lake/packages/MathFin/…`): `Credit.lean:86/:94`,
  `HazardCurve.lean:45/:51/:55/:62/:91`, `CDSTimeVarying.lean:69`,
  `PoissonInterarrival.lean:50/:71/:99`, `Futures/Black76.lean:91/:96/:101/:114`,
  Girsanov listing; AC-face Cox-absence check (`ls FixedIncome | grep -i "cox|hazard"` →
  only HazardCurve).
- AC-face **mathlib** spot-checks: `intervalIntegral.integral_pos` at
  `…/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1392`;
  `intermediate_value_Icc` at `…/Mathlib/Topology/Order/IntermediateValue.lean:553`.
  Note: the AC face materializes a *partial* mathlib source tree (8,264 .lean, 0 .olean —
  oleans live in the build dir), so source-grep negatives there are not conclusive.
- Absence grep: risky-annuity/CDS-option/annuity-measure/forward-spread over
  `mathfin/MathFin/` — only deterministic Cox hits.

**Not run this ask** (reported as such, per the recording standard): the compile gates —
`cd AmericanPutConvexity && lake env lean ../builds/lean/port-test-cox.lean` and
`mdbook build` + `check_links.py`. The port-test result (exit 0, 29/29 standard-three,
zero sorry) is **recorded** at `promotions/pr4-description.md:36-39` and quoted, not
re-executed. The builder (B-pass) re-verifies on the compilation face as backstop per the
build-face convention (AGENTS.md §Name-verification).

**Verdict restated**: full-with-scope-cut. Flip 0068 to FULL on the §3 substrate with the
§4 gates quoted verbatim in the lesson's honest-boundary paragraph; apply the §7 registry
corrections in the same edit.

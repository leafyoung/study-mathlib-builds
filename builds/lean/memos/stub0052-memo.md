# Memo — E-pass for flipping stub lesson 0052 (two kinds of jump)

**Date**: 2026-10-14. **Dispatcher**: build-queue stub-flip pass (NOTES.md:667 lists 0052
among the 9 remaining stubs, all recorded build-gated).
**Subject**: `mdbook/src/lessons/0052-two-kinds-of-jump.md` (STUB; registered
`mdbook/src/SUMMARY.md:128`).

**Read/run this ask**: the stub in full; `resources/fixed-income-notes-chapters/scans/ch02-scan.md`
in full; `pdftotext resources/fixed-income-notes-chapters/ch02-price-process-characterization.pdf`
→ `/tmp/ch02.txt` (911 lines; PDF page = printed page, offset +0), §2.2 pp. 38–45 and §2.3
pp. 46–49 read in full (lines 300–911); lesson 0051 in the sections that bound 0052's scope
(`0051-price-process-characterization.md:121–207`); section maps of 0058 and 0068; the
whole `PoissonRandomMeasure.lean` (259 lines); headers/tails of `PoissonCompensatedBilinear`,
`PoissonCompensatedIsometryAdapted`, `PoissonCompensatedIntegralL2(Dense)`,
`PoissonCompensatedIntegralOperator`; `PoissonCounting`, `PoissonInterarrival`,
`PoissonThinning`, `PoissonSuperposition` declarations; `FixedIncome/Cox.lean` header +
mixing section; `builds/lean/cox_scratch.lean:80–105` (scope fences);
`builds/lean/memos/stub0068-memo.md` (face-discipline register);
`builds/lean/memos/stub0054-memo.md`/`stub0058-memo.md` present as siblings.

**Face discipline (per AGENTS.md name-verification convention)**: all MathFin names below
were grepped on the **AC face first** — `AmericanPutConvexity/.lake/packages/MathFin/`
(pin **784a831**, `git log -1`: "feat(foundations): the bracket is adapted, and it
compensates M² (#210)"). All Poisson/isometry/bracket files there are **line-identical to
mathfin HEAD** (verified by matching anchors at :79/:109/:125/:135/:215/:228/:243 in
`PoissonRandomMeasure.lean`, :50 in `PoissonCompensatedIntegralL2.lean`, :191 in
`PoissonCounting.lean`). `FixedIncome/Cox.lean` is **absent at the AC pin** (AC face
`FixedIncome/` has only CDS/CDSTimeVarying/Credit/HazardCurve — `ls` verified); its names
are verified at mathfin HEAD (4d82234) and were AC-face-verified at promotion time by the
recorded port-test (`promotions/pr4-description.md:36–39`: `cd AmericanPutConvexity &&
lake env lean ../builds/lean/port-test-cox.lean` → exit 0, 29/29 declarations, zero sorry;
**not re-run in this E-pass**) — the same disclosure discipline the 0068 flip used.
Mathlib names verified against the build face
`AmericanPutConvexity/.lake/packages/mathlib/` (81a5d257).

---

## 1. Verdict: **full-with-scope-cut**

No build is required. The stub's blocker ("the infinite-activity regime needs compensated
sums against a general Lévy measure … every compensated object in the stack sits on a
finite Poisson intensity, so the moment infinite mass appears, none applies") is **stale at
the integral layer**: `PoissonRandomMeasure` is built on a **σ-finite** mark intensity
(`structure PoissonRandomMeasure (P) (ν) [SigmaFinite ν]`,
`Foundations/PoissonRandomMeasure.lean:135–136`, AC face), and the entire
`PoissonCompensated*` architecture — isometry, orthogonality, and the extended
`itoLevyIntegralL2` CLM on the `L²` closure — is proved *in that generality*. What is
genuinely absent is the **Lévy-process layer above the integral layer** (a process with
stationary independent increments, its path variation, eq. 2.10 as a theorem) — and that is
research-gated, not a small build.

A second, more consequential scope fact the stub missed: **the chapter's own section titled
"Two Kinds of Jump" is §2.3 (pp. 46–49)** — predictable vs totally inaccessible *times*,
scheduled events vs defaults — not the §2.2 finite/infinite-variation regime split the stub
presents as the item (`0052:9` names only §2.2/Thm 2.10). The scan ledger's verdict for 0052
(`ch02-scan.md:96–98`) assigns four things: realised vs predictable QV, the two kinds of
jump, predictable vs totally inaccessible times, Cox survival-as-discount. Of these, the
**time-kind dichotomy (§2.3) is far more provable than the regime dichotomy (§2.2)**: its
intensity side is the whole landed Cox machine, and its scheduled-events side is lesson
0058's §9.8 territory. The flip should restore the scan-verdict scope, with 0051
cross-references where it already taught the material.

**The scope cut**: eq. 2.10 as a theorem, the FV/IV regime dichotomy as path statements
($\sum_{s\le t}|\Delta X_s|=\infty$ with $[X]_t<\infty$; $[X]_t=\sum(\Delta X_s)^2$;
$E[X]_t=t\int_{|x|<1}x^2\nu(dx)$), the triplet/truncation bookkeeping, the α-stable
family as objects, Itô's formula with jumps, and the announcing-sequence/inaccessibility
formalism all stay **gated**, taught as chapter-sourced structure around the proved
integral-layer core. The proved half is substantial: every finite-activity object, the
bracket moment identities, the orthogonality the chapter's own proof sketch leans on, and
the L² compensated-integral machinery that is exactly the substrate the small-jump term
would be built from.

---

## 2. Blocker audit — what in the stub's banner is dead, what survives

Banner (`0052:3–5`): *"the stack's jump machinery is Poisson-style (finite activity)
throughout; the infinite-activity regime needs compensated sums against a general Lévy
measure, i.e. Lévy–Khintchine machinery that is absent."*

1. **"Poisson-style (finite activity) throughout" — STALE.** The PRM takes σ-finite ν
   (`PoissonRandomMeasure.lean:135–136`); finiteness appears only as a **per-region**
   hypothesis on the compensated increment (`hfin : referenceIntensity ν B ≠ ⊤`,
   `poisson_law` field :142–143, `compensated_integral_zero/sq` :215/:228). An
   infinite-activity mark measure (infinite mass near the origin) is in-scope for the
   object as long as it is σ-finite — exactly the α-stable situation, where every shell
   $\epsilon_{k+1}\le|x|<\epsilon_k$ has finite mass and only the union has infinite mass.
2. **"the moment infinite mass appears, none applies" — FALSE at the integral layer.**
   `compensated_simple_isometry` (`PoissonCompensatedIntegralL2.lean:50`), the
   overlapping-box bilinear pairing (`PoissonCompensatedBilinear.lean:357`),
   `assembly_isometry` (:355), `levyClosure` (:379), `itoLevyIntegralL2` (:410) and
   `itoLevyIntegralL2_norm` (:424) — all under `[SigmaFinite ν]`. The `L²` closure of
   finite-intensity-box integrands **is** the compensated small-jump integral's home: the
   chapter's "compensated sums over successive shells … orthogonal, … summable variances …
   converge in L²" (ch. 2 p. 43, txt :592–600) is precisely an element of this closure.
   What does NOT exist at infinite mass: the pointwise compensated *count* $\tilde N(B)$
   for $\hat\nu(B)=\infty$ (no `poisson_law` to lean on), and any pathwise object.
3. **"it is absent from Mathlib as well" — SURVIVES, re-verified this ask.**
   `grep -rln "LevyProcess\|Lévy process\|levyProcess"` over build-face
   `Mathlib/Probability/` → only unrelated hits (Lévy's theorem/metric mentions in
   `BorelCantelli.lean`, `Convergence.lean`, `CentralLimitTheorem.lean`). mathfin clone:
   `grep -ril "levy" MathFin/` → only PRM/isometry provenance docstrings (the modules cite
   Applebaum Def 2.3.1/Thm 4.2.3 and `cgarryZA/LevyStochCalc`; the isometry is proved there,
   LevyStochCalc's axiom #6) plus `AxiomAuditGen.lean`. **No Lévy process object, no
   Lévy–Khintchine triplet, anywhere.**
4. **Path to unblock, step (1) "Generalize the compensated Poisson integral from
   finite-intensity marks to σ-finite Lévy measures" (`0052:48–50`) — ALREADY LANDED.**
   That generalization *is* `PoissonRandomMeasure` + the `PoissonCompensated*` family.
   Step (2) shell-sum L² convergence — half-landed: the abstract CLM on the closure exists;
   instantiating it on a *concrete* infinite-mass integrand (the shell-approximation
   argument $H\in$ `levyClosure`) is not. Step (3) triplet + $[X]_t$ — untouched, and it
   needs the process layer first.

So the honest residual blocker is: **no Lévy-process abstraction** (a time-indexed process
with stationary independent increments; càdlàg jump paths; pathwise QV), hence no eq. 2.10,
no regime dichotomy as a theorem, no $[X]_t$, no triplet — and no announcing-sequence /
totally-inaccessible-time formalism in Mathlib. A strictly smaller and precisely delimited
gate than the stub's banner.

---

## 3. Proved content the flipped lesson can teach (lemma ↔ chapter equation)

All lines AC face (`AmericanPutConvexity/.lake/packages/MathFin/MathFin/`) unless marked
HEAD; Mathlib lines are build-face.

**§2.2 Poisson machine (Calc. 2.6–2.9, Def. 2.4–2.7, Thm. 2.5):**
- Counting process from iid exponential interarrivals has Poisson$(rt)$ marginals (the
  construction half of Thm 2.5's pair; Saporito Thm 3.3.5) —
  `PoissonCounting.map_count_eq_poissonMeasure`, `Foundations/PoissonCounting.lean:191`.
- Survival law from increments alone, $P(N_t=0)=e^{-\lambda t}$, and its Cauchy-equation
  factorization $P(N_t{=}0)=P(N_s{=}0)\cdot P(N_t{-}N_s{=}0)$ (the engine of Thm 2.5's
  proof) — `PoissonInterarrival.survival_eq` (:50), `survival_factorizes` (:71),
  `Foundations/PoissonInterarrival.lean`.
- First arrival $\tau\sim\mathrm{Exp}(\lambda)$ (the §2.3 intensity side) —
  `PoissonInterarrival.map_firstArrival_eq_expMeasure` (:99).
- Poisson mean and variance, $\mathbb E[N]=r$, $\mathbb E[N^2]=r^2+r$ (Mathlib gap-fill;
  the moment content of Calc. 2.8/2.9) — `poissonMeasure_integral_id` (:79),
  `poissonMeasure_integral_sq` (:109), `Foundations/PoissonRandomMeasure.lean`. Composed
  with `map_count_eq_poissonMeasure`: $\mathbb E[N_t]=\mathrm{Var}(N_t)=\lambda t$ —
  the computation of Calc. 2.9 (b(t)=λt) and the mean behind Calc. 2.8.
- The compensated increment $\tilde N(B)=N(B)-\hat\nu(B)$ (Def. 2.7's object, box form):
  `PoissonRandomMeasure.compensated` (:158), mean-zero `compensated_integral_zero`
  (:215), second moment $\mathbb E[\tilde N(B)^2]=\hat\nu(B)$ `compensated_integral_sq`
  (:228) — the diagonal energy of the Itô–Lévy isometry — and `memLp_compensated` (:243).
- Counts are a.e. finite on finite-intensity sets — `ae_count_ne_top`
  (`PoissonCompensatedBilinear.lean:50`) — the proved form of "finitely many jumps of size
  $\ge\epsilon$ a.s." (the stub's attempt-exercise, now anchorable; ch. 2 p. 39, txt
  :387–390).

**The two-bracket split and the orthogonality core (Calc. 2.8/2.9 + Thm 2.10's proof
sketch):**
- Orthogonality of compensated increments on disjoint regions —
  `compensated_mul_compensated_disjoint` (:82) and the covariance
  $\mathbb E[\tilde N(C)\tilde N(D)]=\hat\nu(C\cap D)$, `compensated_covariance` (:95),
  `Foundations/PoissonCompensatedBilinear.lean` — the finite-intensity form of the
  chapter's "compensated sums over shells are … orthogonal, because disjoint jump sizes
  are independent" (p. 43, txt :594–596).
- Adapted/weighted bilinear pairing (the Itô–Lévy inner-product core) —
  `integral_adapted_bilinear_future` (:240), `integral_bilinear_pairing` (:357).
- The Itô–Lévy isometry for simple integrands — `compensated_simple_isometry`
  (`Foundations/PoissonCompensatedIntegralL2.lean:50`); its L²-norm form
  `simpleIntegrand_sq_integral` (`PoissonCompensatedIntegralL2Dense.lean`); the extended
  CLM `itoLevyIntegralL2` (:410) on `levyClosure` (:379) with the full-generality isometry
  `itoLevyIntegralL2_norm` (:424) — `Foundations/PoissonCompensatedIntegralOperator.lean`.
  Header of the Dense module discloses the deferred Summit (marked-predictable
  σ-algebra characterisation) — quote it when gating.
- Continuous-world bracket vocabulary (cross-ref to 0051, which already taught it):
  `predQuadVariation` (`brownian-motion/BrownianMotion/StochasticIntegral/QuadraticVariation.lean:32`),
  `condExp_sq_sub_bracket` (:255) + `bracketProcess_adapted` (:216)
  (`Foundations/BracketCompensator.lean`, AC face) — $M^2-\langle M\rangle$ a martingale.

**Finite-activity jump models (the large-jump half of Thm 2.10's proof):**
- Superposition $\mathrm{Poisson}(\lambda)+\mathrm{Poisson}(\mu)=\mathrm{Poisson}(\lambda+\mu)$
  — `poissonMeasure_conv_poissonMeasure` (`Foundations/PoissonSuperposition.lean:52`,
  re-export of Mathlib's).
- Thinning/marking — `markedPoissonMeasure_eq_prod` (:103), `thinned_streams` (:136),
  `Foundations/PoissonThinning.lean`.
- Compound-Poisson MGF — `compoundPoisson_mgf_identity` (`Actuarial/Mortality.lean:118`,
  AC face), `compoundPoisson_mgf` (`Actuarial/CompoundPoissonMGF.lean:63`).
- Merton jump-diffusion call price (the desk-facing finite-activity model) —
  `mertonCallPrice` (`BlackScholes/MertonJumpDiffusion.lean:127`, AC face).

**§2.3 the intensity kind of jump (cross-reference, do not re-teach):**
- Lesson 0051 §"dropping continuity" (`0051:121–160`) already teaches Def. 2.13/Calc.
  2.14/eq. 2.3 with anchors `survival_eq`, `survival_factorizes`,
  `survivalFromForce` (`Actuarial/Mortality.lean:38` region), `Credit.survivalProbability`
  (`FixedIncome/Credit.lean:45`), `cds_leg_equality` (:94),
  `hazard_eq_neg_log_deriv_survival` (`FixedIncome/HazardCurve.lean:72`) — all AC-face
  verified. 0052 should *use* these as the defaults-have-intensity half of the §2.3
  dichotomy and hand off to 0068 for options.
- The deeper Cox machinery (mathfin HEAD `FixedIncome/Cox.lean`, port-test disclosure
  above): `cox_survival_timeVarying` (:389), `cox_mixing_survival` (:599, the
  doubly-stochastic survival $P(\tau>t)=E[e^{-\Lambda_t}]$ at the Fubini level),
  `cox_mixing_survival_le` (:618), `cox_mixed_survival` (:638),
  `cox_defaultProb_density` (:571) via `defaultDensity_antideriv` (:466) and
  `clockTail_eq_defaultDensity` (:486), `riskyAnnuity_eq` (:139), `cdsFairSpread_TV_balances`
  (:511). Scope fences verified directly at `builds/lean/cox_scratch.lean:84–102`
  (enlargement out of scope; nothing conditions on survival).

---

## 4. What stays gated (the boundary, for the lesson's "stated plainly" section)

1. **No Lévy process object.** Nothing in the clones (or build-face Mathlib) defines a
   process with stationary independent increments; `grep` re-run this ask (§2.3 above).
   Eq. 2.10 is a statement about such a process — no home for it.
2. **No pathwise quadratic variation for jump paths.** All QV machinery in the workspace
   (`QuadraticVariationL2.lean`, `PointwiseBracket.lean`, `BracketCompensator.lean`,
   `brownian-motion`'s `QuadraticVariation.lean`) sits on Brownian/pre-Brownian objects.
   $[M]_t=N_t$ (the random staircase, Calc. 2.8) and the agreement/disagreement of the two
   brackets are taught **moment-level only** (Var = mean = λt) plus chapter-sourced prose.
   The continuous-case agreement is already taught in 0051 via `condExp_sq_sub_bracket`.
3. **Compensator as conditional expectation.** Calc. 2.6's
   $\mathbb E[N_t-a(t)\mid\mathcal F_s]=N_s-a(s)$ is not stated anywhere; the stack has the
   unconditional compensated moments and the raw material (`indep_of_disjoint_region`
   field, `PoissonRandomMeasure.lean:150–154`) but no compensator theorem.
4. **Predictable vs totally inaccessible times (Def. 2.12).** `grep -rn
   "inaccessible\|Inaccessible"` and `grep -rln "announcing"` over build-face
   `Mathlib/Probability/` + `MeasureTheory/` → **zero hits**. Vocabulary that does exist:
   `IsStoppingTime` (`Mathlib/Probability/Process/Stopping.lean:75`), `IsPredictable` for
   *processes* (`Mathlib/Probability/Process/Predictable.lean:272`, alias of
   `IsStronglyPredictable`). The dichotomy is taught chapter-sourced; its formalization is
   a declared build, not a stub-able claim.
5. **The infinite-activity integral is abstract-only.** `levyClosure`/`itoLevyIntegralL2`
   give an L² object with an isometry — no pointwise integral, no process $X_t$, no paths.
   Instantiating it on a concrete infinite-mass mark measure (e.g. the α-stable density
   $x^{-1-\alpha}$ on $(0,1)$) needs the shell-approximation argument $H\in$ `levyClosure`
   (monotone shell truncation, $\int_{|x|<\epsilon}x^2\nu\to0$) — landed nowhere.
6. **Triplet $(b,\sigma^2,\nu)$ and truncation bookkeeping** (ch. 2 p. 44, txt :666–676):
   absent everywhere. Teach as chapter-sourced desk remark (why $b$ is not intrinsic).
7. **Itô's formula with jumps** (p. 45): every `ItoFormula*` module is continuous-path;
   the jump-sum term has no home. Chapter-sourced only.
8. **α-stable processes** (p. 44): no object. The boundary computation
   ($\int_0^1 x^{-\alpha}dx<\infty\iff\alpha<1$) is chapter-sourced prose; build face has
   the engine (`integral_rpow`, `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:147`,
   hypothesis `-1 < r`) if a future build wants to harden it — see §6.
9. **fBM QV trichotomy (Calc. 2.11)**: already taught in 0051 §"where characterization
   stops" — do not duplicate; forward-reference.
10. **Cox fences** (inherited from the build's own scope fences, `cox_scratch.lean:84–102`):
    nothing conditions on survival; no conditional-expectation object; measure-change layer
    not exercised.

---

## 5. Chapter anchors (PDF page = printed page; extraction /tmp/ch02.txt, 911 lines)

- §2.2 "Dropping Continuity", pp. 38–45.
  - Def. 2.4 (Poisson process) p. 39 (txt :334); Thm 2.5 + eq. 2.2 p. 39 (:338–346).
  - Calc. 2.6 (compensator) + Def. 2.7 (compensated Poisson) p. 40 (:392–406).
  - Calc. 2.8 (realised QV $[M]_t=N_t$) p. 40 (:413–422); Calc. 2.9 (predictable
    $\langle M\rangle_t=\lambda t$) pp. 40–41 (:423–451).
  - Example 2.1 (why Lévy needs continuity) p. 41 (:454–461); two-brackets remark
    ([M]=⟨M⟩ iff continuous) p. 41 (:462–484); Figure 2.1 p. 42.
  - **Thm 2.10 (Lévy–Itô, eq. 2.10) p. 43** (:565–583); proof sketch — large jumps as
    compound Poisson (:586–591), shell orthogonality + L² convergence (:592–600),
    Gaussian residue (:601–604) — pp. 43–44.
  - FV/IV regimes ($\int_{|x|<1}|x|\nu$ finite vs infinite, $[X]_t$, $E[X]_t$) p. 44
    (:629–646); α-stable boundary p. 44 (:650–657); truncation/triplet remark p. 44
    (:666–676); Itô's lemma with jumps p. 45 (:684–714).
- §2.3 "Two Kinds of Jump", pp. 46–49.
  - **Def. 2.12 (predictable / totally inaccessible) p. 46** (:789–792); scheduled-vs-default
    and the intensity/atom compensator remark pp. 46–47 (:793–809).
  - Def. 2.13 (Cox) p. 47 (:818–820); **Calc. 2.14 / eq. 2.3 p. 47** (:822–833).
  - Incompleteness-as-shopping-list and the payoff-not-asset criterion p. 48.
- Scan ledger `ch02-scan.md`: lesson verdicts :92–101 (0052's assigned scope :96–98);
  stack anchors :75–90.

---

## 6. Build question: none required; smallest *enrichment* build named for the record

**Verdict full-with-scope-cut ⇒ `buildRequirement` empty.** The flip is unlocked by
research alone: every section the skeleton below names has a landed anchor, and the gated
boundary is teachable as chapter-sourced structure (the 0054/0058/0068 register).

For the record, the two builds one *could* do, and why neither gates the flip:

- **Smallest isolated build (optional enrichment)**: the α-stable shell dichotomy — for
  $\nu_\alpha(dx)=c\,x^{-1-\alpha}dx$ on $(0,1)$: $\int_{(0,1)}|x|\,\nu_\alpha<\infty
  \iff\alpha<1$ and $\int_{(0,1)}x^2\,\nu_\alpha<\infty\iff\alpha<2$. Closest substrate:
  build-face `integral_rpow` (`Analysis/SpecialFunctions/Integrals/Basic.lean:147`,
  valid for $-1<r$) for the convergent direction; the divergent direction needs a small
  comparison argument (`MeasureTheory` monotone-comparison / explicit antiderivative blow-up).
  It would harden one chapter-sourced paragraph; it unlocks no section that prose cannot
  already carry, and it does not produce a process. Not a gate.
- **The real residual core is research-gated, not a small build**: a Lévy-process layer
  (increment-law abstraction over the PRM, càdlàg jump paths, pathwise QV, compensator
  theorem) before eq. 2.10 can even be stated. The stub's original research-gate assessment
  survives in this narrowed form; pair the landing zone with ch. 16 credit material when
  reached (scan ledger :100–101), as recorded.

---

## 7. Section skeleton for the flipped lesson (each section names its lemma)

1. `# Lesson 0052 — The two kinds of jump` + Goal line.
2. `## Motivate` — prices jump (defaults, earnings, peg breaks, p. 38); the chapter's two
   dichotomies (§2.2 regimes, §2.3 times); what changed since the stub was written.
3. `## Establish — the two brackets of a jump martingale (Calc. 2.8/2.9)` —
   `map_count_eq_poissonMeasure` + `poissonMeasure_integral_id`/`poissonMeasure_integral_sq`
   ($E[N_t]=\mathrm{Var}(N_t)=\lambda t$); `compensated_integral_zero`/`compensated_integral_sq`;
   cross-ref 0051 for the continuous-world agreement (`condExp_sq_sub_bracket`);
   realised-staircase stated chapter-sourced, moment-level only.
4. `## Establish — the chapter's two kinds: scheduled events vs surprises (Def. 2.12)` —
   intensity side proved (`map_firstArrival_eq_expMeasure`; Cox cross-refs → 0051/0068);
   size side → 0058's scheduled-event variance lumps; announcing-sequence formalism gated
   (build-face vocabulary `IsStoppingTime`/`IsPredictable` named honestly).
5. `## Establish — the Lévy–Itô split, proved half (Thm 2.10)` — large-jump shells are
   compound Poisson (`ae_count_ne_top`, `poissonMeasure_conv_poissonMeasure`,
   `thinned_streams`, `compoundPoisson_mgf_identity`, `mertonCallPrice`); the small-jump
   machinery (`compensated_simple_isometry`, `compensated_covariance` orthogonality,
   `itoLevyIntegralL2_norm` on `levyClosure`) — general in σ-finite ν, exactly the
   substrate eq. 2.10's compensated term waits on; the FV/IV dichotomy stated as the gated
   theorem that machinery is waiting for.
6. `## The gated boundary — stated plainly` — §4 items 1–8, with the Dense module's
   deferred-Summit disclosure quoted.
7. `## Connect` — 0051 (continuous corner of the classification), 0058 (scheduled events),
   0068 (credit options), the payoff-not-asset criterion (p. 48) forward-referencing the
   barrier/short-dated desk practice.
8. `ask-your-tutor` admonish tip (recommended; matches 0051 and the flipped siblings).
9. `## Primary source` — ch. 2, pp. 38–49.
10. `## Exercises` + `## Answers` — keep the stub's ε-threshold exercise, now anchored on
    `ae_count_ne_top`; add one bracket exercise from the moment lemmas and one orthogonality
    exercise from `compensated_covariance`.

**Style models**: 0038/0046 per AGENTS.md; register of freshly flipped 0054/0058/0068
(proved core + explicit gated-boundary section).

---

## 8. Stale references in the current stub text (fix list for the authoring pass)

1. `0052:3–5` banner "Poisson-style (finite activity) throughout" — stale (§2.1 here):
   PRM is σ-finite-mark; quote `PoissonRandomMeasure.lean:135–136`.
2. `0052:42–44` "Every compensated object in the stack sits on a finite Poisson intensity,
   so the moment infinite mass appears, none applies" — false at the integral layer;
   finiteness is per-region (`hfin` hypotheses), and the L² closure CLM is the
   infinite-mass home. Replace with the precise residual gate (no Lévy process, no pathwise
   objects, no pointwise compensated count at infinite mass).
3. `0052:48–50` unblock step (1) — already landed; delete or mark done. Step (2) is
   half-landed (abstract CLM yes, concrete shell instantiation no). Step (3) survives.
4. `0052:9` item statement — scope too narrow vs the scan verdict (`ch02-scan.md:96–98`);
   restore the four-part scope with 0051 cross-refs for the already-taught Cox/survival and
   twin-theorem material (`0051:121–160`, and 0051 explicitly defers "the infinite-activity
   half" to 0052).
5. `0052:21–34` "What the stack has" — all five citations re-verified today and still
   accurate; incomplete (missing the whole `PoissonCompensated*` isometry architecture,
   `Cox.lean`, thinning/superposition detail, `ae_count_ne_top`).
6. `0052:44` "absent from Mathlib as well" — still true, keep with the fresh grep citation.
7. `0052:55–57` attempt-exercise — keep; it is now anchorable on `ae_count_ne_top`
   (`PoissonCompensatedBilinear.lean:50`).

**Bookkeeping on flip**: `model-coverage-map.md:39` (ch2 row: "0052 STUB" → FULL),
`:124` (blocked-items row "Infinite-activity Lévy jumps (ch2)": gating language updates to
"integral layer landed; Lévy-process layer research-gated"), `NOTES.md:667` stub count
9 → 8, SUMMARY.md unchanged (already registered at :128). mdbook gate per convention 5.

# Stub-unblock memo — lesson 0058 (density moves, coordinates, scheduled events)

E-pass (flash-explorer, read-only), 2026-10-14. Scope: decide whether
`mdbook/src/lessons/0058-density-moves-coordinates-scheduled-events.md` (STUB) can flip,
against the landed ForwardEqScratch (stages 1–3) + GyongyScratch (Layer 1/2) +
BreedenLitzenberger substrate and Bagaria ch. 9 §§9.4/9.6/9.8. Every name below was
re-verified this pass by grep into the files cited; PDF quotes come from a fresh
`pdftotext` of `resources/fixed-income-notes-chapters/ch09-implied-and-local-volatility.pdf`
run this pass. Build-face rule followed: MathFin/Mathlib names cited at
`AmericanPutConvexity/.lake/packages/` first (that is what `builds/lean/*.lean` compile
against), mathfin working-HEAD (b46e9b4) numbers as secondary.

## 1. Verdict: **full-with-scope-cut**

The stub's named blocker — "the forward (Fokker–Planck) side of the stack does not
exist … and Dupire's numerator needs parameter differentiation under the expectation"
(stub :3–6) — is now **half-obsolete in each clause**:

- The forward side EXISTS and is proved: `ForwardEqScratch.lean` stages 1–3 (constant
  drift :229, time-dependent :754, migration :661/:1210, **flux form :1269/:1310**),
  and — the genuinely (t, x)-dependent half — the weak forward equation with Gyöngy
  conditional-expectation coefficients, `Gyongy.marginal_flow_weak_equation_constructed`
  (`GyongyScratch.lean:1078`). Landing records: QUEUE.md items 10/11 both **DONE
  (2026-10-13)**, commits `8651df7` (item 10) and `eb9237a` (item 11); both files grep
  **zero `sorry`** (ran this pass); both carry in-file `#print axioms` audit blocks
  (ForwardEqScratch.lean:1372–1396, GyongyScratch.lean:1129–1146); orchestrator V-passes
  recorded in QUEUE.md:51–52.
- The parameter-differentiation-under-the-integral assembly EXISTS: ForwardEqScratch's
  private migration engine (`hasDerivAt_convDen_t/_x/_xx` :445/:530/:644,
  `hasDerivAt_convDenGen_t/_x/_xx(_core)` :970/:1082/:1136/:1189) is exactly
  "differentiate under the integral with dominated convergence", executed; plus the
  public kernel-family lemma `hasDerivAt_integral_mul_kernelFamily`
  (build-face `FeynmanKacHeatEquation.lean:595`).

What did NOT land, and forces the scope cut: the **full pointwise Dupire statement
(eq. 9.4)** and its coordinate corollary (eq. 9.5) — item 10's Route C was REJECTED as
hypothesis-echo, "gated on a non-Gaussian density carrier (`memos/item10-memo.md`)"
(QUEUE.md:51); the only proved densities are Gaussian. The §9.8 event arithmetic has no
substrate at all. The flip is therefore a **0021-shaped FULL lesson** (proved half =
§9.4's forward layer + §9.7's weak layer; build half = §9.6 coordinates + §9.8 events,
taught as chapter math with named gates, never as proved corollaries) — the exact
precedent of `lessons/0021-local-volatility-dupire.md`, which is FULL while teaching the
unformalized Dupire formula as its build half.

## 2. Proved content the flipped lesson can teach (landed names ↔ chapter equations)

All ForwardEqScratch names are in `builds/lean/ForwardEqScratch.lean` (namespace
`ForwardEqScratch`); GyongyScratch names in `builds/lean/GyongyScratch.lean` (namespace
`Gyongy`). Line numbers from this pass's reads.

| Chapter object (ch9) | Landed substrate | file:line |
|---|---|---|
| eq. (9.2)'s **divergence/flux form** — coefficients *inside* the spatial derivatives | `forward_eq_timeDependent_flux` — `∂_t p = −∂_x(μ(t)·p) + ½ ∂²_x(σ(t)²·p)` for the density `p = K(v t, x − m t)` of `dX = μ(t)dt + σ(t)dW` | ForwardEqScratch.lean:1269 |
| eq. (9.2)/(9.3) **migrated through a test function** (the assembly the stub names as its blocker, "flux-form migration lemma") | `forward_eq_convolution_timeDependent_flux` — same divergence form for `u = ∫_{[a,b]} g(y)·p(t, x−y) dy` | ForwardEqScratch.lean:1310 |
| eq. (9.2)'s non-flux predecessors (the chain-rule story) | `forward_eq_constant_drift` (:229), `forward_eq_driftless` (:247), `forward_eq_timeDependent` (:754), `forward_eq_convolution` (:661), `forward_eq_convolution_timeDependent` (:1210) | ForwardEqScratch.lean |
| §9.4's opening move — "chapter 3's adjoint applied to this chapter's process", in **weak/test-function form** (the adjoint pairing with no operator object) | `marginal_flow_weak_equation_constructed` — `d/dt 𝔼[f(X_{t⁺})] = 𝔼[f'·a] + ½𝔼[f''·b²]` with `a = 𝔜[β_{⟨t⟩} | σ(X_{⟨t⟩})]`, `b² = 𝔜[δ²_{⟨t⟩} | σ(X_{⟨t⟩})]`, proved (hitoid discharged) for the constructed Itô process on the band `(0, ↑T)` | GyongyScratch.lean:1078 |
| Thm 9.6's coefficients in genuine **(t, x) form** (Doob–Dynkin Borel functions) | `exists_driftCoeff_fn` (:1210), `exists_diffCoeffSq_fn` (:1242), composed into `marginal_flow_weak_equation_fn_constructed` (:1281) | GyongyScratch.lean |
| Thm 9.6's conclusion (one-time-marginal mimicry), modulo the named gate | `gyongy_mimicry_gated` | GyongyScratch.lean:1516 |
| Thm 9.3 (Breeden–Litzenberger — the density the lesson moves) | `breedenLitzenberger` (face :73), `lognormalTerminalPDF` (face def :66), `lognormalTerminalPDF_change_of_variables` (face :197; mathfin HEAD :144), `lognormalTerminalPDF_nonneg` | build-face `MathFin/BlackScholes/BreedenLitzenberger.lean` |
| Lemma 9.2 (the coordinates exist) | `implied_volatility_unique` (face :69), `bsV_vega_pos` (face :40) | build-face `MathFin/BlackScholes/ImpliedVolatility.lean` |
| §9.2 arbitrage constraint (price-coordinate denominator sign) | `bsV_strike_convexOn` (face :133) | build-face `MathFin/BlackScholes/StrikeConvexity.lean` |
| Driftless forward seed | `feynmanU_heat_equation` (face :1304), `hasDerivAt_feynmanU_t/_x/_xx` (face :1006/:1057/:1113) | build-face `MathFin/Foundations/FeynmanKacHeatEquation.lean` |
| Generator layer (lesson 0053) | `itoDrift` (face `ItoLemma.lean:80`), `itoDrift2D` (face `ItoLemma2D.lean:120`) | build-face `MathFin/Foundations/` |
| Calc 9.8's pricing primitives (only) | `bs_cash_or_nothing_formula` (face `Digital.lean:67`), `bs_call_eq_asset_minus_K_cash` (face :210), `bachelier_call_formula` (face `Bachelier.lean:184`) | build-face `MathFin/BlackScholes/` |

Compile status: **not re-run this pass** (read-only E-pass). Cited from QUEUE.md:51–52
(items 10/11 DONE with orchestrator V-pass incl. term-by-term fidelity diff), landing
commits `8651df7`/`eb9237a`, zero-`sorry` grep (ran), and the in-file `#print axioms`
audit blocks. The B-pass re-verifies on the compilation face per standing convention.

## 3. What stays gated (the honest boundary, quoted)

1. **The chapter's exact coefficients (eq. 9.2's `(r−q)S` and `σ_loc(T,S)·S`) have no
   density carrier.** ForwardEqScratch.lean:1257–1261 (stage-3 docstring): "Genuinely
   `(t, x)`-dependent coefficients have no density carrier in the substrate (item-10
   E-pass memo, Route C: the only proved densities are Gaussian, and hypothesis-carried
   versions were rejected as vacuous), so this stage lands the *statement form* of eq. 9.2
   …". item10-memo:357–365 (Conflict 3): "The full pointwise Dupire statement has no
   carrier in the substrate: the only density objects in the program are Gaussian
   (`pden` :162, `pdenGen` :705 = shifted heat kernels); a (t, x)-dependent diffusion's
   density is not Gaussian …". So the flux theorems are t-only-coefficient; the lesson
   must teach eq. 9.2 as the *statement class* these theorems instantiate, not claim the
   multiplicative-drift instance.
2. **Dupire (9.4) and the implied-coordinate ratio (9.5) are unformalized** — zero clone
   hits (ch09-scan.md:123–126; item10-memo §1b grep). The stub's own sentence "With
   (9.4) unformalized, (9.5) has no object to re-express" (:43) **remains true** and
   stays in the flipped lesson as the build half. The rule of two (eq. 9.6) and Example
   9.2's `σ_loc = σ` check are likewise unformalized.
3. **Gyöngy's Y-side.** `GyongyScratch.lean:203–205`: "Gated: the mimicking diffusion's
   *existence* (`dY = a(t,Y) dt + b(t,Y) dW` for merely measurable `a`, `b²`; MathFin's
   `SDEExistence.lean` Picard route needs Lipschitz coefficients, per
   `picardMap_contraction`) and the identification of `Y`'s marginals."
   `gyongy_mimicry_gated` carries the residual as the explicit `hgate` — docstring
   GyongyScratch.lean:1498–1500: "(iv) `hgate` — flow uniqueness: two probability-measure
   flows solving the weak forward equation of
   `Gyongy.marginal_flow_weak_equation_fn_constructed` (integrated form, test functions
   in the class) from the same initial law coincide". item11-memo:16–23 verdict: strong
   solution "NO — and mathematically false as a general target"; Skorokhod/martingale-problem
   core "absent from *every* clone … a research-scale project, not a queue item".
4. **Mass conservation is not a proved lemma.** Eq. (9.3)'s "total conserved by
   construction rather than by hope" and the 1.42 anecdote (PDF p. 7) are desk-level
   readings of the flux *statement form*; no `∫p = 1` or conservation theorem exists in
   ForwardEqScratch. Teach as reading, marked as such.
5. **§9.8 scheduled events: no substrate at all.** No event-lump object, no
   total-variance decomposition (eq. 9.9), no mixture-vs-matched-Gaussian construction,
   no variance-interpolation theorem anywhere (ch09-scan.md:123–126 records the zero
   hits; nothing landed since touches it). Only the pricing primitives of the table in
   §2 exist (`bs_cash_or_nothing_formula`, `bachelier_call_formula`). Calc 9.8's
   0.194-vs-0.230 digital gap is taught as the chapter's arithmetic, with those lemmas
   named as what a future build would combine.

## 4. Chapter anchors (split-PDF page = book printed page − 154)

`pdftotext` run this pass on `ch09-implied-and-local-volatility.pdf` (18 pages). The
in-page printed markers ("161" on PDF p. 7, "165" on PDF p. 11) pin the mapping: **PDF
p. N = book p. N+154**. Note: AGENTS.md's "PDF page = printed page, offset +0" holds for
the full 441-pp. notes file, **not** for this split file — worth correcting in AGENTS.md
at the next edit (flagged here; not edited — read-only pass).

- §9.4 "How the Density Moves", eq. (9.2), eq. (9.3) flux + conservation remark + the
  "density integrating to 1.42" anecdote: **PDF p. 7** (book p. 161).
- Def 9.4, Thm 9.5 (Dupire), eq. (9.4), proof (differentiate C in T, substitute (9.2),
  IBP twice): **PDF p. 8** (book p. 162).
- Example 9.2 (flat smile, `σ_loc = σ`): **PDF p. 9** (book p. 163).
- §9.6 + eq. (9.5) (implied-coordinate ratio): **PDF pp. 10–11** (book pp. 164–165);
  rule of two eq. (9.6) + "read backwards" remark: **PDF p. 11** (book p. 165).
- Thm 9.6 (Gyöngy): **PDF p. 12** (book p. 166). Thm 9.7, eq. (9.7)/(9.8): **PDF p. 14**
  (book p. 168) — lesson 0038's coverage.
- §9.8, eq. (9.9), Calc 9.8 setup: **PDF p. 15** (book p. 169); the 0.194-vs-0.230
  digital gap: **PDF p. 16** (book p. 170).

## 5. Section-by-section skeleton for the flipped lesson (FULL format)

H1 (title/filename unchanged — permanent identifier) → `**Goal:**` line → Motivate →
Establish §1–5 → Connect → Primary source → `## Exercises` → `## Answers`
(ask-your-tutor admonish optional in Part X per AGENTS.md).

1. **Motivate** — lesson 0057 read the static density off the surface (straddle/RR/fly
   as moment extractors); this lesson: what moves it. Chapter line: "Dupire's formula
   needs to know how the risk neutral density changes with maturity" (PDF p. 7).
2. **Establish §1 — The forward equation and its flux form (eq. 9.2/9.3).** Teaches
   `forward_eq_constant_drift` → `forward_eq_timeDependent` →
   `forward_eq_timeDependent_flux` (coefficients inside — eq. 9.2's shape) →
   `forward_eq_convolution_timeDependent_flux` (the migration lemma: the forward
   equation survives convolution against a test density — the DCT assembly the stub
   called missing). Honest note: t-only deterministic coefficients; eq. 9.2's exact
   `(r−q)S` / `σ_loc(T,S)S` instance gated (quote ForwardEqScratch.lean:1257–1261);
   conservation = reading of the divergence form, not a proved lemma.
3. **Establish §2 — The adjoint pairing without an operator (the weak form).** Teaches
   `marginal_flow_weak_equation_constructed` (GyongyScratch.lean:1078): the proved
   content of "chapter 3's adjoint applied to this chapter's process" —
   `d/dt 𝔼[f(X)] = 𝔼[f'·a] + ½𝔼[f''·b²]` — plus the Doob–Dynkin upgrade
   `exists_driftCoeff_fn`/`exists_diffCoeffSq_fn`/`marginal_flow_weak_equation_fn_constructed`
   (the program's first genuine `(t, x)` coefficients). This is the test-function dual
   of §1's density-side equation: the same statement with derivatives moved onto `f`.
4. **Establish §3 — What the marginals know: Gyöngy, in one paragraph.** Teaches
   `gyongy_mimicry_gated` (GyongyScratch.lean:1516) modulo the quoted `hgate`
   flow-uniqueness gate; links to lesson 0038 (Thm 9.7 deep dive) — do not re-teach
   0038, only the Y-side boundary as it bears on "in which coordinates".
5. **Establish §4 — Dupire in the coordinates we actually have (§9.6) — the build
   half.** Presents eq. (9.5)'s ratio and the rule of two (eq. 9.6) as the chapter's
   chain-rule corollary of (9.4), explicitly marked build-target (0021 precedent).
   Proved anchors named: the coordinates themselves (`implied_volatility_unique`,
   `bsV_vega_pos` — Lemma 9.2) and the price-coordinate denominator sign
   (`bsV_strike_convexOn`); the vol-coordinate denominator positivity has no substrate.
6. **Establish §5 — Scheduled events (§9.8) as total-variance arithmetic.** Eq. (9.9)
   and Calc 9.8 taught as the chapter's pencil arithmetic (lumps read off straddling
   expiries; 0.194 vs 0.230 as the shape-vs-moment payoff, PDF p. 16). Proved anchors:
   `bs_cash_or_nothing_formula`, `bachelier_call_formula`, `bachelierD` (face
   `Bachelier.lean:127`) named as the primitives a future build would combine; state
   plainly that the event layer has no formalization.
7. **Connect** — lesson 0054 (the semigroup operator object is still the open half:
   0054:85 "the semigroup-object formalization"; its own text already records stages
   1–3, 0054:65–84), lesson 0021 (Dupire's build half — 0058 now shares its forward
   prerequisite), lesson 0060 (the forward smile — where the rule of two does damage).
8. **Primary source** — Bagaria ch. 9 §§9.4/9.6/9.8 (+ 9.5/9.7 as connective);
   `builds/lean/ForwardEqScratch.lean`, `builds/lean/GyongyScratch.lean`,
   `MathFin/BlackScholes/{BreedenLitzenberger,ImpliedVolatility,StrikeConvexity,Digital,Bachelier}.lean`.
9. **Exercises/Answers** — the stub's attempt exercise survives with upgraded names
   (see §6.5); add (i) a flux-form reading exercise (identify `J` in
   `forward_eq_timeDependent_flux`'s conclusion); (ii) a weak-form exercise (what test
   function converts `marginal_flow_weak_equation_fn_constructed` into §1's equation);
   (iii) the Calc 9.8 pencil computation (mixture of three Bachelier calls vs
   variance-matched Gaussian — no Lean claimed).

## 6. Stale references in the current stub text (fix at flip)

1. **Status line (:3–6) — premise false.** "the forward (Fokker–Planck) side of the
   stack does not exist (lesson 0026's honest column; lesson 0054's forward half)".
   Contradicted by QUEUE.md:51–52 (items 10/11 DONE 2026-10-13), commits
   `8651df7`/`eb9237a`, and by lesson 0054's own current text (0054:65–84 records
   stages 1–3 incl. the flux form). Lesson 0026's honest column (0026:87–94) is also
   partially stale for the same reason (its forward-Kolmogorov gap item is now served
   for deterministic coefficients).
2. **"lesson 0021's missing assembly" (:5, :41–43) — doubly stale.** (a) The
   dominated-convergence assembly now exists (ForwardEqScratch private engine,
   §2 above; `hasDerivAt_integral_mul_kernelFamily`, build-face
   FeynmanKacHeatEquation.lean:595). (b) Lesson 0021:68's shopping-list name
   `integral_deriv_mul_derivWithin` does not exist at this Mathlib rev (item10-memo
   :349–356, Conflict 2; real names:
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, ParametricIntegral.lean:286 —
   used ~10× in ForwardEqScratch — and the endpoint-only trap
   `IntervalIntegrable.ae_hasDerivAt_integral`). The flipped lesson must not repeat
   either stale name; likewise 0021's exercise-5 answer (:165–167, "neither yet
   assembled") is now stale — a 0058→0021 cross-link should say the forward half
   landed.
3. **"No adjoint $\mathcal{L}^*$, no flux object, no forward equation for any drift-ful
   process" (:39–40) — each clause false in absolute form.** Flux object:
   `forward_eq_timeDependent_flux` (:1269). Drift-ful forward equation:
   `forward_eq_constant_drift` (:229). Adjoint content (weak form):
   `marginal_flow_weak_equation_constructed` (:1078). What legitimately survives:
   the semigroup *operator object* (lesson 0054's remaining blocker) and the chapter's
   exact `(t,S)`-dependent coefficients (§3.1 above).
4. **Registry text stale** (orchestrator-side, for the flip edit):
   `mdbook/src/reference/model-coverage-map.md:127` still lists 0058's blocker as
   "forward equation + parameter-differentiation assembly / lesson 0054's sequencing"
   — update when flipping (not done here; read-only pass).
5. **Verified NOT stale (keep):** every name in the stub's "What the stack has" —
   `breedenLitzenberger`, `lognormalTerminalPDF`,
   `lognormalTerminalPDF_change_of_variables` (face BreedenLitzenberger.lean
   :73/:66/:197), `bsV_strike_convexOn` (face :133), `feynmanU_heat_equation` +
   `hasDerivAt_feynmanU_t/_x/_xx` (face :1304/:1006/:1057/:1113), `itoDrift`/`itoDrift2D`
   (face ItoLemma.lean:80 / ItoLemma2D.lean:120), `implied_volatility_unique`/
   `bsV_vega_pos` (face :69/:40); and the attempt-exercise premise "`hasDerivAt_bsd2_tau`
   (`PDE.lean`), which exists" — verified on both faces (face `PDE.lean:188`, mathfin
   HEAD :189). Only note: with stage 3 landed the exercise can pin its factors with
   `hasDerivAt_pdenGen_t/_x/_x_x` (:735/:720/:726) + `forward_eq_timeDependent_flux`
   rather than the price-side `hasDerivAt_bsd2_tau` alone.

## 7. Checks run this pass (and not run)

- Ran: `pdftotext` of ch09 (full + per-page `-f/-l` splits) — all PDF quotes and page
  anchors; `grep` name verifications against the build face
  (`AmericanPutConvexity/.lake/packages/MathFin/…`) and mathfin HEAD for every name in
  §2/§6.5; `grep -c sorry` on ForwardEqScratch.lean / GyongyScratch.lean → 0/0;
  `git log --oneline` (read-only) to date the landings (`8651df7`, `eb9237a`).
- Not run: `lake env lean` on either scratch file (compile status cited from QUEUE.md
  items 10/11 + in-file axiom audits); `mdbook build` / `check_links.py` (that is the
  flip edit's verification bar, run by the authoring pass).

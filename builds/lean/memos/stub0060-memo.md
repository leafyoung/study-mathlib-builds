# Stub E-pass memo — lesson 0060 (the forward smile)

Date: 2026-10-14. E-pass on flash (Explorer·0060), read-only; no git, no lesson edits.
Question: can `mdbook/src/lessons/0060-the-forward-smile.md` (STUB) flip FULL now, with what
scope cut — and if not, what is the smallest honest Lean build that unlocks it (or is it
research-gated)?

## Verdict: **needs-build**

The stub cannot flip honestly today: its central identities (eqs 10.8–10.9) have **no landed
Lean core** — the only §10.5-matched substrate is the Heston generator's time-homogeneity
anchor (§10.5.3 support), nothing at all for §10.5.2. Under the flip register the three
siblings set (0054/0058/0068: proved anchors + gated chapter math taught *on* those anchors),
a FULL 0060 would be 100% gated chapter math — below the bar. But the unlock is a **small,
concrete, non-research build**: one `builds/lean/` file that lands eq 10.8's first-order
Dupire-ratio slope from the bsV greek layer already on the APC build face. Not
research-gated: no measure theory, no SDE theory, no forward measures, no new Mathlib —
every HasDerivAt atom the build needs was grep-verified on the build face this session.

Why the stub's own BLOCKED reason overstates the bar (it was written 2026-10-03, before the
current register): it demands "the forward-measure/numeraire machinery" to verify eqs
10.8–10.9. The chapter never invokes one for these identities — §10.5.2 runs Dupire's ratio
on the calibrated surface and then "read(s) (10.8) as a statement about calendar time"
(p. 182); the rule-of-two-in-reverse gives eq 10.9 algebraically. The forward-measure layer
is needed only to *price* forward-start payoffs honestly (the table's forward column), not
for the identities themselves.

## Proved content (landed, exact names, matched to chapter equations)

Everything below was grep-verified this session at the cited path:line.

Matched to eq 10.10 / §10.5.3 (Heston, "no function of t"):
- `hestonGenerator` — `builds/lean/heston_scratch.lean:241`. The 2D Heston generator
  `Lf = (r−v/2)∂_x f + κ(θ−v)∂_v f + (v/2)∂_xx f + ρξv∂_xv f + (ξ²v/2)∂_vv f` with signature
  `(r κ θ ξ ρ : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ` — **no time argument**. This is the
  machine-checked anchor for §10.5.3's structural claim ("what (10.10) does *not* contain:
  any function of t", p. 183): time homogeneity read off the generator's type.
- `hestonGenerator_expAffine2` — `builds/lean/heston_scratch.lean:258` — generator on
  exp-affine test functions = affine-in-`v`, x-free bracket (the affine machinery behind eq
  10.10's characteristic function; the complex route itself is out of scope per the file
  header, ~line 30).
- `hestonTransform_pde` — `builds/lean/heston_scratch.lean:702` — the transform solves the
  pricing PDE in (T, x, v); `hestonProfile_pde` :670 likewise. Calendar date appears nowhere.
- `covariation_itoIntegralCLM_T` — `mathfin/MathFin/Foundations/ItoIntegralCovariation.lean:72`
  and `variance_itoIntegralCLM_T` — :84 — the $dW\,dZ = \rho\,dt$ machinery eq 10.10's
  correlated drivers rest on (as the ch10 scan ledger records).
- `itoDrift2D` — `mathfin/MathFin/Foundations/ItoLemma2D.lean` (defined ~:115, cited :26/:32).

Context (shared with siblings, cited by the stub, re-verified):
- `bsV_vega_pos` — `mathfin/MathFin/BlackScholes/ImpliedVolatility.lean:40`.
- Gyöngy marginals-only point for the Connect: `exists_driftCoeff_fn`
  `builds/lean/GyongyScratch.lean:1210`; `gyongy_mimicry_gated` — :1516.

**No landed lemma matches eqs 10.6 (CEV), 10.7, 10.8, 10.9.** Fresh word-greps for
`CEV`, `SABR`, `Dupire` across `mathfin/MathFin/` and the build-face
`AmericanPutConvexity/.lake/packages/MathFin/MathFin/` are all empty (run this session;
"eston" substring hits are "h**eston**"-only after filtering "honest/question").

### Build-face substrate for the unlock build (APC MathFin pin 784a831, verified this session)

The build face carries MathFin + BrownianMotion as lake packages
(`AmericanPutConvexity/lakefile.toml:11-12`; builds/lean files already import MathFin
modules — `builds/lean/greeks_signs.lean:1` imports `MathFin.BlackScholes.PutGreeks`):

- `bsV (K r σ) (S τ)` — `.lake/packages/MathFin/MathFin/BlackScholes/PDE.lean:302` (call price)
- `hasDerivAt_bsV_tau` — PDE.lean:351 (**theta**: derivative in maturity τ)
- `hasDerivAt_bsV_sigma` — PDE.lean:419 (**vega** as HasDerivAt)
- `hasDerivAt_bsV_SS` — PDE.lean:338 (**gamma**); `hasDerivAt_bsV_t` — :397 (calendar-time form)
- `hasDerivAt_bsd1_tau`/`hasDerivAt_bsd2_tau` — PDE.lean:150/:188
- `hasDerivAt_bsd1_sigma`/`hasDerivAt_bsd2_sigma` — PDE.lean:208/:242
- `MathFin/BlackScholes/StrikeGreeks.lean`: `hasDerivAt_bsd1_K` :43, `hasDerivAt_bsd2_K` :85,
  `hasDerivAt_bsV_K` :98, `hasDerivAt_bsV_KK` :174 (strike-side first/second derivatives)
- No `Dupire` anywhere on the build face (grep empty) — consistent with 0058's residual gate.

Style precedents for the bookkeeping: `builds/lean/greeks_signs.lean` (300 lines, 14
theorems — bsV HasDerivAt chains from primitives; NOTES.md records the pin lacks
`DerivOfDeriv`, so deriv-form chains are rebuilt from Mathlib primitives — the builder must
expect that), `builds/lean/heston_scratch.lean` (794 lines), `ForwardEqScratch.lean`.

## The build (smallest honest unlock) — `builds/lean/ForwardSmileScratch.lean`

Compile face: `cd AmericanPutConvexity && lake env lean ../builds/lean/ForwardSmileScratch.lean`
(zero sorry, `#print axioms` standard-three; WIP-checkpoint per AGENTS).

1. `smileSurface` (def) — σ_BS(k,T) = σ + ε·ψ₁·k/√(T+T₀)  (eq 10.7, ε-tilted for the
   first-order extraction); positivity for σ>0, T+T₀>0.
2. `bsCallSmile` (def) — C(ε,k,T) := bsV (F·e^k) 0 (σ_BS ε k T) F T — the chapter's zero-rates
   setting (S = F fixed; k = ln(K/F); p. 182).
3. **`dupireRatio_k_slope` (the deliverable = eq 10.8).** Dupire's zero-rates ratio
   R(ε,k,T) := 2·∂_T C / (K²∂²_K C) enters **as a definition** (the chapter: "run Dupire's
   formula of chapter 9 on it", p. 182; Dupire's formula itself stays gated — see boundary).
   Convenient k-form: since ∂_K = (1/K)∂_k, K²∂²_K C = C_kk − C_k. Then
   `deriv (fun ε => deriv (fun k => R ε k T) 0) 0 = 2σψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}`
   for σ>0, T>0, T₀>0; and the σ_loc-slope reading
   `deriv (fun ε => deriv (fun k => √(R ε k T)) 0) 0 = ψ₁·((3/2)T+2T₀)/(T+T₀)^{3/2}`.
   Hand-verified this session (E-pass, by calculation, not Lean): expanding
   w(k,T) = σ_BS²·T to first order with the Gatheral implied-variance form of the ratio
   (denominator `1 − (k/w)w_k + …`; the −(k/w)w_k term is first-order and required) gives
   σ_loc² = σ² + εσψ₁k·(3T+4T₀)/(T+T₀)^{3/2} + O(ε²) — identical to the printed eq 10.8
   since (3T+4T₀)/2 = (3/2)T+2T₀. The target formula is correct as printed.
4. Corollaries (trivial algebra off 3, each a named lemma):
   `ruleOfTwo` — at T=0 the factor vs the implied skew is exactly 2 (√T₀·((3/2)·0+2T₀)/T₀^{3/2}
   = 2; numerically confirmed 2.0 this session);
   `localSkew_tendsto` — ∂_k σ_loc|₀ ∼ (3/2)ψ₁/√T as T→∞ (Tendsto atTop);
   `forwardSkew_eq_half` — eq 10.9: ψ_fwd(t) = ½ψ₁·((3/2)t+2T₀)/(t+T₀)^{3/2} (the chapter's
   rule-of-two-in-reverse at date t; the ½-step stated as chapter math, anchored on 3);
   `forwardSkew_tendsto` — → (3/4)ψ₁/√t; numeric readings at σ=20%, ψ₁=−0.10, T₀=1/12
   (`norm_num`): ratio to today's skew 0.213/0.108/0.068 at t = 1/4/10 — the chapter's "a
   fifth … an eighth … under a tenth" (p. 182 Remark), confirmed by `python3` this session
   (both the exact eq-10.9-at-date-t ratio and the (3/4)√(T₀/t) asymptotic).

Scale estimate: ~400–800 lines. The ε/k chain rule through bsd1/bsd2 into bsV is the bulk;
no integration, no ODEs, no probability. Closest existing substrate: the bsV greek layer
listed above.

**Builder caveat (typography trap):** pdftotext garbles eq 10.8 — the stacked 3/2 fraction
reads as a leading constant, yielding the impossible numerator "T + 2T₀" (whose T=0 value
3ψ₁/√T₀ would contradict the text's own rule-of-two limit 2ψ₁/√T₀). The page-182 image
(rendered this session, `/tmp/ch10_p10-10.png`) shows the true numerator: **(3/2)T + 2T₀**,
fully consistent with both stated limits. Build against the image-verified form.

## Gated boundary (stays gated even after the build)

1. **Dupire's formula as a theorem** (σ_loc² = 2∂_T C/(K²∂²_K C) *from the local-vol model*).
   The build uses it as a definition; the derivation remains lesson-0021/0058's residual gate
   (no non-Gaussian density carrier — registry row `model-coverage-map.md:51`, flip row :127).
2. **The §10.5.3 table** (5y-skew shares 22%/~100%/fitted/20%; forward column ~100%/~100%/11%/97%)
   — simulation output (footnote 5 "heston::Heston", p. 183: spot and forward smiles from the
   same routine). Quoted as source data, like 0059 quotes its tables. `builds/lean/mc_pricer.lean`
   (54 declarations: SLLN consistency + CLT for BS-terminal European payoffs) is the closest
   harness; a local-vol slice-extraction layer is a separate, larger build — not this unlock.
3. **CEV as a process** (eq 10.6) — no CEV substrate anywhere (fresh greps, this session); the
   lesson reads eq 10.6 structurally (coefficient depends on the level, not the date).
4. **Honest forward-start pricing** (change of numeraire for the ratio payoff S_{t+τ}/S_t) —
   needed for the table's forward column, not for eqs 10.8–10.9. The build face has
   `StockNumeraire.lean` (`stockNumeraireMeasure` :151) and `RiskNeutralProbabilities.lean`,
   but no forward-starting-payoff assembly.
5. **Hot-start forward-skew non-flatness** (v₀=9% vs θ=4%, 1/κ = six months, p. 183–184) —
   simulation; and the stationary-distribution premise ("once v_t has reached its stationary
   distribution") — CIR/square-root existence is still open (Tier-2 item 18 residual).
6. **Heston SDE existence** — heston_scratch is generator/transform level, not a process.

## Chapter anchors (printed pages; verified from the split PDF this session)

**Page-mapping correction:** for `ch10-smile-dynamics-stochastic-volatility.pdf` the PDF page
= printed page **− 172** (23-page file for printed pp. 173–195; `pdftoppm -f 10` renders the
page headed "182"). This contradicts the "PDF page = printed page, offset +0" note in
AGENTS.md's split-file description — flag for whoever relies on it for this chapter.

- **§10.5 intro — p. 181 (PDF 9):** forward smile = "the smile of an option on the ratio
  S_{t+τ}/S_t, struck at the money at a future date t"; cliquets/ratchets; two term
  structures (maturity: quoted, ∼1/√T; forward: fixed tenor τ, moving start t, stationary).
- **§10.5.1 — pp. 181–182:** eq 10.6 (CEV, β<1); both term structures flat at σ₀=25%, β=0.7;
  "its forward smile is its spot smile"; "gets the forward term structure right and the
  maturity term structure wrong. It cannot be calibrated to a real surface at all."
- **§10.5.2 — p. 182 (PDF 10):** eq 10.7 (σ_BS = σ + ψ₁k/√(T+T₀), k = ln(K/F)); Dupire ratio;
  **eq 10.8** = ψ₁·((3/2)T+2T₀)/(T+T₀)^{3/2} (image-verified; pdftotext garbles it); limits
  2ψ₁/√T₀ at T=0 ("the rule of two, recovered") and (3/2)ψ₁/√T at large T; "by ten years it
  is a third of today's"; **eq 10.9** = ½ψ₁((3/2)t+2T₀)/(t+T₀)^{3/2} → 3ψ₁/(4√t); Remark:
  a fifth at 1y, an eighth at 4y, under a tenth at 10y (σ=20%, ψ₁=−0.10, T₀=1 month); the
  one-dial moral ("matching the observable one determines the unobservable one — and
  determines it wrongly").
- **§10.5.3 — p. 183 (PDF 11):** eq 10.10 (Heston, taken "only for the measurement"); the
  4×2 table (image-verified); market row reading √(0.25/5) = 22%; Structure paragraph
  ("The second Brownian motion … is somewhere to keep a term structure that would otherwise
  have to be written into the calendar"); hot-start caveat v₀=9% vs θ=4% (1/κ = 6 months);
  footnote 5 (heston::Heston, one routine for both smile columns).

## Section skeleton (each section names what it teaches and on which lemma)

1. **H1 + Goal line** — theorem-reading lesson with one machine-checked identity; announce
   (à la 0059's Goal) which parts are proved, stated, or simulated.
2. **Motivate** — cliquets/ratchets mispriced invisibly; the two term structures; "one dial
   for both".
3. **Establish — a model with no calendar in it (§10.5.1)** — eq 10.6 read structurally;
   time-homogeneity as a *type-level* fact, anchored on `hestonGenerator`
   (heston_scratch.lean:241 — no time argument); CEV's right-forward/wrong-maturity split.
4. **Establish — what calibration puts in (§10.5.2)** — eq 10.7 defined; Dupire ratio as
   definition (gated as theorem); **eq 10.8 taught from `dupireRatio_k_slope`** (build
   deliverable); `ruleOfTwo`; `localSkew_tendsto`; the calendar-time reading.
5. **Establish — the forward skew (eq 10.9)** — `forwardSkew_eq_half`, `forwardSkew_tendsto`,
   the ⅕/⅛/<⅒ readings (`norm_num`); the rule-of-two-in-reverse step identified explicitly as
   chapter math anchored on §4's identity.
6. **Establish — whether the trade is forced (§10.5.3)** — eq 10.10 with
   `covariation_itoIntegralCLM_T`/`variance_itoIntegralCLM_T` (ItoIntegralCovariation.lean:72/:84)
   and `itoDrift2D`; the no-t argument anchored on `hestonGenerator`; the table as source
   data; hot-start caveat.
7. **The gated boundary — stated plainly** (six items above).
8. **What the stack has (grep-verified)** — updated inventory incl. build-face greek layer.
9. **Connect** — 0059 (rule of two's origin; same chapter), 0058 (Dupire's gate), Gyöngy
   (`gyongy_mimicry_gated`, GyongyScratch.lean:1516 — vanillas see marginals, forward smiles
   are where the missing dynamics surfaces), heston_scratch/0022, hook to 0061 (the mixing
   weight λ becomes observable in forward smiles).
10. **ask-your-tutor admonish** (0059, same chapter, carries one — include).
11. **Primary source** — Bagaria ch. 10.5, pp. 181–184.
12. **Exercises + Answers** — keep the stub's attempt exercise (verified: (3/4)√(T₀/t) gives
    0.217/0.108/0.069 vs the chapter's ⅕/⅛/<⅒); add the rule-of-two substitution, a
    structural CEV question, and a "which column does your model get right" discussion.

## Stale references in the current stub text

1. **Lines 30–34 ("What the stack has")**: "CEV, Heston-as-process, Dupire on a parametric
   surface, and any forward-measure apparatus: none found in the clones." — Half-stale:
   process-level Heston is still absent (correct), but `builds/lean/heston_scratch.lean`
   landed 2026-10-13 (Tier-2 item 19) with the no-t generator — the §10.5.3 anchor exists
   and the stub predates it. Also omits the build-face bsV greek layer any eq-10.8 build
   composes (PDE.lean:302/:338/:351/:419, StrikeGreeks.lean:43/:85/:98/:174).
2. **Lines 3–6 (BLOCKED reason)**: "needs the forward-measure/numeraire machinery" to verify
   eqs 10.8–10.9 — over-wide; §10.5.2's derivation uses Dupire's ratio + calendar-axis
   reading only (p. 182). Forward-measure machinery gates the *table*, not the identities.
3. **Line 6**: "a simulation/slice-extraction layer — none assembled" — still true for
   slices, but `mc_pricer.lean` (BS-terminal MC, SLLN+CLT) landed since the scan and is the
   extension point; the stub doesn't mention it.
4. **`model-coverage-map.md:52`** (Part II row for ch10): "Missing: … affine char-function
   derivation" — stale; the 2D real affine exponent landed (`heston_scratch.lean`; only the
   complex-u route remains open per its header).
5. **`model-coverage-map.md:128`** (flip row): blocker "forward-measure/variance machinery
   unassembled | lessons 0021 + 0027 assembly" — to be rewritten on flip (blocker becomes
   the ForwardSmileScratch build; the forward-measure item moves to the table's gate).
6. **AGENTS.md split-file note** "PDF page = printed page, offset +0" — false for the ch10
   file (PDF = printed − 172; verified by rendering PDF page 10 = printed 182).

## Verification log (what this E-pass actually ran)

- `pdftotext …/ch10-smile-dynamics-stochastic-volatility.pdf /tmp/ch10.txt` + reads of the
  §10.5 region (lines 440–700).
- `pdftoppm -f 10/-f 11` → page images for printed pp. 182/183 (eq 10.8 numerator; the
  4×2 table) — both read visually.
- Greps: `CEV|SABR|Dupire|eston` over `mathfin/MathFin` and the build-face MathFin
  (all empty except Heston substrings); anchor names (`bsV_vega_pos`,
  `covariation_itoIntegralCLM_T`, `variance_itoIntegralCLM_T`, `itoDrift2D`,
  `gyongy_mimicry_gated`, `exists_driftCoeff_fn`, the bsV greek layer) at the cited
  path:line — all present.
- `python3` arithmetic check of the rule of two (factor 2.0) and the ⅕/⅛/<⅒ readings
  (0.2133/0.1079/0.0684 exact; 0.2165/0.1083/0.0685 asymptotic).
- Hand verification (calculation, not Lean) that the first-order implied-variance expansion
  of the Dupire ratio reproduces the printed eq 10.8 exactly.
- Not run: any Lean compile (E-pass is read-only; the build itself is the B-pass).

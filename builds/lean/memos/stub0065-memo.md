# Memo — E-pass for flipping stub lesson 0065 (the spectral route)

**Date**: 2026-10-14. **Dispatcher**: stub-flip pass (QUEUE.md footer: "NEXT: the 12 stub
lessons per the model-coverage-map registry"; NOTES.md:667 records the remaining stubs as
"all gated on NEW builds").
**Subject**: `mdbook/src/lessons/0065-the-spectral-route.md` (STUB; SUMMARY.md:141).

**Read this ask**: the stub in full (61 lines);
`resources/fixed-income-notes-chapters/scans/ch14-scan.md` in full;
`pdftotext resources/fixed-income-notes-chapters/ch14-solvable-models.pdf` → /tmp/ch14.txt
(§14.5 read in full, extraction lines 1077–1346; printed page = PDF page, offset +0 per the
scan header "pp. 248–268"); sibling FULL lesson 0064 in full;
`builds/lean/cir_existence_scratch.lean` (header + OU section, lines 1–340 of 624);
`builds/lean/ForwardEqScratch.lean` stage-3 region (grep + reads);
`builds/lean/QUEUE.md` (footer + DONE-log); `mdbook/src/NOTES.md` stub-session section
(654–670); `mdbook/src/reference/model-coverage-map.md` (ch14 rows, :56 and :131);
`builds/lean/memos/stub0068-memo.md` (the flip-register model); AC-build-face mathlib and
MathFin sources (greps quoted below).

---

## 1. Verdict: **needs-build** (small; polynomial algebra only — no analysis)

The stub's blocker sentence is **still true and stays true after any build at this pin**:
no $L^2(\pi)$ operator theory, no eigenfunction expansion, no spectral gap exists anywhere
in the clones (re-grepped this ask, §2). So a "flip now" that taught the spectral route as
stack math would overclaim — total loss.

But the stub's own path-to-unblock already identified the honest flip shape, and the
workspace's recorded plan (model-coverage-map.md:131, unblock path "**Hermite layer
build**"; NOTES.md:667 "all gated on NEW builds") names it too. The **smallest honest
build** is the polynomial spectral slice: the OU generator as a map on `Polynomial ℝ` plus
the eigenfunction identity $\mathcal{L}\,He_n(x/s) = -n\kappa\,He_n(x/s)$ (eq. 14.16's OU
case / Calc 14.14) by induction on `hermite_succ`, the Gaussian no-flux score instance of
Calc 14.13, and the two-mode gap-bias inequality. Estimated 150–350 lines; **pure
polynomial/real-algebra + one `deriv` computation — no SDE, no measure theory, no
unbounded operators**. After it lands, the flip is a standard full-with-scope-cut: proved
polynomial core + explicit operator-theory boundary (the pattern of the 0054/0058/0068
flips: NOTES.md:654–656, "each teaches only proved math with an explicit gated-boundary
section").

**Fallback** (if the queue prefers not to spend a B-pass): a flip is *defensible now* at
the lesson-0064/0067 chapter-math standard — every §14.5 equation is PDF-verified below,
the stack anchors exist on the build face, and the boundary paragraph would quote the
gates. But it would make 0065 the only FULL lesson whose **central theorem** (the
eigenfunction identity) has neither a landed lemma nor a landed derivation route (0064
routes its ladder through the landed `itoDrift`; 0067's taught content is contract logic
over landed leg definitions). The build is cheap and removes that exposure; recommend the
build.

---

## 2. Blocker audit — what changed since the stub was written (2026-10-02)

Stub banner (`0065-the-spectral-route.md:3-7`): "no spectral theory for
Ornstein–Uhlenbeck-type operators exists in any clone: no $L^2(\pi)$ self-adjointness of a
diffusion generator, no eigenfunction expansion, no spectral gap … Mathlib has the
polynomial ingredient (`hermite`) but not the operator theory wired to it."

1. **Operator-theory absence — RE-VERIFIED TRUE this ask.** Greps over
   `mathfin/MathFin/` for `reversible|ornstein|eigenfunc|spectral`: only hits are
   `spectralRisk_translation` (an unrelated risk measure, AxiomAuditGen.lean:1007),
   `MatrixMarketMakingRiccati.lean` (finite-dimensional matrix spectral reduction — §3e),
   and a VasicekBondPrice docstring mentioning the OU representation. Greps over
   `builds/lean/*.lean` for the same + `hermite|Hermite`: zero eigenfunction builds; the
   only OU content is law-level (`cir_existence_scratch.lean`, §3c). The AC-face Hermite
   directory holds exactly `Basic.lean` + `Gaussian.lean` (`ls` verified) — **no
   orthogonality, no completeness, no $L^2(\pi)$**; AC-face `RingTheory/Polynomial/` has
   **no Laguerre, no Jacobi** (only `Chebyshev.lean`) — Ex 14.3's CIR and Jacobi rows have
   no polynomial objects on the face.
2. **New substrate landed since 2026-10-02 that the stub's "What the stack has" does not
   know about** (all verified this ask, §3): the explicit OU process with exact law
   (`ouProcess_hasLaw`, item 18), the flux-form forward equation
   (`forward_eq_timeDependent_flux`, 0054's build) — the PDE-level twin of eq. (14.19)'s
   divergence form — the 2D generator action (`hestonGenerator`, item 19), and the
   finite-dimensional spectral reduction (`matrixRiccatiCoeff` family, present on the AC
   MathFin face at `Foundations/MatrixMarketMakingRiccati.lean:90`).
3. **The Mathlib polynomial layer is intact on the build face**: `hermite` (Basic.lean:48),
   `hermite_succ` (:54), `hermite_eq_deriv_gaussian` (Gaussian.lean:61), `IsReversible`
   (Invariance.lean:**60** — the stub cites :58, stale, §7), `Matrix.exp_diagonal`
   (MatrixExponential.lean:84), `IsHermitian.exp` (:99), `Matrix.charpoly`
   (Charpoly/Basic.lean:132), bounded `Spectrum.lean`/`JointEigenspace.lean` present
   (`ls` verified).
4. Therefore the residual blocker is **exactly** what the build closes: the eigenfunction
   identity and the Gaussian no-flux instance are one polynomial induction away, and
   nothing else in the lesson is reachable at this pin.

---

## 3. Existing substrate matched to chapter equations (all verified this ask)

### 3a. The eigenfunctions as objects — build face
- `Polynomial.hermite : ℕ → Polynomial ℤ`
  (`AmericanPutConvexity/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Hermite/Basic.lean:48`,
  recursion `X * hermite n - derivative (hermite n)`); **`hermite_succ`** (:54,
  `hermite (n+1) = X * hermite n - derivative (hermite n)`) — the induction engine the
  build consumes; `hermite_zero` :63, `hermite_one` :66, `degree_hermite`/`monic_hermite`
  (:75–93 region). `hermite 2 = X^2 - 1` follows in one `simp` from `hermite_succ` — the
  Calc 14.14 $n=2$ object.
- **`hermite_eq_deriv_gaussian`** (`.../Hermite/Gaussian.lean:61`, aeval form;
  `deriv_gaussian_eq_hermite_mul_gaussian` :42; `hermite_eq_deriv_gaussian'` :68) — the
  Rodrigues formula: Hermite polynomials as Gaussian-density derivatives. This is the
  formal engine of BOTH the eigenfunction identity and Calc 14.13's score computation.

### 3b. Reversibility's formal shadow — build face
- **`IsReversible`** (`.../Mathlib/Probability/Kernel/Invariance.lean:60`): set-level
  detailed balance `∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π` for a Markov kernel;
  `IsReversible.invariant` (:65). Kernel-level only; **no diffusion-generator or
  density-level bridge** — Def 14.12 stays chapter-sourced, with this citation as "the
  definition exists, unwired" (exactly the stub's framing, line updated).

### 3c. The stationary law π concretely — item 18 build
- **`ouProcess` / `ouProcess_hasLaw`** (`builds/lean/cir_existence_scratch.lean:233/:242`)
  and **`ouProcess_integral`** (:292): the explicit OU fluctuation
  $X_t = e^{-(k/2)t}(x_0 + s\int_0^t e^{(k/2)u}dB_u)$ with exact law
  $\mathcal{N}(x_0 e^{-(k/2)t},\, \tfrac{s^2}{k}(1-e^{-kt}))$. As $t\to\infty$ the
  variance tends to $s^2/k$ — with OU rate $\kappa = k/2$ this is $\sigma^2/2\kappa$: the
  stationary law of Def 14.11 ($\pi = N(0, \sigma^2/2\kappa)$) is *the limit of a landed
  law*, not a new object. `cirVariance_mean` (:487 per stub0068-memo) is the headline
  sibling. House-pattern cousin on the AC MathFin face:
  `vasicekShortRate_hasLaw_gaussian` (`.../MathFin/FixedIncome/VasicekSDEGaussian.lean:132`,
  `#print axioms` recorded in AxiomAudit.lean:806).

### 3d. The divergence form's PDE twin — 0054's build
- **`forward_eq_timeDependent_flux`** (`builds/lean/ForwardEqScratch.lean:1269`; migration
  variant :1310): the flux (divergence) form of the Fokker–Planck equation
  $\partial_t p = -\partial_x(\mu p) + \tfrac12 \partial_x^2(v p)$ for time-dependent
  coefficients, proved by flux identification against the non-flux form. Eq. (14.19) is the
  *stationary zero-flux* specialization of exactly this structure
  ($\mu\pi = \tfrac12(\sigma^2\pi)'$ ⟺ the flux vanishes); the pairing
  $\langle \mathcal{L}f,g\rangle_\pi = -\tfrac12\int\sigma^2\pi f'g'$ stays chapter-sourced
  (it is an operator statement), but the lesson can say honestly: the PDE-level divergence
  form is landed machinery, and the Gaussian instance of the no-flux condition goes into
  the build (§6, item 5).

### 3e. Finite-dimensional spectral precedent — AC MathFin face
- **`matrixRiccatiCoeff`** (`AmericanPutConvexity/.lake/packages/MathFin/MathFin/
  Foundations/MatrixMarketMakingRiccati.lean:90`, hypothesis `Â.IsHermitian`),
  **`matrixRiccatiCoeff_spectral_sq`** (:104, `Â·Â = U·diag(λᵢ²)·Uᴴ`),
  `matrixRiccatiCoeff_isHermitian` (:116), `hasDerivAt_matrixRiccatiCoeff` (:127): a
  **landed spectral reduction** — symmetric-matrix diagonalization driving a closed form.
  This is the "finite-dimensional first" pattern of the stub's unblock step (1), already
  instantiated one floor down (matrices, not operators). Verified present on the AC face
  (`ls .../MathFin/Foundations/ | grep riccati` → both Riccati files).

### 3f. Adjacent anchors (light citations)
- **`Matrix.exp_diagonal`** (`.../MatrixExponential.lean:84`, note the `[Algebra ℚ 𝔸]`
  generality) — the diagonal-decoupling primitive behind eq. (14.17)'s "one exponential per
  mode"; `IsHermitian.exp` (:99) — self-adjoint exponentiates to a positive contraction,
  the bounded shadow of the chapter's mechanism.
- **`hestonGenerator`** (`builds/lean/heston_scratch.lean:241`,
  `hestonGenerator_expAffine2` :258, item 19) — the stack's only 2D generator action
  (exponential-affine directions); a footnote for Ex 14.2's 2D setting, not the swirl
  itself.
- **`Matrix.charpoly`** (`.../Charpoly/Basic.lean:132`) — formal home for Ex 14.2's
  spectrum claim (charpoly of the swirl's $-A$ is $(X+1)^2+\theta^2$, roots $-1\pm i\theta$).
- Lesson 0064 (FULL; `0064-polynomial-family-moment-ladder.md:41-54`): the triangular
  matrix with diagonal $-\kappa n$ — "the eigenvalues, before there are eigenvectors"
  (stub :39). The flipped 0065 is that lesson's announced completion (0064:53-54,
  0064:189-190 already cross-reference it).

---

## 4. What stays gated (honest boundary — none of it is reachable at this pin)

1. **$\mathcal{L}$ as an unbounded operator on $L^2(\pi)$, and self-adjointness**
   $\langle \mathcal{L}f,g\rangle_\pi = \langle f,\mathcal{L}g\rangle_\pi$ as an operator
   theorem (Calc 14.13's pairing). The build lands only the eval-level Gaussian score
   instance.
2. **The expansion (14.17) as a theorem** — needs the spectral theorem for unbounded
   self-adjoint operators + completeness of the Hermite basis in $L^2(\pi)$. AC face has
   bounded-operator `Spectrum.lean`/`JointEigenspace.lean` only. "Cheap across maturities"
   and "honest a-priori error" stay chapter-sourced.
3. **Spectral-gap theory** — "$\lambda_1$ is the mean reversion rate, $\ln 2/\lambda_1$
   the half-life" is a chapter reading; only the two-mode weighted-average inequality
   (build item 6) is proved. The gap-bias *moral* (second route to ch. 20) is taught as
   chapter-sourced arithmetic on top of the proved inequality.
4. **General-diffusion Calc 14.13** ("for *every* scalar diffusion") — needs density
   differentiation for general $(\mu,\sigma)$; only the Gaussian instance is in the build.
   (`forward_eq_timeDependent_flux` is the time-dependent forward equation, not the
   operator pairing — do not conflate them in the lesson.)
5. **Ex 14.2's swirl as a stochastic statement** (the 2D SDE, its stationarity, the
   film/snapshot reversibility test) — only matrix-algebra fragments are stretch goals
   (charpoly, $\Sigma = \tfrac12 I$ isotropy by $2\times2$ algebra). `hestonGenerator`
   covers exponential-affine directions only.
6. **The reversibility bridge** — `IsReversible` is kernel-level (Invariance.lean:60);
   Def 14.12 ↔ generator self-adjointness has no stack home.
7. **CIR/Laguerre and Jacobi/Beta rows of Ex 14.3** — no Laguerre or Jacobi polynomials on
   the AC face (only `Chebyshev.lean` in `RingTheory/Polynomial/`); the Pearson table is
   taught with the OU row proved and the other two rows chapter-sourced.
8. **The numerical cross-check** the chapter itself runs (p. 265: "quant/src/generator.rs
   verifies this for the first five eigenfunctions … and the expansion (14.17) end to end")
   — has no Lean counterpart; do not imply one exists.

---

## 5. Chapter anchors (pdftotext /tmp/ch14.txt; printed page = PDF page, offset +0)

- **p. 263–264**: the spectral route intro; **eq. (14.16)** ($\mathcal{L}\varphi_n =
  -\lambda_n\varphi_n$, extraction :1086) and **eq. (14.17)** ($P_t f = \sum_n c_n
  e^{-\lambda_n t}\varphi_n$, :1095); "cheap across maturities, honest a-priori error"
  (:1092–1096 region).
- **p. 264**: **Def 14.11** ($L^2(\pi)$, inner product eq. (14.18), :1114; stationary
  reading $N(0,\sigma^2/2\kappa)$ :1118–1122); **Def 14.12** (reversible, :1124; the
  film test :1126–1131); **Calc 14.13** (:1131): no net flux ⟹ $\mu\pi =
  \tfrac12(\sigma^2\pi)'$, divergence form **eq. (14.19)** (:1146), pairing + symmetry
  (:1148–1152, "symmetric in $f$ and $g$ on its face").
- **p. 264–265**: **Ex 14.2** (swirl, :1159; $A$ matrix :1162–1165; $\Sigma = \tfrac12 I$
  isotropy :1173–1176; the two pairings $-\alpha^\top A\Sigma\beta$ vs
  $-\alpha^\top\Sigma A^\top\beta$ :1180–1184; eigenvalues $-1\mp i\theta$ :1186;
  "one-dimensional tool", structural reason :1188–1193).
- **p. 265**: **Ex 14.3** (Pearson table, :1194–1212: OU/Hermite/$-n\kappa$,
  CIR/Laguerre/$-n\kappa$, Jacobi/Beta; "the intersection of the two ideas");
  **Calc 14.14** (:1220): $s^2 = \sigma^2/2\kappa$, $\mathcal{L}He_n = -n\kappa He_n$;
  the $n=2$ mechanism (:1226–1232, $f = (x/s)^2-1$, $Lf = -\kappa x\cdot\frac{2x}{s^2} +
  \frac{\sigma^2}{2}\cdot\frac{2}{s^2} = -2\kappa f$); numerical cross-check note :1241.
- **p. 265–266**: Remark, what the spectrum is good for (:1238ff): cheap across maturities;
  honest error; gap = mean reversion rate, $\ln 2/\lambda_1$ half-life (:1256–1261).
- **p. 266**: Remark, the gap is an asymptotic rate (:1263ff): effective decay
  $-\frac{d}{dt}\ln$ of the sum = **weighted average** $\frac{\sum\lambda_n c_n
  e^{-\lambda_n t}}{\sum c_n e^{-\lambda_n t}}$ (:1282), above $\lambda_1$ early when
  weights share a sign; one-exponential fit overstates mean reversion (:1288–1291) —
  "second and independent route" to ch. 20's bias.
- **p. 267**: Fig. 14.3 (all-modes vs slowest mode; fitted-rate curve, :1346–1380).

---

## 6. Build requirement (the smallest honest build)

**New module** `builds/lean/ou_spectral_scratch.lean` (final name per S-pass), compiled on
the build face: `cd AmericanPutConvexity && lake env lean ../builds/lean/ou_spectral_scratch.lean`.
Section variables $\kappa\ \sigma : ℝ$ (and $s$ with $s^2 = \sigma^2/(2\kappa)$, i.e.
hypothesis `2 * κ * s^2 = σ^2`). Deliverables, in dependency order:

1. **`ouGen`** — the OU generator as a polynomial map on `Polynomial ℝ`:
   `p ↦ -(κ • X) * p.derivative + (σ^2/2) • p.derivative.derivative`
   (the object lesson 0064's Connect "build order (1)" asked for; pure `Polynomial` API).
2. **Commutator lemmas** (the induction engine, all `derivative_mul`/`derivative_X`
   algebra): `ouGen_derivative : ouGen p.derivative = (ouGen p).derivative + p.derivative`;
   `ouGen_X_mul : ouGen (X * p) = X • ouGen p + p.derivative - X • p`.
3. **`ouGen_hermite`** (unit parameters, $\mathbb{Z}\to\mathbb{R}$ via
   `Polynomial.map`): `ouGen (map (hermite n)) = -(n : ℝ) • map (hermite n)` — induction on
   `n` via `hermite_succ` (`Basic.lean:54`); base `hermite_zero`. **This is eq. (14.16)'s
   OU case / Calc 14.14's identity** — the lesson's centerpiece, proved.
4. **`ouGen_heigen_scaled`** (eval level, $s^2 = \sigma^2/(2\kappa)$): for
   $q_n(x) = He_n(x/s)$, `eval x (ouGen_{κ,σ} q_n) = -(n*κ) * eval x q_n` — chain rule on
   the scaling (or a scaled-polynomial lemma). Includes the **`n = 2` instance**
   (`ouGen_heigen_two`) reproducing Calc 14.14's displayed computation verbatim.
5. **`gaussianScore_ou`** — Calc 14.13's no-flux condition for the Gaussian stationary
   law, eval level: `deriv (fun x => exp (-x^2/(2*s^2))) x = -(x/s^2) * exp (-x^2/(2*s^2))`,
   hence $(\sigma^2/2)\cdot\pi' = -\kappa\,x\cdot\pi$ when $s^2 = \sigma^2/(2\kappa)$
   (`deriv_exp` + chain rule; `hermite_eq_deriv_gaussian`, Gaussian.lean:61, is the
   family-level engine to cite).
6. **`twoMode_rate_ge_gap`** — the gap-bias core: for `0 ≤ λ₁ ≤ λ₂`, `0 < c₁`, `0 < c₂`,
   `0 ≤ t`:
   `(λ₁*c₁*exp(-λ₁*t) + λ₂*c₂*exp(-λ₂*t)) / (c₁*exp(-λ₁*t) + c₂*exp(-λ₂*t)) ≥ λ₁`
   (cross-multiplied; `field_simp` + `nlinarith`). The chapter's weighted average
   (:1282) restricted to two modes with shared-sign weights.
7. **Stretch, not gates**: `swirl_charpoly` — `Matrix.charpoly` of the swirl's $-A$ equals
   $(X+1)^2+\theta^2$ (roots $-1\pm i\theta$; `Matrix.charpoly`, Charpoly/Basic.lean:132),
   and/or the isotropy $\Sigma = \tfrac12 I$ from $A\Sigma + \Sigma A^\top = I$ by
   `Matrix` algebra; a `Tendsto` corollary of `ouProcess_hasLaw`'s variance to
   $s^2/k$ (the stationary variance).

**Closest existing substrate to build from**: `hermite`/`hermite_succ` (AC
`Hermite/Basic.lean:48/:54`), `hermite_eq_deriv_gaussian` (AC `Hermite/Gaussian.lean:61`),
`ouProcess_hasLaw` (`cir_existence_scratch.lean:242`) for the stationary-law connection,
`forward_eq_timeDependent_flux` (`ForwardEqScratch.lean:1269`) as the divergence-form
precedent, `matrixRiccatiCoeff` (AC MathFin `MatrixMarketMakingRiccati.lean:90`) as the
finite-dimensional spectral precedent, `vasicekShortRate_hasLaw_gaussian` (AC
`VasicekSDEGaussian.lean:132`) as the OU-law house pattern.

**Gates**: `lake env lean` zero error/sorry; `#print axioms` standard-three on every public
theorem; statement-fidelity diff against /tmp/ch14.txt :1086 (eq. 14.16 OU case), :1146
(eq. 14.19 Gaussian instance), :1220–1236 (Calc 14.14), :1282 (weighted average). Note:
AC-face mathlib materializes source without oleans — the compile gate is `lake env lean`
from inside `AmericanPutConvexity/`, per the build-face convention (AGENTS.md
§Name-verification).

After landing: record in `builds/lean/README.md` + `QUEUE.md`; update the registry row
(model-coverage-map.md:131) in the same edit as the lesson flip; optional promotion target
`MathFin/FixedIncome/OUSpectral.lean` per the promotion workflow (blocked on upstream
#244 per AGENTS.md §Upstream-PR discipline — fork-side only).

---

## 7. Stale references in the current stub text

| Location | Text | Status |
|---|---|---|
| 0065:36 | "`IsReversible` … (`Mathlib/Probability/Kernel/Invariance.lean:58`)" | **Line stale**: :60 on the AC build face (grep this ask). Flip must cite the build face. |
| 0065:32 | "Grep-verified (ch. 14 scan, re-verified 2026-10-02)" | **Date stale**: items 18/19 + ForwardEq/Gyongy/mc/cms/cox/hw landed since. Absence claims re-verified TRUE this ask (§2.1); the section must ADD the new substrate (§3c–3e). |
| 0065:32–35 | "What the stack has" lists mathlib4 only | **Incomplete on the build face**: `hermite` :48 and `hermite_eq_deriv_gaussian` (Gaussian.lean:61) exist on the AC face — cite the build face per AGENTS.md convention; note no Laguerre/Jacobi there (affects how Ex 14.3 is taught). |
| 0065:3–7 (banner) | the operator-theory absence | **Still TRUE** — not stale; replaced at flip by the build status after §6 lands. |
| 0065:51–56 (path to unblock) | steps (1)–(5) | Correct; superseded by the concrete §6 spec. New fact the stub could not know: the flux-form PDE machinery (ForwardEqScratch stage 3) softens step (2)'s framing — the divergence form exists at PDE level; the pairing stays gated. |
| 0065:38–39 | `Spectrum.lean`, `JointEigenspace.lean`, `MatrixExponential.lean` incl. `IsHermitian.exp` | Not stale — re-verified on AC face (`MatrixExponential.lean:84/:99`). |
| 0065:39 | "lesson 0064's triangular diagonal $-\kappa n$ — the eigenvalues, before there are eigenvectors" | Not stale; 0064:53-54/189-190 already cross-reference 0065 as the completion. |
| `model-coverage-map.md:131` | blocker "no OU spectral theory / orthogonal-polynomial eigenfunctions", path "Hermite layer build" | Update in the flip's same edit (post-build: blocker → landed `ouGen_hermite` etc.). |

---

## 8. Section skeleton for the flipped lesson (each section names its lemma)

**H1 + Goal**: the second route to solvability — diagonalise the generator; proved
substrate: the OU Hermite layer (`ouGen_hermite`, `ouGen_heigen_scaled`,
`gaussianScore_ou`, `twoMode_rate_ge_gap` — new build) over `hermite_succ`; honestly gated:
the $L^2(\pi)$ expansion and spectral-gap theory.

1. **Motivate — eigenvalues without eigenvectors.** 0064 ended at the triangular diagonal
   $-\kappa n$ (0064:41–54); §14.5 is the announced completion, and the second independent
   route to ch. 20's estimation bias. Link: 0054's gated $P_t$ (the semigroup object the
   expansion is about does not exist in the stack — say so here, once).
2. **Establish A — the diagonal invariant family (eqs. 14.16/14.17).** Chapter math;
   `Matrix.exp_diagonal` (`MatrixExponential.lean:84`) as the decoupling primitive — one
   exponential per mode; honest note: this is the shape of the theorem, not the theorem.
3. **Establish B — the weighted space and reversibility (Defs. 14.11/14.12).** Chapter
   math; `IsReversible` (`Invariance.lean:60`) as the kernel-level definition, unwired;
   π concretely: `ouProcess_hasLaw` (`cir_existence_scratch.lean:242`) — stationary
   variance $s^2/k = \sigma^2/2\kappa$ as the limit of a landed law.
4. **Establish C — one dimension is free (Calc 14.13, eq. 14.19).** Chapter math for the
   general statement; the PDE-level precedent `forward_eq_timeDependent_flux`
   (`ForwardEqScratch.lean:1269`); the Gaussian instance **proved**:
   `gaussianScore_ou` (new build), with `hermite_eq_deriv_gaussian` (`Gaussian.lean:61`)
   as the Rodrigues engine.
5. **Establish D — the Hermite eigenfunctions (Calc 14.14) — the proved core.**
   `ouGen_hermite` + `ouGen_heigen_scaled` + `ouGen_heigen_two` (new build) via
   `hermite_succ`; the $n=2$ mechanism as the chapter displays it; the Pearson table
   (Ex 14.3) with the OU row proved, CIR/Jacobi rows chapter-sourced (no Laguerre/Jacobi
   on the face).
6. **Establish E — where it fails: the swirl (Ex 14.2).** Chapter math; matrix fragments
   via `Matrix.charpoly` (`Charpoly/Basic.lean:132`, stretch `swirl_charpoly`);
   `hestonGenerator` (`heston_scratch.lean:241`) as the existing 2D-generator footnote;
   the structural boundary — a one-dimensional tool.
7. **Establish F — the gap is an asymptotic rate.** `twoMode_rate_ge_gap` (new build);
   the weighted average (:1282); one-exponential fit overstates mean reversion → ch. 20
   cross-link (chapter-sourced beyond two modes).
8. **Honest boundary** — the §4 gates, quoted precisely (expansion, self-adjointness,
   completeness, gap theory, general Calc 14.13, swirl-as-process, Laguerre/Jacobi, the
   chapter's own numerical check).
9. **Connect.** 0064 (the diagonal completed), 0054 (gated $P_t$), 0022/0033 (the
   transform route — the other solvability), 0072/ch. 20 (the bias), and the
   finite-dimensional precedent `matrixRiccatiCoeff`
   (`MatrixMarketMakingRiccati.lean:90`) — spectral reduction one floor down, landed.
10. **ask-your-tutor admonish** (e.g.: "ask why the swirl's snapshot cannot see the
    rotation — stationary law isotropic, spectrum complex — and what that says about
    fitting two-factor models one factor at a time").
11. **Primary source** (ch. 14 PDF §14.5 pp. 263–267; scan ledger; the build file + the
    §3 anchor files with AC-face-first citations) → **Exercises** (carry the stub's
    attempt exercise forward as Ex 1, now with the landed lemma name; a two-mode-numbers
    exercise for F; a charpoly exercise for E) → **Answers**.

Registration: SUMMARY.md:141 already carries the lesson; the flip edits the lesson file +
registry row (model-coverage-map.md:131) in the same edit.

---

## 9. Verification record

Commands run this ask (outputs quoted above):
- `pdftotext resources/fixed-income-notes-chapters/ch14-solvable-models.pdf /tmp/ch14.txt`
  + sed reads of extraction lines 1037–1400 (§14.5 in full) and anchor greps (:1086, :1095,
  :1114, :1124, :1131, :1146, :1159, :1194, :1220, :1241, :1261, :1282, :1288, :1379).
- AC-face mathlib greps: `Hermite/Basic.lean` (:48/:54/:57/:63/:66/:75-93),
  `Hermite/Gaussian.lean` (:42/:61/:68), `Probability/Kernel/Invariance.lean` (:60/:65,
  def body read), `Analysis/Normed/Algebra/MatrixExponential.lean` (:28/:84/:99),
  `LinearAlgebra/Matrix/Charpoly/Basic.lean` (:132); `ls` of the Hermite dir (Basic +
  Gaussian only), `RingTheory/Polynomial/` (no Laguerre/Jacobi; Chebyshev present),
  `Analysis/InnerProductSpace/` (Spectrum + JointEigenspace present).
- AC-face MathFin grep: `vasicekShortRate_hasLaw_gaussian` (`VasicekSDEGaussian.lean:132`,
  AxiomAudit.lean:806); `ls Foundations | grep riccati` (both Riccati files present).
- Substrate greps: `builds/lean/*.lean` for ornstein/eigenfunc/spectral/self-adjoint/
  reversible/hermite (only `cir_existence_scratch.lean` OU law-level);
  `mathfin/MathFin/` for the same (only spectralRisk, MatrixMarketMakingRiccati, a
  docstring); `ForwardEqScratch.lean` flux region (:1248–1350);
  `heston_scratch.lean` `hestonGenerator` (:241/:258).
- Read: lesson 0064 in full; lesson 0065 (stub) in full; ch14-scan.md in full;
  QUEUE.md footer + DONE-log; NOTES.md:640–670; model-coverage-map.md ch14 rows;
  stub0068-memo.md in full (register model); cir_existence_scratch.lean:1–340.

**Not run this ask** (reported as such): `cd AmericanPutConvexity && lake env lean` on any
file (no new build proposed here — the §6 build is the unlock), and `mdbook build` /
`check_links.py` (no lesson edit made in an E-pass). The B-pass re-verifies both faces at
first checkpoint per ROUTING.md.

**Verdict restated**: **needs-build** — the §6 polynomial spectral slice (est. 150–350
lines, no analysis) unlocks an honest full-with-scope-cut flip; until it lands, 0065 stays
a stub, per the workspace's own recorded plan (NOTES.md:667, model-coverage-map.md:131).

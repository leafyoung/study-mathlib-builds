# Machine-Checked Math for Quants — Lean build artifact (v1.1.0)

The complete, reproducible Lean artifact of the study-mathlib build program: formalized
quant-finance mathematics on Mathlib + MathFin, built as the research layer of the
mdbook course *"Machine-Checked Math for Quants"*.

## What's here

`builds/lean/` — 18 primary build files (~18,100 lines, ~510 theorem/lemma
declarations), every one **sorry-free** with all public declarations depending only on
`[propext, Classical.choice, Quot.sound]`:

| Area | Files |
|---|---|
| Affine engine / CIR / Heston | `AffineEngineScratch.lean`, `cir_existence_scratch.lean`, `heston_scratch.lean` |
| Itô–drift identity + Gyöngy | `ItoContribution*.lean`, `GyongyScratch.lean` |
| Forward (Fokker–Planck) equations, stages 1–3 | `ForwardEqScratch.lean` (incl. flux form, item 10) |
| Hull–White / bootstrapping / Jamshidian | `hw_scratch.lean`, `hw_bootstrap.lean`, `jamshidian_scratch.lean` |
| Greeks / capstone / CMS / credit / MC pricer | `greeks_signs.lean`, `scratch.lean`, `cms_scratch.lean`, `cox_scratch.lean`, `mc_pricer.lean` |
| **v1.1.0 unlocks** | `ForwardSmileScratch.lean` (eq. 10.8), `lsv_scratch.lean`, `ou_spectral_scratch.lean` (eq. 14.16 OU case), `inflation_scratch.lean` (eqs. 17.6–17.10), `EstimationScratch.lean` (eq. 21.2's D-term), `discrete_var_scratch.lean` (VaR subadditivity failure) |
| Promotion series (upstream staging) | `port-test-*.lean`, `promotions/` (PR-2..6 patches + descriptions) |

Plus the program ledgers (`QUEUE.md`, `PUBLISHING.md`, `ROUTING.md`, `README.md`,
`memos/`) recording every item's provenance, verification transcript, and substrate
findings.

## Reproducing

```bash
# elan toolchain: leanprover/lean4:v4.32.0
git clone https://github.com/robertmartin8/AmericanPutConvexity
cd AmericanPutConvexity && lake build   # fetches pinned Mathlib/MathFin
cp <file>.lean . && lake env lean <file>.lean   # exit 0 = verified
```

The promoted modules (Itô batch, Hull–White calibration, Monte-Carlo pricer,
Cox/CMS/Bootstrapping — PR-1..6) are **merged upstream**:
[formal-mathfin main](https://github.com/formal-applied-math/formal-mathfin) via
[#244](https://github.com/formal-applied-math/formal-mathfin/pull/244) and
[#247](https://github.com/formal-applied-math/formal-mathfin/pull/247), from the
fork [`leafyoung/formal-mathfin`](https://github.com/leafyoung/formal-mathfin).

## Provenance

Built research-first against Bagaria's *Fixed Income & Derivative Pricing* notes
(per-chapter scan ledgers) with every name grep-verified against the pinned
dependency faces; full program history in `builds/lean/QUEUE.md` and the course book
(mdbook, in the source workspace).

## License

Apache-2.0 (matching the Mathlib/MathFin ecosystem this builds on).

# Machine-Checked Math for Quants — Lean build artifact (v1.0.0)

The complete, reproducible Lean artifact of the study-mathlib build program: formalized
quant-finance mathematics on Mathlib + MathFin, built as the research layer of the
mdbook course *"Machine-Checked Math for Quants"*.

## What's here

`builds/lean/` — 12 primary build files (~14,000 lines, ~380 theorem/lemma
declarations), every one **sorry-free** with all public declarations depending only on
`[propext, Classical.choice, Quot.sound]`:

| Area | Files |
|---|---|
| Affine engine / CIR / Heston | `AffineEngineScratch.lean`, `cir_existence_scratch.lean`, `heston_scratch.lean` |
| Itô–drift identity + Gyöngy | `ItoContribution*.lean`, `GyongyScratch.lean` |
| Forward (Fokker–Planck) equations, stages 1–3 | `ForwardEqScratch.lean` (incl. flux form, item 10) |
| Hull–White / bootstrapping / Jamshidian | `hw_scratch.lean`, `hw_bootstrap.lean`, `jamshidian_scratch.lean` |
| Greeks / capstone / CMS / credit / MC pricer | `greeks_signs.lean`, `scratch.lean`, `cms_scratch.lean`, `cox_scratch.lean`, `mc_pricer.lean` |
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

The upstream-facing modules (Hull–White calibration, Monte-Carlo pricer, Itô batch,
Cox/CMS/Bootstrapping) also live in [`leafyoung/formal-mathfin`](https://github.com/leafyoung/formal-mathfin)
(branch `ito-drift-expectation`, fork `main` @ `5708258`), submitted upstream as
[formal-mathfin#244](https://github.com/formal-applied-math/formal-mathfin/pull/244).

## Provenance

Built research-first against Bagaria's *Fixed Income & Derivative Pricing* notes
(per-chapter scan ledgers) with every name grep-verified against the pinned
dependency faces; full program history in `builds/lean/QUEUE.md` and the course book
(mdbook, in the source workspace).

## License

Apache-2.0 (matching the Mathlib/MathFin ecosystem this builds on).

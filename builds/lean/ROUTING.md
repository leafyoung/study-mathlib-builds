# ROUTING.md — multi-pass model routing for the build program

*Operationalizes the benchmark verdict (benchmark/tier2/results.md): flash:max
for content exploration at ~1/4 the credit cost; glm-5.3 max for anything
landing under a required name (flash's failure mode there is name-bound
degradation — a compile-clean, sorry-free theorem bound to a degenerate
specialization). With flexibility: glm:max may explore when the work is
statement-judgment-shaped.*

## Mechanisms (verified 2026-10-13)

| Mechanism | How | Status |
|---|---|---|
| **Pinned agent definitions** (primary) | `.zcode/agents/flash-explorer.md` (GLM-5.3-Flash, max, read-only) + `.zcode/agents/glm-builder.md` (GLM-5.3, max, full tools) — `model:` + `thoughtLevel:` frontmatter | live from the NEXT session (registry loads at session start; probe on 2026-10-13 confirmed not hot-reloadable) |
| **Manual session switch** (fallback; the only option in the session where this was written) | user flips the session model; unpinned subagents (general-purpose) inherit it | always available |
| Workflow `subagent_model` | `CreateWorkflow` accepts a per-run model override | exists; not used (no workflow request) |

**Fallback enforcement**: before any B-pass dispatch on the manual-switch path,
the orchestrator runs `ListModels` and confirms `[current]` is glm-5.3; if not,
HOLD the dispatch and ask the user to switch. E-passes conversely require
`[current]` = flash (unless deliberately escalated to glm — allowed anywhere).
The orchestrator's own work (S/V passes, specs, verification, commits) is
name-binding work and stays on glm regardless.

## The four passes (per build item)

| Pass | Agent | Cost class | Deliverable |
|---|---|---|---|
| **E — Explore** | flash-explorer (read-only) | ~10–40 cr | substrate memo: verified name inventory (file:line, exact signatures, pin vs HEAD), 1–3 routes through verified substrate, conflicts, explicit unknowns |
| **S — Specify** | orchestrator (glm) | — | build spec with EXACT theorem names + signatures (the statement-fidelity contract), sources, verification bar; stored verbatim in QUEUE.md |
| **B — Build** | glm-builder | 100s of cr | the deliverable .lean under the contract names; WIP checkpoints; self-run verification bar |
| **V — Verify** | orchestrator (glm) | — | compile + axioms + **statement-fidelity diff** (escalation trigger #5: diff delivered names/signatures against the S-pass contract — never trust compile-pass alone) + NOTES.md + commit |

Escalation E→glm (the flexibility clause) — route exploration to glm (either
pinned glm-builder in explore mode, or orchestrator does it inline) when ANY of:

1. **Greenfield**: no upstream names to grep — the route itself must be invented
   (e.g. item 11 Y-existence).
2. **Context ceiling**: answering requires holding a >3000-line substrate file
   (e.g. anything consuming ItoContribution.lean's 6,700 lines).
3. **Flash self-reports ESCALATE** — unresolved name/signature conflicts in its
   memo.
4. **Statement-judgment is the task**: deciding which generalization survives is
   never delegated to flash (the tier2 probe's lesson).

Hybrid is the norm for mixed items: flash sweeps the known substrate, glm
explores only the delta.

## Manual-switch batching protocol (fallback path)

Model flips are manual, so passes are BATCHED, never interleaved:

1. User sets session → flash; orchestrator runs ALL pending E-passes (batched
   across queue items) via general-purpose agents; archives memos to
   `builds/lean/memos/itemNN-memo.md`.
2. User sets session → glm; orchestrator runs S on the memos, dispatches B
   (one at a time per quota discipline), runs V per landing.
3. Pass-state per item is tracked in QUEUE.md (new column): `E→S→B→V` position,
   so any interruption (quota outage mid-batch, session end) resumes cleanly —
   same resume protocol, one more state axis.

## Queue mapping (2026-10-13)

| Item | Route | Rationale |
|---|---|---|
| 19 Heston 2D affine (IN FLIGHT) | B(glm) already dispatched pre-routing; on landing run V with fidelity diff vs the QUEUE-stored spec | — |
| 10 Forward-eq stage 3 (Dupire (t,x)) | E(flash): sweep ForwardEqScratch + lesson 0021 + ch21 anchors → E'(glm): coefficient-structure judgment → S → B(glm) | mixed: substrate half-known; the Dupire coefficient argument is statement-judgment |
| 11 Gyöngy Y-existence | glm-only (E' straight to glm exploration, possibly multi-round) | research-grade greenfield |
| PR-2..7 module-ization (PUBLISHING.md) | E(flash): dep-map each landed build (imports, private lemmas, house-style deltas vs mathfin/CONTRIBUTING) → S → B(glm): the split landing under upstream-required names → V with the per-PR checklist | mechanical mapping = flash's sweet spot; upstream names = glm |
| 0054/0058/0060 stub unblocking | inherits item 10's route (forward-eq substrate) | lesson status flips on landing |
| Future "existence"-class items | glm-only | statement judgment |

## Standing rules

- Sequential heavy agents (quota discipline): never E(flash) concurrent with
  B(glm) unless the E is trivial; never two B's.
- Memos are archived (`builds/lean/memos/`) — they outlive sessions and are the
  E-pass resume artifact (an interrupted batch re-runs only missing memos).
- Every V records the fidelity-diff result in NOTES.md, pass or fail.
- When the pinned agents go live (next session), the manual protocol retires to
  fallback-only; dispatch by agent type, session model untouched.

# GARCD Lean 4 root-owner / GLOBAL_BEST handoff — 2026-11-10

## Source of truth and authority

- Canonical research branch: `research/modularize-2026-11-09` (source checkpoint `d2a0cad64f8ff0363101f1889329628b9052c894`).
- Evidence: [Actions run 42730914791](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42730914791), exact SHA `d2a0cad64f8ff0363101f1889329628b9052c894`: `GARCD.Module01` through `GARCD.Module04` returned exit code **0**.
- `GARCD.Module05` failed with **5 direct diagnostics**; `Module06`–`Module12` and `Support` could not be independently verified because they import failed dependencies. Do not count their repeated traces as independent errors.
- GitHub Actions setup + Mathlib cache successful. Import aggregation, clean builds, and independent `#print axioms` are not yet completed.
- No upstream universal DESC/A-0/B-0 unconditional theorem is claimed.

## Module04: resolved root groups and one NO-GO local identity

| Owner | Original locations | Category | Resolution | Evidence |
| --- | --- | --- | --- | --- |
| PARITY | 177, 197, 207, 313, 371 | ROOT_INDEPENDENT / SAME_ROOT_SIBLING | Make odd-power proof independent of word length; align sum exponents; use `Nat.mul_mod` for odd multiplier | [42730914791](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42730914791) |
| WGT-SUM | 497, 507, 1037 | ROOT_INDEPENDENT | Normalize exponent subtraction before `rw`; equate finite sums termwise | same |
| REPEAT | 767, 813, 829 | ROOT_INDEPENDENT / SAME_ROOT_SIBLING | Preserve recursive IH, make `mul_sum` type clear, distribute right-hand sum with `conv_rhs`, instantiate IH after shifting powers | same |
| ROTATION | 1067 | NO-GO local intermediate, CORRECTED | **Discarded false intermediate:** `hC_rot` used coefficient `3^(m-1-j)`; the correct `hC_rot_exact` uses `3^(m-j)`. The overall public rotation theorem stays unweakened and compiles. | same |

### Independent numerical counterexample to the discarded local formula

Let `a₀ = 1`, `tl = [1]`, `m = 1`, `w = [1,1]`. Then `C_p(w) = 3 + 2 = 5` by direct evaluation. The discarded intermediate formula gives `3^0 * 2^0 + 2^1 = 3` instead. Hence **5 ≠ 3**. It was a **false local proof step**, not an established lemma. The corrected local expression uses `3^1 * 2^0 + 2^1 = 5`. The history preserves the original text; no `Archive/` file was modified.

## Module05: current active mathematical frontier

Baseline [42730914791](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42730914791) diagnostics, classified by immediate cause, not assuming the mathematical statements true:

| Owner | Baseline line(s) | Root group | Proposed proof strategy | Status |
| --- | --- | --- | --- | --- |
| M05-FINITE | 155 | INFRASTRUCTURE / BLOCKED_UNCERTAIN | The exact decidable exhaustive certificate exceeded Lean recursion depth; increase `maxRecDepth` *locally*, never replace it by `True` or unchecked external evidence | CANDIDATE `bf6b3959`, CI pending |
| M05-DESC-BOUND | 341 | ROOT_INDEPENDENT | Isolate the arithmetic inequality `3^p - 2^p < 2^A - 3^p`, then transport it via length / exponent sum equations | CANDIDATE `9d39c9d5`, CI pending |
| M05-RECUR | 627 | ROOT_INDEPENDENT | Exact `calc` using induction hypothesis and separate products `3^(k+1)`, `2^(u+2(k+1))`; no nonlinear `linarith` leap | CANDIDATE `9d39c9d5`, CI pending |
| M05-WORD | 685, 687 | SAME_ROOT_SIBLING | Rewrite `A_total w` and `w.length` from the proved two-segment word formulas *before* applying `omega` | CANDIDATE `9d39c9d5`, CI pending |
| DOWNSTREAM | Module06–12, Support | LIKELY_CASCADE / BLOCKED_UNCERTAIN | Do not start independent mathematical patches until the import frontier passes | BLOCKED |

## Validation funnel — same one-frontier discipline as the prior 350k-line Lean project

1. Freeze exact source SHA + raw module logs; map all errors before proposing a patch.
2. One owner per root group. Use distinct branches only for genuinely different proof strategies; do not fan out identical speculative edits.
3. All patch commits are **CANDIDATE** until their own exact source compiles in GitHub Actions.
4. Promote a verified non-regressive checkpoint to the canonical research branch only after checking its full diff and expected branch HEAD (no force push).
5. Eventually run each Module01–12 + Support, `lake build GARCD`, clean builds twice, and independent `#print axioms`; then and only then revisit universal DESC.
6. Reject `sorry`, `admit`, new `axiom`, changing goal to `True`, silently weakening propositions, or deleting archived source.
7. `#check` is not a theorem proof. A green setup step is not compilation. A compiled local theorem is not a proof of Collatz, and an AI plan is not kernel evidence.

Status labels for mathematical claims: `PROVED / CORRECTED / NO-GO / CONDITIONAL / INTERFACE / TOY-PROXY / OPEN`. The overall DESC conjecture remains **OPEN**.

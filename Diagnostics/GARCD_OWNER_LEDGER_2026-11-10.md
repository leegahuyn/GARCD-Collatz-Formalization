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

## 2026-11-10 verified update — Module05 and Module06

This section supersedes the earlier `CANDIDATE` labels for the code changes, but preserves their historical diagnostics and the original proof targets.

- `GARCD.Module01`–`GARCD.Module05` **exit 0** at exact commit `a082bc2fd667796e1e14cb141c09e407900db991`, [Action 42732725399](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42732725399). Module06 had six errors at that point.
- `GARCD.Module01`–`GARCD.Module06` **exit 0** at exact commit `cc07f33e951b8d2e32c4cdce312ba9f158ccf233`, [Action 42734199413](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42734199413), first attempt. Module06 root groups: `M06-INV-ZMOD` (inverse product), `M06-ZMOD-FINITE` (3⁻¹=2 in ZMod 5, three residual concrete congruences), and `M06-SQ-H3` (three-term signed-sums factorization). No public theorem statement was weakened.
- **INFRASTRUCTURE / BLOCKED_UNCERTAIN:** That same Action terminated during `GARCD.Support` compilation after the runner received a shutdown signal, process exit **143**. The `Support` exit code was *not* recorded, and no raw artifact was uploaded on the interrupted attempt. This is **not** a Lean proof failure, and neither Support nor its dependents can be marked PASS.
- The original `GARCD/Support.lean` has 3608 lines and contains heavy kernel-decided finite certificates of 5,005; 19,448; 125,970; 497,420; 817,190; and 3,268,760 words. It is **possible**, but not yet proven, that resource pressure contributed to the runner interruption. Do not treat that hypothesis as a verified root cause.
- The user-specified orchestration contract remains: single active mathematical frontier, one root owner, no duplicate import errors, exact source SHA and actual Lean result above AI suggestions, only verified promotions. `Module07`–`Module12` remain `BLOCKED_UNCERTAIN` until Support is independently checked.
- Whole `lake build GARCD`, two clean builds, direct `#print axioms`, and the unconditional universal DESC target remain **NOT VERIFIED / OPEN**.

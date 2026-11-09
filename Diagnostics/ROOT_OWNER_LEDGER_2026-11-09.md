# GARCD Module02 root-owner ledger — 2026-11-09

## Evidence authority

- Canonical research branch: `research/modularize-2026-11-09`, last verified HEAD at ledger creation `a4d170ea2361ec6d3e8b79c77e1e969fb1ec45a5`.
- Candidate evidence baseline: `adfea6c848fea676e4f0559f091b3382dd7c6c4c`.
- Source of exact diagnostics: [Actions 42596030989](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42596030989), artifact `13663152889`, `logs/Module02.log`.
- Baseline: Module01 exit=0, Module02 exit=1. Module02 contains **10 diagnostic error rows**; counts below are diagnostic rows, not verified/false mathematical statements. Module03+ and Support logs reprint Module02 import failure and **must not** be counted as independent validated errors.
- Do **not** promote the Module02 code to the canonical branch until a direct, exact-commit successful build is recorded. Patches in this branch are only `CANDIDATE`.

## Single active mathematical frontier: Module02

| Owner ID | Exact baseline location(s) | Observed failure | Classification | Owner / planned proof strategy | Candidate status |
| --- | --- | --- | --- | --- | --- |
| M02-01 | 781 | `omega` cannot infer a nonlinear divisibility fact, although an explicit factor exists | ROOT_INDEPENDENT | Nat arithmetic owner; give witness for 2-divisibility and check with `ring` | proposed patch `eebdd632`, needs direct result |
| M02-02 | 1198, 1206 | `RealizesWord` mapped-`List.range` `getD` normalization not closed | ROOT_INDEPENDENT + SAME_ROOT_SIBLING | List API owner; rewrite `getD` to in-bounds `getElem` | proposed patch `eebdd632`, needs direct result |
| M02-03 | 1350 | Real quotient denominator rewrite pattern does not exist after simplification | ROOT_INDEPENDENT | Real algebra owner; explicit denominator identity plus nonzero hypotheses | OPEN |
| M02-04 | 1532 | `decide` cannot kernel-reduce `Nat.factorization` during finite examples | ROOT_INDEPENDENT | Finite computation owner; use exact valuation certificates, not unchecked evaluation | OPEN |
| M02-05 | 1755:36, 1755:46 | `omega` treats variable multiplication as opaque and cannot establish large residue witness | ROOT_INDEPENDENT + SAME_ROOT_SIBLING | Nat bound owner; provide `1 ≤ M` and monotone multiplication witnesses | OPEN |
| M02-06 | 1797 | Nat cast / ZMod power coercion goal left after `ring` | ROOT_INDEPENDENT | ZMod arithmetic owner; normalize coercions with exact Mathlib API | OPEN |
| M02-07 | 1805:30, 1805:86 | `2^A < 2^(A+1)` not inferred by linear arithmetic alone | ROOT_INDEPENDENT + SAME_ROOT_SIBLING | Nat exponent owner; use `pow_succ` and strict positivity | OPEN |
| M02-DOWNSTREAM | Module03–12, Support | repeated Module02 errors in each cumulative build | LIKELY_CASCADE / BLOCKED_UNCERTAIN | coordinator; inspect actual downstream independent errors only after Module02 passes | BLOCKED |
| INFRA-01 | Lean toolchain + Mathlib cache | setup succeeded in this run | INFRASTRUCTURE | no infrastructure blocker observed | PASS (setup only) |

These labels group **diagnostics** by immediate proof tactic and input, not by an unverified claim that the mathematics is true.

## Historical root-cause reductions (diagnostic rows, not theorem count)

- `aa49bf37` baseline: Module02 **29** diagnostics.
- `a4d170ea`: exported 12 already compiled `F_explicit_*` declarations; 0 unknown-id errors; Module02 still fails.
- `4f9d24a`: **24**.
- `2ddf3010`: **20**.
- `7e767a9`: **19**.
- `e6f736eb`: **14**.
- `adfea6c8`: **10**.
- Do not use counts from downstream logs as independent defects; those are import cascades.

## Coordinator protocol (A05–A10 / previous large-scale Lean formalization)

1. Freeze the exact `GITHUB_SHA`, the source file hash, and the complete action artifact.
2. Read **all** compiler errors and associate each to a declaration before patching. In an import failure, keep later uncompiled modules **BLOCKED_UNCERTAIN**, not PASS or independent failure.
3. Group by underlying cause: `ROOT_INDEPENDENT`, `SAME_ROOT_SIBLING`, `LIKELY_CASCADE`, `BLOCKED_UNCERTAIN`, `INFRASTRUCTURE`.
4. Allow **one mathematical frontier** and one owner per root group. Alternative proof strategies may use independent branches; do not apply conflicting patches in the same file concurrently.
5. Owner contract: precise proposition unchanged; affected declaration(s); minimal diff; expected error change; `lake build GARCD.Module02`; full raw log; commit SHA.
6. Compare source hashes and remaining root errors; promote a candidate to `GLOBAL_BEST` only on verified nonregression, never by AI agreement or `#check` alone. The checked-in canonical research branch remains independently tracked.
7. After Module02 PASS, repeat sequential module builds, `lake build GARCD`, two clean builds, independent `#print axioms`, and only then `Research/DESC_Open_Probe.lean`. Any failed stage is **FAIL/OPEN**.
8. No `sorry`, `admit`, new `axiom`, goal-to-`True` replacement, proposition weakening, or deletion of archived original source.

## Proof-status boundary

The universal DESC, A-0 and B-0 remain **OPEN**. No code candidate here proves the Collatz conjecture, and a failing-module compilation session does not certify declarations in that module.

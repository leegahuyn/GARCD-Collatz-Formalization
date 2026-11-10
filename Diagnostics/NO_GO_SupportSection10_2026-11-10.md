# SupportSection10 NO-GO and corrected positive-length equivalence — 2026-11-10

## Original exact-source counterexample

The original `GARCD/Support.lean`, later extracted verbatim into `GARCD/SupportSection10.lean`, contained
`wordsAsFixedCuts (A r : ℕ) (hA : 0 < A)` asserting an equivalence

`OriginalPositiveWord A r ≃ CutCode A r`

for **all** `r : ℕ`. This statement is false at `A=1, r=0`:

- `OriginalPositiveWord 1 0` consists of finite positive lists with length 0 and sum 1. It has no elements: a length-0 list is empty and sums to 0.
- `CutCode 1 0` is `{s : Finset (Fin 0) // s.card = 0 - 1}` in `Nat`. Since `0 - 1 = 0`, the empty set is a valid element.
- Therefore the first subtype is empty while the second is inhabited. No equivalence exists.

This is a **NO-GO false statement**, not a failing `omega` tactic.
Original repository SHA `17fbad528598efdb9c4b24718bab2917a16949bc` retains the unsound claimed declaration text.

## Corrected candidate, exact mathematical scope

Rename `wordsAsFixedCuts_pos`, require `hA:0<A` and `hr:0<r`. This is the valid domain of the fixed-length positive-composition/cut-code bijection, and it is exactly the domain used by the downstream public counting theorem `originalPositiveWord_card_choose (hA : 1 ≤ A) (hr : 1 ≤ r)`.

No conclusion is inferred for `r=0` from the corrected bijection. The public positive-domain count proposition is left unchanged. The corrected theorem and a new helper proving interior-cut cardinality are **CANDIDATE** pending exact SHA Lean kernel compilation.

The method compares boundary points including both endpoints with interior points; it uses `CompositionAsSet`'s existing equivalences in Mathlib and a finite `Finset.card_bij`.

## Other independent SupportSection10 failures

On CI run [42759298310](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42759298310) the six independent compiler errors were at lines 114, 156, 420/452, 478/498. Root groups:
- interior-cut-count proof missing
- false `r=0` domain in inverse
- Chernoff exponent let-normalization
- ENNReal finite-sum/coercion conversion.

All mathematical statements are preserved except the explicitly renamed and **corrected** false r=0 equivalence. No `sorry`, `admit`, new axiom, or `native_decide` has been added. Full `lake build GARCD`, two clean builds, and whole-repository axiom audit remain separate uncompleted gates.

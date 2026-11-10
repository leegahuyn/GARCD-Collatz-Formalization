# Support heavyweight kernel certificate isolation — 2026-11-10

## Purpose

One build root at a time. The original `GARCD/Support.lean` combines reusable analytic research with six heavyweight `decide +kernel` exact finite certificates (5005, 19448, 125970, 497420, 817190, 3268760 compositions). GitHub Actions repeatedly shut down the runner while compiling this combined file. No evidence of a Lean kernel error was observed; status remains INFRASTRUCTURE/BLOCKED_UNCERTAIN.

## No skipped theorem

The six full propositions and their original bodies are transferred verbatim into `GARCD/SupportFiniteCertificates.lean`. The conjunction `GARCD_31_all_eight_pairs_complete` is likewise preserved. They were not directly referenced elsewhere in the original `Support.lean` or other module imports. The source `Support.lean` retains all other declarations (including `GARCD_31_small_odd_numbers_reach_one` and the later Hausdorff work).

Critically, the aggregate `GARCD.lean` now imports **both** `GARCD.Module12` and `GARCD.SupportFiniteCertificates`, so `lake build GARCD` **cannot** silently omit expensive exact certificates.

The diagnostic script runs `Module01..10`, then `Support`, then `Module11..12`, and separately `SupportFiniteCertificates`, giving the heavy module a 70-second **diagnostic-only** timebox. Timeout code 124 is **not proof failure nor PASS**; a final full build must succeed without a timeout.

This is a source-preserving structural dependency isolation, not a mathematical theorem edit; no new axiom, sorry, admit, native_decide or relaxed statement is introduced. Original is retrievable from parent SHA `a3e540d669f6f51d390c35f69f2bad6feb43c4a1` and Archive is untouched.

# Support P16 certificate extraction and Module11 imports — 2026-11-10

**Reason:** [CI 42745150402](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42745150402) confirms 01–10 PASS, 70s Support TIMEOUT 124, 70s finite certificate TIMEOUT124, and Module11 failures include undeclared names (e.g. `ChernoffX`, `ActualGeometricEnvelopeGoal`) that originate in Support. Its original only-import Module10 did not expose them. This is a missing-import root, not eighty independent proof failures.

Exact block `GARCD_P16_Analytic_Research` from Support, including `GARCD_31_small_odd_numbers_reach_one` (2048 odd numbers, 88 iterates, `decide +kernel`) and `GARCD_31_All_Admissible_Words_p_le_16_No_Cycle`, is preserved verbatim in `GARCD/SupportP16Certificates.lean`. It imports `GARCD.Support` for its earlier finite admissible table. Nothing outside the block in Support refers to its private or public symbols.

The top-level `GARCD.lean` now imports `GARCD.Module12`, `GARCD.SupportFiniteCertificates`, **and** `GARCD.SupportP16Certificates`. No certificate is omitted from actual full `lake build GARCD`. Diagnostic script tests Module11/12 after Support and tests the two heavyweight certificate files separately with a 70-second timeout each. No timeouts apply to the full root build or axiom audit; code 124 means BLOCKED_UNCERTAIN.

`Module11.lean` gains explicit `import GARCD.Support` to expose its real declaration dependencies. Any additional proof failures require separate owner review. Source proof goals and statements unchanged. No sorry/admit/axiom or native_decide introduced. Original source retained via Git history at `c6a7f21c8c9cb0e8e2085dcb45f7874880e4903e`.

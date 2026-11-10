# Heavy finite certificates: exact split without dropping any proof — 2026-11-10

Parent exact SHA `9437fa3cfdfaa0df158801c630a03b5394ff0c12`. The direct full-file [Actions run 42761193692](https://github.com/leegahuyn/GARCD-Collatz-Formalization/actions/runs/42761193692) compiled Module01–06 and then ended with GitHub runner shutdown signal / process 143 before `SupportFiniteCertificates` completed; this is INFRASTRUCTURE/BLOCKED_UNCERTAIN, not a kernel error.

The original six `theorem GARCD_31_p{10,11,13,14,15,16}_A{16,18,21,23,24,26}_complete` declarations and their `decide +kernel` proof bodies were copied **verbatim** into six independently compilable files `SupportCert10`, `SupportCert11`, `SupportCert13`, `SupportCert14`, `SupportCert15`, `SupportCert16`. Each imports the original `Module06` and sets `maxHeartbeats 0` as in the original.

The aggregate `SupportFiniteCertificates.lean` now imports all six modules and contains the original full 4,734,620-case conjunction theorem unchanged. The top-level `GARCD.lean` still imports that aggregate transitively; no certificate is omitted, weakened or replaced by `native_decide`, sorry, admit or axiom.

The companion direct workflow compiles every separated theorem with full kernel verification and prints the exact axioms only if all seven pass. GitHub job cap is 45 minutes, diagnostics capture errors or runner shutdown distinctly.

**Status:** candidate until actual Lean PASS on all files, full root build, two clean builds, and repository-wide axiom audit.

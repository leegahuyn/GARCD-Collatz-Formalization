# Staged Support original-source compilation — 2026-11-10

Source baseline `dc8a94418b05b92f79af2173c1103e3ceacbd052`; all original Support declarations and theorem proofs are retained verbatim in their original order, partitioned at 11 exact top-level `end GARCD` boundaries. Each new unit imports its direct predecessor and opens the same global namespaces as the original file. The original `GARCD.Support` is an aggregator importing `GARCD.SupportSection10`; its trailing documentation is retained. Original source is preserved in the parent commit.

`Scripts/verify.sh` now builds SupportPrelude then Section01..10 individually, before Support and the dependent Module11/12. The full `GARCD.lean` root import tree still contains both P16 and heavyweight finite full certificates, each timeboxed to 70s in diagnostic script only; actual `lake build GARCD` must recheck everything.

This structural candidate does not claim Lean PASS, does not bypass any theorem, introduces no sorry/admit/axioms, and does not turn `native_decide` on. It is designed to identify independent errors and reduce compile-memory peaks.

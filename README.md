# GARCD — Collatz Formalization Research

**UNVERIFIED CANDIDATE.** This repository does not claim a complete kernel-certified formalization or a proof of the Collatz conjecture.

## Single source of truth
Original source preserved at `Archive/GARCD_Modules_1_12_Repair_v1_REISSUED.lean`.
SHA-256: `25a2e863e1cb8d0677d7016c38c57c455cc695c83fa2a35afd8e46bc90fd2cb4`

Module 01–12 plus `Support.lean` are exact consecutive source chunks with necessary Lean module import/scope wrappers only.

## Build
```sh
lake update
lake exe cache get
bash Scripts/verify.sh
lake build GARCD
bash Scripts/axiom-audit.sh
```

Research/DESC_Open_Probe.lean is **deliberately outside** the library build: the full DESC conjecture is not proved.

## Research verification policy
1. First collect the complete diagnostic landscape.
2. Group repeated errors by root cause (namespace/import/API/type/proof gap).
3. Keep only one authoritative patched source; one owner per error root.
4. Promote a fix only after exact-source compilation improves and does not regress.
5. An AI proposal or green-looking workflow output is not proof. Verify Lean kernel results and `#print axioms` after a clean build.
6. Record claim statuses separately: PROVED, CORRECTED, NO-GO, CONDITIONAL, INTERFACE, TOY/PROXY, OPEN.

Pinned upstream toolchain: `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`.

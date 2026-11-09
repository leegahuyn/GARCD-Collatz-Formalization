#!/usr/bin/env bash
set -euo pipefail
lake build GARCD
lake env lean Audit/AxiomAudit.lean | tee Diagnostics/Axioms.stdout.txt
if grep -E 'sorryAx|unsound' Diagnostics/Axioms.stdout.txt; then
  echo 'WARNING: review detected axioms'; exit 1
fi

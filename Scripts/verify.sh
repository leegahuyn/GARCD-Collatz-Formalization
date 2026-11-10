#!/usr/bin/env bash
set -uo pipefail
mkdir -p Diagnostics/logs
printf 'module\texit_code\tbytes\n' > Diagnostics/MODULE_RESULTS.tsv
modules=(Module01 Module02 Module03 Module04 Module05 Module06 Module07 Module08 Module09 Module10 Support Module11 Module12)
failed=0
for m in "${modules[@]}"; do
  echo "::group::GARCD.$m"
  if [ "$m" = "Support" ]; then
    # Diagnostic time-box only: Support contains millions of exact decidable checks.
    # A timeout is NOT PASS. Capture code 124 instead of losing all module logs to runner shutdown.
    timeout --signal=TERM --kill-after=10s 70s lake build "GARCD.$m" > "Diagnostics/logs/${m}.log" 2>&1
  else
    lake build "GARCD.$m" > "Diagnostics/logs/${m}.log" 2>&1
  fi
  code=$?
  if [ "$code" -eq 124 ]; then echo "Module $m TIMEOUT (INFRASTRUCTURE, not proof failure)"; fi
  printf '%s\t%s\t%s\n' "$m" "$code" "$(wc -c < "Diagnostics/logs/${m}.log")" >> Diagnostics/MODULE_RESULTS.tsv
  echo "Module $m exit=$code"
  grep -E 'error:|unsolved goals|unknown identifier|failed|panic|sorry' "Diagnostics/logs/${m}.log" | head -30 || true
  echo "::endgroup::"
  if [ "$code" -ne 0 ]; then failed=1; fi
done
exit "$failed"

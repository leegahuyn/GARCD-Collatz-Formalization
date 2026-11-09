#!/usr/bin/env bash
set -uo pipefail
mkdir -p Diagnostics/logs
printf 'module\texit_code\tbytes\n' > Diagnostics/MODULE_RESULTS.tsv
modules=(Module01 Module02 Module03 Module04 Module05 Module06 Support Module07 Module08 Module09 Module10 Module11 Module12)
failed=0
for m in "${modules[@]}"; do
  echo "::group::GARCD.$m"
  lake build "GARCD.$m" > "Diagnostics/logs/${m}.log" 2>&1
  code=$?
  printf '%s\t%s\t%s\n' "$m" "$code" "$(wc -c < "Diagnostics/logs/${m}.log")" >> Diagnostics/MODULE_RESULTS.tsv
  echo "Module $m exit=$code"
  grep -E 'error:|unsolved goals|unknown identifier|failed|panic|sorry' "Diagnostics/logs/${m}.log" | head -30 || true
  echo "::endgroup::"
  if [ "$code" -ne 0 ]; then failed=1; fi
done
exit "$failed"

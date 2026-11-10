#!/usr/bin/env bash
set -uo pipefail
mkdir -p Diagnostics/logs
printf 'module\texit_code\tbytes\n' > Diagnostics/MODULE_RESULTS.tsv
# Focused repair frontier: Module01--10 already compiled with exit=0
# on canonical exact source a3e540d669f6f51d390c35f69f2bad6feb43c4a1.
# Their imports are recompiled transitively; complete lake build GARCD is still required.
modules=(SupportPrelude SupportSection01 SupportSection02 SupportSection03 SupportSection04 SupportSection05 SupportSection06 SupportSection07 SupportSection08 SupportSection09 SupportSection10 Support Module11 Module12 SupportP16Certificates SupportFiniteCertificates)
failed=0
for m in "${modules[@]}"; do
  echo "::group::GARCD.$m"
  if [ "$m" = "SupportP16Certificates" ] || [ "$m" = "SupportFiniteCertificates" ]; then
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
  if [ "$code" -ne 0 ]; then
    failed=1
    case "$m" in
      SupportPrelude|SupportSection[0-9][0-9])
        echo "DEPENDENCY_BLOCK: downstream Support sections, Module11/12, and root build not independently checked."
        echo "The exact first failed source and log above are the active mathematical frontier."
        break
        ;;
    esac
  fi
done
exit "$failed"

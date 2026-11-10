import GARCD
import Lean

/-!
# Whole GARCD namespace axiom audit

This checks all imported declarations in the GARCD namespace, not just
a manually selected list of major theorems. A declaration using any axiom
besides Lean's ordinary propext, Classical.choice, and Quot.sound causes
an error. It does not prove the universal DESC statement.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.filter fun x =>
    Name.isPrefixOf `GARCD x.1).map Prod.fst
  let mut checked : Nat := 0
  let mut failCount : Nat := 0
  for name in names do
    let axs ← collectAxioms name
    let unexpected := axs.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    checked := checked + 1
    if !unexpected.isEmpty then
      failCount := failCount + 1
      logError m!"UNEXPECTED AXIOMS {name}: {unexpected.toList}"
  logInfo m!"GARCD WHOLE_NAMESPACE_AUDIT checked={checked}, unexpected={failCount}"
  if checked == 0 then
    throwError "GARCD namespace unexpectedly has no declarations"
  if failCount != 0 then
    throwError "GARCD whole-namespace axiom audit failed"

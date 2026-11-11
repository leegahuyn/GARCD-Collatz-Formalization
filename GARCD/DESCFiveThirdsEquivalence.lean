import GARCD.DESCRationalDriftBarrier

/-!
# Exact equivalence: eventual five-thirds valuation drift ↔ Collatz

The OPEN proposition `GlobalFiveThirdsDriftGoal`, defined in
`GARCD.DESCMeanFiveThirds`, requires for each odd n >= 7 a finite
prefix r with 3*A_orbit n r >= 5*r.

The implication from this condition to the full Collatz conjecture
was already kernel-verified. This module establishes the converse
unconditionally: if the standard Collatz conjecture holds, every
odd orbit eventually reaches 1, so all later exponents are 2.

Given an explicit Syracuse hitting time R, the choice
    r = R + (5*R + 1) = 6*R + 1
satisfies
    3*A_orbit n r - 5*r = 3*A_orbit n R + 1 > 0.

Thus the global drift property is provably EQUIVALENT to Collatz.
This file does NOT prove either side without an assumption.
-/

namespace GARCD

/-- A finite accelerated orbit witness F^[R](n) = 1 constructively
gives a supercritical valuation prefix by time 6*R + 1. -/
theorem reaches_one_yields_five_thirds_drift_certificate
    {n R : ℕ} (hR : x_seq n R = 1) :
    ∃ r : ℕ, 1 ≤ r ∧
      5 * r ≤ 3 * A_orbit n r := by
  let k : ℕ := 5 * R + 1
  refine ⟨R + k, by dsimp [k]; omega, ?_⟩
  have hA : A_orbit n (R + k) =
      A_orbit n R + 2 * k :=
    (x_seq_add_of_eq_one hR k).2.2
  dsimp [k] at *
  omega

/-- Reverse implication; uses the already kernel-checked
equivalence between standard Collatz and Syracuse convergence.
This is NOT an unconditional proof of Collatz. -/
theorem Collatz_implies_GlobalFiveThirdsDriftGoal :
    CollatzConjectureProp → GlobalFiveThirdsDriftGoal := by
  intro hcollatz n hodd hn
  have hreach : ReachesOneSyracuse n :=
    (Syracuse_Convergence_Iff_CollatzConjectureProp.mpr hcollatz)
      n hodd
  obtain ⟨R, hR⟩ := hreach
  exact reaches_one_yields_five_thirds_drift_certificate hR

/-- The exact mathematical status of the open global drift
condition. It is EQUIVALENT to the full Collatz conjecture.
An equivalence proof does NOT prove its terms. -/
theorem GlobalFiveThirdsDriftGoal_iff_Collatz :
    GlobalFiveThirdsDriftGoal ↔ CollatzConjectureProp := by
  constructor
  · exact GlobalFiveThirdsDriftGoal_implies_Collatz
  · exact Collatz_implies_GlobalFiveThirdsDriftGoal

/-- This open global valuation condition also carries precisely
the difficulty of the original thirteen unresolved odd
residue classes modulo 128, via already validated equivalences. -/
theorem GlobalFiveThirdsDriftGoal_iff_RemainingDESC13 :
    GlobalFiveThirdsDriftGoal ↔ RemainingDESC13Mod128Goal := by
  exact GlobalFiveThirdsDriftGoal_iff_Collatz.trans
    RemainingDESC13Mod128Goal_iff_Collatz.symm

end GARCD

#print axioms GARCD.reaches_one_yields_five_thirds_drift_certificate
#print axioms GARCD.Collatz_implies_GlobalFiveThirdsDriftGoal
#print axioms GARCD.GlobalFiveThirdsDriftGoal_iff_Collatz
#print axioms GARCD.GlobalFiveThirdsDriftGoal_iff_RemainingDESC13

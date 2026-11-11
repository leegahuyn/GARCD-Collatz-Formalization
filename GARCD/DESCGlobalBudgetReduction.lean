import GARCD.DESCValuationBarrier

/-!
# Quantitative global valuation-surplus reduction

The still-OPEN claim that all odd n >= 3 eventually attain a
supercritical cumulative valuation is sufficient for Collatz.

This module PROVES ONLY the implication from the explicit hypothesis
to the full conjecture, and the necessary obstruction to an
individual orbit that never descends. It does not prove the
hypothesis itself.

No sorry, admit, axiom or hidden universal descent assumption.
-/

namespace GARCD

/-- Exact quantitative global surplus hypothesis (OPEN). -/
def GlobalValuationSurplusGoal : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
    ∃ r : ℕ, (3 * n + 1) ^ r <
      n ^ r * 2 ^ A_orbit n r

/-- If the explicit global valuation-surplus condition is ever proved,
then GARCD's original Collatz conjecture is fully established.
This theorem DOES NOT assert GlobalValuationSurplusGoal. -/
theorem GlobalValuationSurplusGoal_implies_Collatz :
    GlobalValuationSurplusGoal → CollatzConjectureProp := by
  intro hsurplus
  have hall : DESCArithmeticProp := by
    intro n hodd hn
    obtain ⟨r, hbig⟩ := hsurplus n hodd hn
    obtain ⟨j, hjpos, _, hdesc⟩ :=
      valuation_threshold_forces_DESC n r (by omega) hbig
    exact ⟨j, hjpos, hdesc⟩
  exact (DESCArithmeticProp_iff_remaining_thirteen_mod128.trans
    RemainingDESC13Mod128Goal_iff_Collatz).mp hall

/-- If the orbit of a positive starting value never drops below
its start, every finite prefix must obey the explicit valuation
barrier; such an orbit can never exhibit a supercritical prefix. -/
theorem eternally_non_descent_obeys_valuation_barrier
    (n : ℕ) (hn : 0 < n)
    (hno : ∀ r : ℕ, n ≤ x_seq n r) :
    ∀ r : ℕ, n ^ r * 2 ^ A_orbit n r ≤ (3 * n + 1) ^ r := by
  intro r
  exact no_descent_valuation_barrier n r hn
    (by intro j hj; exact hno j)

end GARCD

#print axioms GARCD.GlobalValuationSurplusGoal_implies_Collatz
#print axioms GARCD.eternally_non_descent_obeys_valuation_barrier

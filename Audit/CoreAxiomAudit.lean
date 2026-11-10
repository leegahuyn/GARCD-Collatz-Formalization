/-!
Independent core-proposition kernel audit.

This file imports the fully compiled Module12 without importing the two very
large optional finite certificate files from the root GARCD target.

IMPORTANT: The universal DESC is only defined and proved EQUIVALENT to the
Collatz conjecture here. This does not prove universal DESC unconditionally.
-/
import GARCD.Module12

namespace GARCD

/-- The exact unconditional, universally quantified arithmetic DESC assertion.
    Declaring it as a Prop does not establish that it is true. -/
def UniversalDESCGoal : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ)

/-- Formal equivalence only: proving this goal would settle Collatz. -/
theorem UniversalDESCGoal_iff_CollatzConjectureProp :
    UniversalDESCGoal ↔ CollatzConjectureProp := by
  change DESCArithmeticProp ↔ CollatzConjectureProp
  exact Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality.symm.trans
    Theorem_10_2_2_DESC_Iff_Collatz_Conjecture

end GARCD

#print axioms GARCD.Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality
#print axioms GARCD.Theorem_10_2_2_DESC_Iff_Collatz_Conjecture
#print axioms GARCD.Theorem_12_2_4_Manuscript_A0_And_B0_Log2_3_Iff_Collatz_Conjecture
#print axioms GARCD.GARCD_Complete_Unconditional_Equivalences_And_Regimes
#print axioms GARCD.UniversalDESCGoal_iff_CollatzConjectureProp

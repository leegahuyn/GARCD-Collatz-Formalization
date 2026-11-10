import GARCD.Module12

/-!
Independent core-proposition kernel audit.

This file imports the fully compiled Module12 without importing the two very
large optional finite certificate files from the root GARCD target.

IMPORTANT: The universal DESC is only defined and proved EQUIVALENT to the
Collatz conjecture here. This does not prove universal DESC unconditionally.
-/

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

/-- Unconditional arithmetic DESC on two explicitly verified infinite residue classes.
    This is only a proper SUBSET of the universal odd inputs, not the open full goal. -/
theorem UniversalDESCGoal_mod4_mod16_partial
    (n : ℕ) (hn : 3 ≤ n) (hclass : n % 4 = 1 ∨ n % 16 = 3) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by
  obtain ⟨h4, h16⟩ := Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn
  rcases hclass with hmod4 | hmod16
  · refine ⟨1, by omega, ?_⟩
    exact (GARCD_4_2_Exact_Descent_Iff n 1).mp (h4 hmod4)
  · refine ⟨2, by omega, ?_⟩
    exact (GARCD_4_2_Exact_Descent_Iff n 2).mp (h16 hmod16)


/-- The EXACT remaining universal DESC obligation after the already proved
five odd residue classes modulo 16. This proposition is not asserted true. -/
def RemainingDESCMod16Goal : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) →
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ)

/-- Universal DESC holds exactly when the three still-uncovered odd residue
classes modulo 16 satisfy DESC. This is a reduction, not a proof of either side. -/
theorem UniversalDESCGoal_iff_remaining_three_mod16 :
    UniversalDESCGoal ↔ RemainingDESCMod16Goal := by
  constructor
  · intro h n hn _
    have hodd : n % 2 = 1 := by omega
    exact h n hodd hn
  · intro h n hodd hn
    by_cases hdone : n % 4 = 1 ∨ n % 16 = 3
    · exact UniversalDESCGoal_mod4_mod16_partial n hn hdone
    · have hrest : n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by
        omega
      exact h n hn hrest

end GARCD

#print axioms GARCD.Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality
#print axioms GARCD.Theorem_10_2_2_DESC_Iff_Collatz_Conjecture
#print axioms GARCD.Theorem_12_2_4_Manuscript_A0_And_B0_Log2_3_Iff_Collatz_Conjecture
#print axioms GARCD.GARCD_Complete_Unconditional_Equivalences_And_Regimes
#print axioms GARCD.UniversalDESCGoal_iff_CollatzConjectureProp
#print axioms GARCD.Theorem_12_5_3_Exact_Invariant_Mod_Sieve_Certificate
#print axioms GARCD.UniversalDESCGoal_mod4_mod16_partial
#print axioms GARCD.UniversalDESCGoal_iff_remaining_three_mod16

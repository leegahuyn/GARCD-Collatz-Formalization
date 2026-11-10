import GARCD.Module06
import Mathlib.Topology.MetricSpace.HausdorffDimension

open scoped BigOperators
open Finset Real Filter






/-! ===== Source: GARCD_Bounds_4096_Research.lean ===== -/

/-!

An alternative, MUCH SMALLER intended proof architecture for p <= 16.

This file records sound proof TARGETS and kernel-decidable computations.

The bridge from word bounds to universal non-divisibility is not yet formalized.

-/



namespace GARCD



/-- Boolean certificate for every natural input n=1,...,4096:

    all have reached 1 by 90 accelerated odd Syracuse steps.

    Do not mistake `#eval` below for a kernel proof. -/

def GARCD_small_F_orbits_4096 : Bool :=

  (List.range 4096).all (fun j => x_seq (j + 1) 90 == 1)



-- Can be tested by executing `#eval GARCD_small_F_orbits_4096`.

-- If evaluation succeeds, the following theorem is a precise kernel-proof target:

-- theorem GARCD_small_F_orbits_4096_certified :

--     GARCD_small_F_orbits_4096 = true := by decide +kernel



/-- The eight numerator-denominator comparisons. The least upper bound on

    a potential period element from the general correction estimate is <4096. -/

theorem GARCD_31_numeric_cycle_upper_bounds :

    (∀ p A : ℕ,

      (p = 5 ∧ A = 8) ∨ (p = 8 ∧ A = 13) ∨

      (p = 10 ∧ A = 16) ∨ (p = 11 ∧ A = 18) ∨

      (p = 13 ∧ A = 21) ∨ (p = 14 ∧ A = 23) ∨

      (p = 15 ∧ A = 24) ∨ (p = 16 ∧ A = 26) →

      2 ^ A * (3 ^ p - 2 ^ p) <

        4096 * 2 ^ p * (2 ^ A - 3 ^ p)) := by

  intro p A h

  rcases h with h | h | h | h | h | h | h | h

  all_goals rcases h with ⟨rfl, rfl⟩ <;> norm_num



/-- Exact admissible pairs for p in [1,16], A in [1,26], finite and

    independent of the 4,734,620 candidate words. -/

theorem GARCD_31_full_admissible_pairs_finite_table :

    ∀ p ∈ Finset.Icc 1 16, ∀ A ∈ Finset.Icc 1 26,

      (3 ^ p < 2 ^ A ∧ 7 ^ p * 2 ^ A ≤ 22 ^ p) →

        ((p = 5 ∧ A = 8) ∨ (p = 8 ∧ A = 13) ∨

         (p = 10 ∧ A = 16) ∨ (p = 11 ∧ A = 18) ∨

         (p = 13 ∧ A = 21) ∨ (p = 14 ∧ A = 23) ∨

         (p = 15 ∧ A = 24) ∨ (p = 16 ∧ A = 26)) := by

  decide +kernel



end GARCD

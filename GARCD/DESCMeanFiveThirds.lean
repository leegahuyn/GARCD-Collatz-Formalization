import GARCD.DESCUniformSevenFourths

/-!
# Stronger 5/3 valuation barrier and a necessary frequency of v₂ = 1

For odd n >= 7, any finite non-descending Syracuse prefix has
mean valuation < 5/3, and must contain strictly more than one-third
single-halving (valuation-one) steps.

These are certified necessary conditions on a hypothetical counterexample,
NOT proof that a descending step eventually exists.

For n >= 7: (3*n+1)^3 < 32*n^3, since 22^3 = 10648 < 32*343 = 10976.
-/

namespace GARCD

private theorem strict_cube_power_gap (n : ℕ) (hn : 7 ≤ n) :
    (3 * n + 1) ^ 3 < 32 * n ^ 3 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 7 := ⟨n - 7, by omega⟩
  rw [hk]
  nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2)]

/-- Necessary 5/3 valuation-budget barrier for an orbit prefix which
never goes below its positive starting value. -/
theorem no_descent_forces_mean_valuation_below_five_thirds
    (n r : ℕ) (hn : 7 ≤ n) (hr : 1 ≤ r)
    (hno : ∀ j : ℕ, j ≤ r → n ≤ x_seq n j) :
    3 * A_orbit n r < 5 * r := by
  have hbar := no_descent_valuation_barrier n r (by omega) hno
  have hbase := strict_cube_power_gap n hn
  have hstrictpow :
      ((3 * n + 1) ^ 3) ^ r < (32 * n ^ 3) ^ r := by
    gcongr <;> assumption <;> omega
  have hstrict : ((3 * n + 1) ^ r) ^ 3 <
      (n ^ r) ^ 3 * 2 ^ (5 * r) := by
    calc
      ((3 * n + 1) ^ r) ^ 3 = ((3 * n + 1) ^ 3) ^ r := by
        simp only [← pow_mul, mul_comm]
      _ < (32 * n ^ 3) ^ r := hstrictpow
      _ = (n ^ r) ^ 3 * 2 ^ (5 * r) := by
        rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
        simp only [mul_pow, ← pow_mul, mul_comm]
  by_contra hnot
  have hlarge : 5 * r ≤ 3 * A_orbit n r := by omega
  have hpow : 2 ^ (5 * r) ≤ 2 ^ (3 * A_orbit n r) :=
    Nat.pow_le_pow_right (by omega) hlarge
  have hleft : (n ^ r) ^ 3 * 2 ^ (5 * r) ≤
      (n ^ r * 2 ^ A_orbit n r) ^ 3 := by
    calc
      (n ^ r) ^ 3 * 2 ^ (5 * r) ≤
          (n ^ r) ^ 3 * 2 ^ (3 * A_orbit n r) :=
            Nat.mul_le_mul_left _ hpow
      _ = (n ^ r * 2 ^ A_orbit n r) ^ 3 := by
        simp only [mul_pow, ← pow_mul, mul_comm]
  have hbar3 : (n ^ r * 2 ^ A_orbit n r) ^ 3 ≤
      ((3 * n + 1) ^ r) ^ 3 := by
    gcongr <;> assumption
  omega

/-- A prefix valuation mean >= 5/3 forces at least one strict descent
at a step j <= r, for every n >= 7. -/
theorem mean_valuation_five_thirds_forces_descent
    (n r : ℕ) (hn : 7 ≤ n) (hr : 1 ≤ r)
    (hlarge : 5 * r ≤ 3 * A_orbit n r) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ x_seq n j < n := by
  by_contra h
  have hno : ∀ j, j ≤ r → n ≤ x_seq n j := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0, x_seq]
    · have hjpos : 1 ≤ j := by omega
      have hnot : ¬ x_seq n j < n := by
        intro hdrop
        exact h ⟨j, hjpos, hj, hdrop⟩
      omega
  have hsmall :=
    no_descent_forces_mean_valuation_below_five_thirds
      n r hn hr hno
  omega

/-- GARCD exact arithmetic DESC certificate from the 5/3 threshold. -/
theorem mean_valuation_five_thirds_forces_DESC
    (n r : ℕ) (hn : 7 ≤ n) (hr : 1 ≤ r)
    (hlarge : 5 * r ≤ 3 * A_orbit n r) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧
      (C_orbit n j : ℤ) <
        ((2 : ℤ) ^ A_orbit n j - (3 : ℤ) ^ j) * (n : ℤ) := by
  obtain ⟨j, hjpos, hjr, hdrop⟩ :=
    mean_valuation_five_thirds_forces_descent n r hn hr hlarge
  exact ⟨j, hjpos, hjr,
    (GARCD_4_2_Exact_Descent_Iff n j).mp hdrop⟩

/-- The number of initial r steps having exactly one division by two. -/
def valuation_one_count (n r : ℕ) : ℕ :=
  (Finset.range r).sum (fun j => if a_seq n j = 1 then 1 else 0)

/-- For every odd n, each exponent is >= 1. Thus the number of
valuation-one steps controls the total valuation budget. -/
theorem one_count_budget (n r : ℕ) (hodd : n % 2 = 1) :
    2 * r ≤ A_orbit n r + valuation_one_count n r := by
  have hsum :
      (Finset.range r).sum (fun _ => (2 : ℕ)) ≤
        (Finset.range r).sum (fun j =>
          a_seq n j + (if a_seq n j = 1 then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hge := a_seq_ge_one hodd j
    split_ifs with heq <;> omega
  simpa [A_orbit, valuation_one_count, Finset.sum_add_distrib,
    Nat.mul_comm] using hsum

/-- Every hypothetical non-descending odd orbit starting at n >= 7
must use valuation-one steps more often than one-third of the time,
for EVERY finite prefix r >= 1. -/
theorem no_descent_forces_one_count_above_one_third
    (n r : ℕ) (hn : 7 ≤ n) (hodd : n % 2 = 1) (hr : 1 ≤ r)
    (hno : ∀ j : ℕ, j ≤ r → n ≤ x_seq n j) :
    r < 3 * valuation_one_count n r := by
  have hmean :=
    no_descent_forces_mean_valuation_below_five_thirds
      n r hn hr hno
  have hcount := one_count_budget n r hodd
  omega

/-- OPEN global hypothesis. Any proof that EVERY odd n >= 7
eventually attains cumulative valuation >= 5r/3 would resolve
the Collatz conjecture; it is not asserted here. -/
def GlobalFiveThirdsDriftGoal : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 7 ≤ n →
    ∃ r : ℕ, 1 ≤ r ∧ 5 * r ≤ 3 * A_orbit n r

/-- Conditional implication; the hypothesis is NOT proved.
For n = 3 or n = 5, GARCD's existing mod-4 theorem covers descent.
-/
theorem GlobalFiveThirdsDriftGoal_implies_Collatz :
    GlobalFiveThirdsDriftGoal → CollatzConjectureProp := by
  intro hall
  have hDESC : DESCArithmeticProp := by
    intro n hodd hn
    by_cases h7 : 7 ≤ n
    · obtain ⟨r, hr, hlarge⟩ := hall n hodd h7
      obtain ⟨j, hjpos, _, hineq⟩ :=
        mean_valuation_five_thirds_forces_DESC n r h7 hr hlarge
      exact ⟨j, hjpos, hineq⟩
    · have h4 : n % 4 = 1 ∨ n % 16 = 3 := by omega
      rcases h4 with hmod4 | hmod16
      · refine ⟨1, by omega, ?_⟩
        exact (GARCD_4_2_Exact_Descent_Iff n 1).mp
          ((Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn).1 hmod4)
      · refine ⟨2, by omega, ?_⟩
        exact (GARCD_4_2_Exact_Descent_Iff n 2).mp
          ((Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn).2 hmod16)
  exact (DESCArithmeticProp_iff_remaining_thirteen_mod128.trans
    RemainingDESC13Mod128Goal_iff_Collatz).mp hDESC

end GARCD

#print axioms GARCD.no_descent_forces_mean_valuation_below_five_thirds
#print axioms GARCD.mean_valuation_five_thirds_forces_descent
#print axioms GARCD.mean_valuation_five_thirds_forces_DESC
#print axioms GARCD.one_count_budget
#print axioms GARCD.no_descent_forces_one_count_above_one_third
#print axioms GARCD.GlobalFiveThirdsDriftGoal_implies_Collatz

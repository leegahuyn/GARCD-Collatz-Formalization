import GARCD.DESCGlobalBudgetReduction

/-!
# Uniform (7/4)-valuation obstruction for non-descending odd orbits

If n >= 3 and no accelerated step through r >= 1 dips below n,
the average 2-adic valuation of that prefix is < 7/4.

This is an elementary explicit *necessary condition* on any
hypothetical non-descending orbit, not a proof that every orbit
eventually achieves average valuation >= 7/4.

The numerical constant is valid because (10/3)^4 < 2^7.
-/

namespace GARCD

private theorem strict_fourth_power_gap (n : ℕ) (hn : 3 ≤ n) :
    (3 * n + 1) ^ 4 < 128 * n ^ 4 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  rw [hk]
  nlinarith [Nat.zero_le (k ^ 4), Nat.zero_le (k ^ 3),
    Nat.zero_le (k ^ 2)]

/-- A hypothetical orbit staying >= n through time r >= 1 has
cumulative valuation strictly less than (7/4) * r. -/
theorem no_descent_forces_mean_valuation_below_seven_fourths
    (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hno : ∀ j, j ≤ r → n ≤ x_seq n j) :
    4 * A_orbit n r < 7 * r := by
  have hbar := no_descent_valuation_barrier n r (by omega) hno
  have hbase := strict_fourth_power_gap n hn
  have hstrictpow :
      ((3 * n + 1) ^ 4) ^ r < (128 * n ^ 4) ^ r := by
    gcongr <;> assumption <;> omega
  have hstrict : ((3 * n + 1) ^ r) ^ 4 <
      (n ^ r) ^ 4 * 2 ^ (7 * r) := by
    calc
      ((3 * n + 1) ^ r) ^ 4 = ((3 * n + 1) ^ 4) ^ r := by
        simp [pow_mul, mul_comm]
      _ < (128 * n ^ 4) ^ r := hstrictpow
      _ = (n ^ r) ^ 4 * 2 ^ (7 * r) := by
        rw [show (128 : ℕ) = 2 ^ 7 by norm_num]
        simp [mul_pow, pow_mul, mul_comm, mul_left_comm, mul_assoc]
  by_contra hnot
  have hlarge : 7 * r ≤ 4 * A_orbit n r := by omega
  have hpow : 2 ^ (7 * r) ≤ 2 ^ (4 * A_orbit n r) :=
    Nat.pow_le_pow_right (by omega) hlarge
  have hleft : (n ^ r) ^ 4 * 2 ^ (7 * r) ≤
      (n ^ r * 2 ^ A_orbit n r) ^ 4 := by
    calc
      (n ^ r) ^ 4 * 2 ^ (7 * r) ≤
          (n ^ r) ^ 4 * 2 ^ (4 * A_orbit n r) :=
            Nat.mul_le_mul_left _ hpow
      _ = (n ^ r * 2 ^ A_orbit n r) ^ 4 := by
        simp [mul_pow, pow_mul, mul_comm, mul_left_comm, mul_assoc]
  have hbar4 : (n ^ r * 2 ^ A_orbit n r) ^ 4 ≤
      ((3 * n + 1) ^ r) ^ 4 := by
    gcongr <;> assumption
  omega

/-- Reaching an average valuation at least 7/4 at any finite
prefix is a sufficient condition for some strict descent. -/
theorem mean_valuation_seven_fourths_forces_descent
    (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hlarge : 7 * r ≤ 4 * A_orbit n r) :
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
    no_descent_forces_mean_valuation_below_seven_fourths
      n r hn hr hno
  omega

/-- Existing GARCD exact arithmetic descent criterion for the
uniform valuation threshold. -/
theorem mean_valuation_seven_fourths_forces_DESC
    (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r)
    (hlarge : 7 * r ≤ 4 * A_orbit n r) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧
      (C_orbit n j : ℤ) <
        ((2 : ℤ) ^ A_orbit n j - (3 : ℤ) ^ j) * (n : ℤ) := by
  obtain ⟨j, hjpos, hjr, hdrop⟩ :=
    mean_valuation_seven_fourths_forces_descent n r hn hr hlarge
  exact ⟨j, hjpos, hjr,
    (GARCD_4_2_Exact_Descent_Iff n j).mp hdrop⟩

end GARCD

#print axioms GARCD.no_descent_forces_mean_valuation_below_seven_fourths
#print axioms GARCD.mean_valuation_seven_fourths_forces_descent
#print axioms GARCD.mean_valuation_seven_fourths_forces_DESC

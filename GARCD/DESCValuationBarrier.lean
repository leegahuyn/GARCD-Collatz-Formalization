import GARCD.DESCGlobalTraceExplicit

/-!
# Finite no-descent valuation barrier

If every Syracuse orbit value through time r remains at least n > 0,
then its cumulative 2-adic valuation cannot be arbitrarily large:

    n^r * 2^(A_orbit n r) <= (3*n+1)^r.

The contrapositive gives a conditional but rigorous finite-time
descent certificate. No assertion is made that the threshold holds
for all n or eventually holds for every orbit.

This elementary inequality is not claimed to be a novel resolution
of the Collatz conjecture.
-/

namespace GARCD

/-- General multiplicative orbit barrier; independent of how the
valuation exponents are computed. -/
private theorem weighted_orbit_barrier
    (n : ℕ) (x a : ℕ → ℕ)
    (hx0 : x 0 = n)
    (hstep : ∀ j, 2 ^ a j * x (j + 1) = 3 * x j + 1)
    (r : ℕ)
    (hno : ∀ j, j ≤ r → n ≤ x j) :
    n ^ r * 2 ^ (∑ j ∈ Finset.range r, a j) * x r
      ≤ (3 * n + 1) ^ r * n := by
  induction r with
  | zero =>
      simp [hx0]
  | succ r ih =>
      have hprev : ∀ j, j ≤ r → n ≤ x j := by
        intro j hj
        exact hno j (by omega)
      have hind := ih hprev
      have hlocal : n * (2 ^ a r * x (r + 1)) ≤
          (3 * n + 1) * x r := by
        calc
          n * (2 ^ a r * x (r + 1)) = n * (3 * x r + 1) := by
            rw [hstep r]
          _ ≤ (3 * n + 1) * x r := by
            nlinarith [hno r (by omega)]
      calc
        n ^ (r + 1) *
            2 ^ (∑ j ∈ Finset.range (r + 1), a j) *
            x (r + 1) =
          (n ^ r * 2 ^ (∑ j ∈ Finset.range r, a j)) *
            (n * (2 ^ a r * x (r + 1))) := by
              rw [pow_succ, Finset.sum_range_succ, pow_add]
              ring
        _ ≤ (n ^ r * 2 ^ (∑ j ∈ Finset.range r, a j)) *
            ((3 * n + 1) * x r) :=
              Nat.mul_le_mul_left _ hlocal
        _ = (3 * n + 1) *
            (n ^ r * 2 ^ (∑ j ∈ Finset.range r, a j) * x r) := by
              ring
        _ ≤ (3 * n + 1) * ((3 * n + 1) ^ r * n) :=
              Nat.mul_le_mul_left _ hind
        _ = (3 * n + 1) ^ (r + 1) * n := by
              rw [pow_succ]
              ring

/-- Exact 2-adic budget obstruction: if there is no descent through
time r, then 2^A_r * n^r <= (3n+1)^r. -/
theorem no_descent_valuation_barrier (n r : ℕ) (hn : 0 < n)
    (hno : ∀ j, j ≤ r → n ≤ x_seq n j) :
    n ^ r * 2 ^ A_orbit n r ≤ (3 * n + 1) ^ r := by
  have hbase : x_seq n 0 = n := by simp [x_seq]
  have hstep (j : ℕ) :
      2 ^ a_seq n j * x_seq n (j + 1) =
        3 * x_seq n j + 1 := syracuse_step_eq n j
  have hmain := weighted_orbit_barrier n
    (x_seq n) (a_seq n) hbase hstep r hno
  have hlow : (n ^ r * 2 ^ A_orbit n r) * n ≤
      (n ^ r * 2 ^ A_orbit n r) * x_seq n r :=
        Nat.mul_le_mul_left _ (hno r le_rfl)
  have hmul : (n ^ r * 2 ^ A_orbit n r) * n ≤
      ((3 * n + 1) ^ r) * n := le_trans hlow hmain
  by_contra hbad
  have hlt : (3 * n + 1) ^ r < n ^ r * 2 ^ A_orbit n r := by
    omega
  have hmullt : ((3 * n + 1) ^ r) * n <
      (n ^ r * 2 ^ A_orbit n r) * n :=
        Nat.mul_lt_mul_of_pos_right hlt hn
  omega

/-- An explicitly testable finite-time threshold guarantees SOME
strict descent at or before r, but not necessarily at time r. -/
theorem valuation_threshold_forces_descent (n r : ℕ) (hn : 0 < n)
    (hlarge : (3 * n + 1) ^ r < n ^ r * 2 ^ A_orbit n r) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ x_seq n j < n := by
  by_contra h
  have hno : ∀ j : ℕ, j ≤ r → n ≤ x_seq n j := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0, x_seq]
    · have hjpos : 1 ≤ j := by omega
      have hnot : ¬ x_seq n j < n := by
        intro hdrop
        exact h ⟨j, hjpos, hj, hdrop⟩
      omega
  have hbound := no_descent_valuation_barrier n r hn hno
  omega

/-- The preceding necessary-condition barrier leads to an exact
GARCD arithmetic DESC witness, with a bounded certificate depth. -/
theorem valuation_threshold_forces_DESC (n r : ℕ) (hn : 0 < n)
    (hlarge : (3 * n + 1) ^ r < n ^ r * 2 ^ A_orbit n r) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧
      (C_orbit n j : ℤ) <
        ((2 : ℤ) ^ A_orbit n j - (3 : ℤ) ^ j) * (n : ℤ) := by
  obtain ⟨j, hjpos, hjr, hdrop⟩ :=
    valuation_threshold_forces_descent n r hn hlarge
  exact ⟨j, hjpos, hjr,
    (GARCD_4_2_Exact_Descent_Iff n j).mp hdrop⟩

end GARCD

#print axioms GARCD.no_descent_valuation_barrier
#print axioms GARCD.valuation_threshold_forces_descent
#print axioms GARCD.valuation_threshold_forces_DESC

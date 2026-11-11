import GARCD.DESCMeanFiveThirds

/-!
# General rational valuation drift barrier

For arbitrary natural positive starting value n and finite depth r >= 1,
let p,q be natural exponents satisfying the CHECKABLE arithmetic gap

   (3*n+1)^p < 2^q*n^p.

If every accelerated Syracuse step 0..r stays at least n, then
   p*A_orbit n r < q*r.

Conversely, p*A_r >= q*r certifies a strict descent by r and an exact
GARCD DESC arithmetic witness. All statements below quantify over
arbitrary p,q,r,n subject to their explicitly stated hypotheses.

This does not assert that every orbit eventually attains a supercritical
mean valuation. No general proof of the Collatz conjecture is claimed.
-/

namespace GARCD

/-- Rationally parameterized obstruction to a non-descending orbit.
The comparison (3n+1)^p < 2^q*n^p can be checked in natural arithmetic. -/
theorem rational_valuation_barrier
    (n r p q : ℕ) (hn : 0 < n) (hr : 1 ≤ r)
    (hgap : (3 * n + 1) ^ p < 2 ^ q * n ^ p)
    (hno : ∀ j : ℕ, j ≤ r → n ≤ x_seq n j) :
    p * A_orbit n r < q * r := by
  have hbar := no_descent_valuation_barrier n r hn hno
  have hstrictpow :
      ((3 * n + 1) ^ p) ^ r < (2 ^ q * n ^ p) ^ r := by
    gcongr <;> assumption <;> omega
  have hstrict : ((3 * n + 1) ^ r) ^ p <
      (n ^ r) ^ p * 2 ^ (q * r) := by
    calc
      ((3 * n + 1) ^ r) ^ p = ((3 * n + 1) ^ p) ^ r := by
        simp only [← pow_mul, mul_comm]
      _ < (2 ^ q * n ^ p) ^ r := hstrictpow
      _ = (n ^ r) ^ p * 2 ^ (q * r) := by
        simp only [mul_pow, ← pow_mul, mul_comm]
  by_contra hnot
  have hlarge : q * r ≤ p * A_orbit n r := by omega
  have hpow : 2 ^ (q * r) ≤ 2 ^ (p * A_orbit n r) :=
    Nat.pow_le_pow_right (by omega) hlarge
  have hleft : (n ^ r) ^ p * 2 ^ (q * r) ≤
      (n ^ r * 2 ^ A_orbit n r) ^ p := by
    calc
      (n ^ r) ^ p * 2 ^ (q * r) ≤
          (n ^ r) ^ p * 2 ^ (p * A_orbit n r) :=
            Nat.mul_le_mul_left _ hpow
      _ = (n ^ r * 2 ^ A_orbit n r) ^ p := by
        simp only [mul_pow, ← pow_mul, mul_comm]
  have hbarp : (n ^ r * 2 ^ A_orbit n r) ^ p ≤
      ((3 * n + 1) ^ r) ^ p := by
    gcongr <;> assumption
  omega

/-- A supercritical rational valuation prefix certifies a strict drop
at some step j ≤ r. This is a conditional sufficient criterion. -/
theorem rational_valuation_threshold_forces_descent
    (n r p q : ℕ) (hn : 0 < n) (hr : 1 ≤ r)
    (hgap : (3 * n + 1) ^ p < 2 ^ q * n ^ p)
    (hlarge : q * r ≤ p * A_orbit n r) :
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
  have hsmall := rational_valuation_barrier n r p q hn hr hgap hno
  omega

/-- Exact GARCD-4.2 arithmetic DESC witness from any rational
2-adic drift certificate which passes the finite power gap check. -/
theorem rational_valuation_threshold_forces_DESC
    (n r p q : ℕ) (hn : 0 < n) (hr : 1 ≤ r)
    (hgap : (3 * n + 1) ^ p < 2 ^ q * n ^ p)
    (hlarge : q * r ≤ p * A_orbit n r) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧
      (C_orbit n j : ℤ) <
        ((2 : ℤ) ^ A_orbit n j - (3 : ℤ) ^ j) * (n : ℤ) := by
  obtain ⟨j, hjpos, hjr, hdrop⟩ :=
    rational_valuation_threshold_forces_descent n r p q
      hn hr hgap hlarge
  exact ⟨j, hjpos, hjr,
    (GARCD_4_2_Exact_Descent_Iff n j).mp hdrop⟩

end GARCD

#print axioms GARCD.rational_valuation_barrier
#print axioms GARCD.rational_valuation_threshold_forces_descent
#print axioms GARCD.rational_valuation_threshold_forces_DESC

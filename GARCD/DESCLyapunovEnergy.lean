import GARCD.DESCFiveThirdsEquivalence

/-!
# Exact multiplicative Lyapunov energy for Syracuse trajectories

Let x_r = F^[r](n), and A_r the cumulative exact 2-adic valuation.
Define H_r = 2^(3*A_r) * x_r^3. The normalized energy
H_r / 32^r is a positive rational quantity, equal to 2^(3*A_r-5*r)*x_r^3.

This file proves:
1. An exact step recurrence, with valuation exponents canceled:
   H_(r+1) = 2^(3*A_r) * (3*x_r + 1)^3.
2. For x_r >= 7, normalized energy contracts at the explicit factor
   rho = 1331/1372 < 1:
   1372 * H_(r+1) <= 1331 * 32 * H_r.
3. The exact finite-prefix product inequality for any orbit staying >= 7.

These statements hold unconditionally under their stated local hypotheses.
They DO NOT force 3*A_r - 5*r to be nonnegative: normalized energy has
no positive lower bound independent of r. Thus this is not a proof of
the global Collatz conjecture or the OPEN GlobalFiveThirdsDriftGoal.
-/

namespace GARCD

/-- Integer numerator of the exact Lyapunov energy; the corresponding
rational energy is `lyapunovCubicNumerator n r / 32^r`. -/
def lyapunovCubicNumerator (n r : ℕ) : ℕ :=
  2 ^ (3 * A_orbit n r) * (x_seq n r) ^ 3

/-- Exact valuation cancellation, without logarithms or approximation. -/
theorem lyapunov_cubic_exact_step (n r : ℕ) :
    lyapunovCubicNumerator n (r + 1) =
      2 ^ (3 * A_orbit n r) * (3 * x_seq n r + 1) ^ 3 := by
  unfold lyapunovCubicNumerator
  rw [A_orbit_succ]
  have hpow : 2 ^ (3 * a_seq n r) = (2 ^ a_seq n r) ^ 3 := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    2 ^ (3 * (A_orbit n r + a_seq n r)) * (x_seq n (r + 1)) ^ 3 =
        2 ^ (3 * A_orbit n r) *
          (2 ^ a_seq n r * x_seq n (r + 1)) ^ 3 := by
            rw [mul_add, pow_add, mul_pow, ← hpow]
            ring
    _ = 2 ^ (3 * A_orbit n r) * (3 * x_seq n r + 1) ^ 3 := by
          rw [syracuse_step_eq n r]

/-- Sharp uniform rational cubic contraction for x >= 7.
Equality occurs for x = 7. The bound is equivalent to
(3 + 1/x)^3 / 32 <= 1331 / 1372. -/
private theorem sharp_cubic_lyapunov_gap (x : ℕ) (hx : 7 ≤ x) :
    1372 * (3 * x + 1) ^ 3 ≤ 1331 * 32 * x ^ 3 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x = k + 7 := ⟨x - 7, by omega⟩
  rw [hk]
  nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2)]

/-- Exact one-step deterministic Lyapunov contraction, without any
real-valued logarithm or probabilistic assumption. -/
theorem lyapunov_cubic_one_step (n r : ℕ)
    (hge : 7 ≤ x_seq n r) :
    1372 * lyapunovCubicNumerator n (r + 1) ≤
      1331 * 32 * lyapunovCubicNumerator n r := by
  rw [lyapunov_cubic_exact_step]
  unfold lyapunovCubicNumerator
  have hgap := sharp_cubic_lyapunov_gap (x_seq n r) hge
  have hmul := Nat.mul_le_mul_left
    (2 ^ (3 * A_orbit n r)) hgap
  calc
    1372 * (2 ^ (3 * A_orbit n r) * (3 * x_seq n r + 1) ^ 3) =
        2 ^ (3 * A_orbit n r) *
          (1372 * (3 * x_seq n r + 1) ^ 3) := by ring
    _ ≤ 2 ^ (3 * A_orbit n r) *
          (1331 * 32 * (x_seq n r) ^ 3) := hmul
    _ = 1331 * 32 *
          (2 ^ (3 * A_orbit n r) * (x_seq n r) ^ 3) := by ring

/-- Finite-prefix contraction: if every pre-step orbit value >= 7,
the normalized Lyapunov energy decreases at least geometrically.
Importantly, this inequality does NOT establish eventual drift surplus. -/
theorem lyapunov_cubic_prefix_bound (n r : ℕ)
    (hge : ∀ j : ℕ, j < r → 7 ≤ x_seq n j) :
    1372 ^ r * lyapunovCubicNumerator n r ≤
      (1331 * 32) ^ r * n ^ 3 := by
  induction r with
  | zero =>
      simp [lyapunovCubicNumerator, A_orbit, x_seq]
  | succ r ih =>
      have hprev : ∀ j : ℕ, j < r → 7 ≤ x_seq n j := by
        intro j hj
        exact hge j (by omega)
      have hrge : 7 ≤ x_seq n r := hge r (by omega)
      have hstep := lyapunov_cubic_one_step n r hrge
      have hprevbound := ih hprev
      calc
        1372 ^ (r + 1) * lyapunovCubicNumerator n (r + 1) =
          1372 ^ r * (1372 * lyapunovCubicNumerator n (r + 1)) := by
            rw [pow_succ]
            ring
        _ ≤ 1372 ^ r * (1331 * 32 * lyapunovCubicNumerator n r) :=
          Nat.mul_le_mul_left _ hstep
        _ = (1331 * 32) *
              (1372 ^ r * lyapunovCubicNumerator n r) := by ring
        _ ≤ (1331 * 32) * ((1331 * 32) ^ r * n ^ 3) :=
          Nat.mul_le_mul_left _ hprevbound
        _ = (1331 * 32) ^ (r + 1) * n ^ 3 := by
          rw [pow_succ]
          ring

end GARCD

#print axioms GARCD.lyapunov_cubic_exact_step
#print axioms GARCD.lyapunov_cubic_one_step
#print axioms GARCD.lyapunov_cubic_prefix_bound

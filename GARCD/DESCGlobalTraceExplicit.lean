import GARCD.DESCGlobalTraceExistence

/-!
# Explicit canonical affine lift modulus

For every n and r, the entire class
  n + 2^(A_orbit n r + 1) * t
has the exact same initial Syracuse valuation word of length r.
This proves the explicit arithmetic progression formula, not descent.
-/

namespace GARCD

/-- The exact canonical arithmetic progression which shares the first
r Syracuse valuation exponents with n (including n = 0). -/
theorem global_affine_trace_exact_modulus (n r : ℕ) :
    ∀ t : ℕ,
      x_seq (n + 2 ^ (A_orbit n r + 1) * t) r =
        x_seq n r + (2 * 3 ^ r) * t := by
  induction r with
  | zero =>
      intro t
      simp [A_orbit, x_seq]
  | succ r ih =>
      intro t
      let e : ℕ := a_seq n r
      have hA : A_orbit n (r + 1) = A_orbit n r + e := by
        simp [A_orbit, e, Finset.sum_range_succ]
      have hpow : 2 ^ (A_orbit n (r + 1) + 1) =
          2 ^ (A_orbit n r + 1) * 2 ^ e := by
        calc
          2 ^ (A_orbit n (r + 1) + 1) =
              2 ^ (A_orbit n r + 1 + e) := by
                congr 1
                omega
          _ = 2 ^ (A_orbit n r + 1) * 2 ^ e := by rw [pow_add]
      have harg : n + 2 ^ (A_orbit n (r + 1) + 1) * t =
          n + 2 ^ (A_orbit n r + 1) * (2 ^ e * t) := by
        rw [hpow]
        ring
      have hmid : x_seq (n + 2 ^ (A_orbit n (r + 1) + 1) * t) r =
          (2 ^ e * (2 * 3 ^ r)) * t + x_seq n r := by
        rw [harg, ih (2 ^ e * t)]
        ring
      have hcoeff : 3 * (2 ^ e * (2 * 3 ^ r)) =
          2 ^ e * (2 * 3 ^ (r + 1)) := by
        rw [pow_succ]
        ring
      have hconst : 3 * x_seq n r + 1 =
          2 ^ e * F (x_seq n r) := by
        change 3 * x_seq n r + 1 =
          2 ^ v2 (3 * x_seq n r + 1) * F (x_seq n r)
        exact (two_pow_v2_mul_F (x_seq n r)).symm
      have heven : (2 * 3 ^ (r + 1)) % 2 = 0 := by omega
      have hstep : F ((2 ^ e * (2 * 3 ^ r)) * t + x_seq n r) =
          (2 * 3 ^ (r + 1)) * t + F (x_seq n r) :=
        affine_F_step _ _ _ _ _ _ hcoeff hconst heven (F_odd _)
      calc
        x_seq (n + 2 ^ (A_orbit n (r + 1) + 1) * t) (r + 1) =
            F (x_seq (n + 2 ^ (A_orbit n (r + 1) + 1) * t) r) := by
              unfold x_seq
              rw [Function.iterate_succ_apply']
        _ = F ((2 ^ e * (2 * 3 ^ r)) * t + x_seq n r) := by
              rw [hmid]
        _ = (2 * 3 ^ (r + 1)) * t + F (x_seq n r) := hstep
        _ = x_seq n (r + 1) + (2 * 3 ^ (r + 1)) * t := by
              have hs : x_seq n (r + 1) = F (x_seq n r) := by
                unfold x_seq
                rw [Function.iterate_succ_apply']
              rw [hs]
              omega

end GARCD

#print axioms GARCD.global_affine_trace_exact_modulus

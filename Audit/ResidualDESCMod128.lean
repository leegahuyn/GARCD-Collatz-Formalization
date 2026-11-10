import GARCD.Module12

/-!
Two additional unconditional subfamilies among the residual odd inputs.
Neither of these claims establishes universal DESC.
-/
namespace GARCD

private lemma v2_lower_of_power_dvd (x k : ℕ)
    (h : 2 ^ k ∣ 3 * x + 1) :
    k ≤ v2 (3 * x + 1) := by
  unfold v2
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (by omega : 3 * x + 1 ≠ 0)).mp h

/-- Every n congruent to 7 mod 128 drops in four accelerated steps. -/
theorem Syracuse_descent_mod128_7 (n : ℕ) (hn : 3 ≤ n)
    (hmod : n % 128 = 7) : x_seq n 4 < n := by
  let q := n / 128
  have hn_eq : n = 128 * q + 7 := by
    dsimp [q]
    omega
  have hv1 : v2 (3 * n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * n + 1) % 4 = 2
    omega
  have h3n : 3 * n + 1 = 2 * (192 * q + 11) := by omega
  have hFn : F n = 192 * q + 11 := by
    unfold F
    rw [hv1, pow_one, h3n, Nat.mul_div_right _ (by omega)]
  have hv2 : v2 (3 * F n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F n + 1) % 4 = 2
    rw [hFn]
    omega
  have h3Fn : 3 * F n + 1 = 2 * (288 * q + 17) := by
    rw [hFn]
    ring
  have hF2 : F (F n) = 288 * q + 17 := by
    change (3 * F n + 1) / 2 ^ v2 (3 * F n + 1) = _
    rw [hv2, pow_one, h3Fn, Nat.mul_div_right _ (by omega)]
  have hv3 : v2 (3 * F (F n) + 1) = 2 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F (F n) + 1) % 8 = 4
    rw [hF2]
    omega
  have h3F2 : 3 * F (F n) + 1 = 4 * (216 * q + 13) := by
    rw [hF2]
    ring
  have hF3 : F (F (F n)) = 216 * q + 13 := by
    change (3 * F (F n) + 1) / 2 ^ v2 (3 * F (F n) + 1) = _
    rw [hv3, show (2 : ℕ) ^ 2 = 4 by norm_num, h3F2]
    omega
  have hdvd : 2 ^ 3 ∣ 3 * F (F (F n)) + 1 := by
    rw [hF3]
    refine ⟨81 * q + 5, by ring⟩
  have hv4 : 3 ≤ v2 (3 * F (F (F n)) + 1) :=
    v2_lower_of_power_dvd _ 3 hdvd
  have hpow : 8 ≤ 2 ^ v2 (3 * F (F (F n)) + 1) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ v2 (3 * F (F (F n)) + 1) :=
        Nat.pow_le_pow_right (by omega) hv4
  have hbound : 8 * F (F (F (F n))) ≤ 3 * F (F (F n)) + 1 := by
    calc
      8 * F (F (F (F n))) ≤
          2 ^ v2 (3 * F (F (F n)) + 1) * F (F (F (F n))) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * F (F (F n)) + 1 := two_pow_v2_mul_F (F (F (F n)))
  change F (F (F (F n))) < n
  rw [hF3] at hbound ⊢
  omega

/-- Every n congruent to 15 mod 128 drops in four accelerated steps. -/
theorem Syracuse_descent_mod128_15 (n : ℕ) (hn : 3 ≤ n)
    (hmod : n % 128 = 15) : x_seq n 4 < n := by
  let q := n / 128
  have hn_eq : n = 128 * q + 15 := by
    dsimp [q]
    omega
  have hv1 : v2 (3 * n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * n + 1) % 4 = 2
    omega
  have h3n : 3 * n + 1 = 2 * (192 * q + 23) := by omega
  have hFn : F n = 192 * q + 23 := by
    unfold F
    rw [hv1, pow_one, h3n, Nat.mul_div_right _ (by omega)]
  have hv2 : v2 (3 * F n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F n + 1) % 4 = 2
    rw [hFn]
    omega
  have h3Fn : 3 * F n + 1 = 2 * (288 * q + 35) := by
    rw [hFn]
    ring
  have hF2 : F (F n) = 288 * q + 35 := by
    change (3 * F n + 1) / 2 ^ v2 (3 * F n + 1) = _
    rw [hv2, pow_one, h3Fn, Nat.mul_div_right _ (by omega)]
  have hv3 : v2 (3 * F (F n) + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F (F n) + 1) % 4 = 2
    rw [hF2]
    omega
  have h3F2 : 3 * F (F n) + 1 = 2 * (432 * q + 53) := by
    rw [hF2]
    ring
  have hF3 : F (F (F n)) = 432 * q + 53 := by
    change (3 * F (F n) + 1) / 2 ^ v2 (3 * F (F n) + 1) = _
    rw [hv3, pow_one, h3F2, Nat.mul_div_right _ (by omega)]
  have hdvd : 2 ^ 4 ∣ 3 * F (F (F n)) + 1 := by
    rw [hF3]
    refine ⟨81 * q + 10, by ring⟩
  have hv4 : 4 ≤ v2 (3 * F (F (F n)) + 1) :=
    v2_lower_of_power_dvd _ 4 hdvd
  have hpow : 16 ≤ 2 ^ v2 (3 * F (F (F n)) + 1) := by
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ v2 (3 * F (F (F n)) + 1) :=
        Nat.pow_le_pow_right (by omega) hv4
  have hbound : 16 * F (F (F (F n))) ≤ 3 * F (F (F n)) + 1 := by
    calc
      16 * F (F (F (F n))) ≤
          2 ^ v2 (3 * F (F (F n)) + 1) * F (F (F (F n))) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * F (F (F n)) + 1 := two_pow_v2_mul_F (F (F (F n)))
  change F (F (F (F n))) < n
  rw [hF3] at hbound ⊢
  omega

theorem DESC_mod128_7 (n : ℕ) (hn : 3 ≤ n) (hmod : n % 128 = 7) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by
  refine ⟨4, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff n 4).mp
    (Syracuse_descent_mod128_7 n hn hmod)

theorem DESC_mod128_15 (n : ℕ) (hn : 3 ≤ n) (hmod : n % 128 = 15) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by
  refine ⟨4, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff n 4).mp
    (Syracuse_descent_mod128_15 n hn hmod)

end GARCD

#print axioms GARCD.Syracuse_descent_mod128_7
#print axioms GARCD.Syracuse_descent_mod128_15
#print axioms GARCD.DESC_mod128_7
#print axioms GARCD.DESC_mod128_15

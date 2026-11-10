import GARCD.Module12

/-! Verified restricted descent certificates and exact residual open obligation.
The universal Collatz conjecture remains unproved. -/

namespace GARCD

/-- The accelerated Syracuse map drops below the starting value after
three odd steps for every n congruent to 11 modulo 32. -/
theorem Syracuse_descent_mod32_11 (n : ℕ) (hn : 3 ≤ n)
    (hmod : n % 32 = 11) :
    x_seq n 3 < n := by
  let q := n / 32
  have hn_eq : n = 32 * q + 11 := by
    dsimp [q]
    omega
  have hv1 : v2 (3 * n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * n + 1) % 4 = 2
    omega
  have h3n : 3 * n + 1 = 2 * (48 * q + 17) := by omega
  have hFn : F n = 48 * q + 17 := by
    unfold F
    rw [hv1, pow_one, h3n, Nat.mul_div_right _ (by omega)]
  have hv2 : v2 (3 * F n + 1) = 2 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F n + 1) % 8 = 4
    rw [hFn]
    omega
  have h3Fn : 3 * F n + 1 = 4 * (36 * q + 13) := by
    rw [hFn]
    ring
  have hF2 : F (F n) = 36 * q + 13 := by
    change (3 * F n + 1) / 2 ^ v2 (3 * F n + 1) = _
    rw [hv2, show (2 : ℕ) ^ 2 = 4 by norm_num, h3Fn]
    omega
  have hv3 : 2 ≤ v2 (3 * F (F n) + 1) := by
    have hodd : F (F n) % 2 = 1 := F_odd (F n)
    have ha_ge1 : 1 ≤ v2 (3 * F (F n) + 1) :=
      v2_three_mul_add_one_ge_one hodd
    by_contra hlt
    have ha_eq1 : v2 (3 * F (F n) + 1) = 1 := by omega
    rw [v2_eq_iff_mod_two_pow_succ (by omega)] at ha_eq1
    change (3 * F (F n) + 1) % 4 = 2 at ha_eq1
    rw [hF2] at ha_eq1
    omega
  have hpow : 4 ≤ 2 ^ v2 (3 * F (F n) + 1) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ v2 (3 * F (F n) + 1) :=
        Nat.pow_le_pow_right (by omega) hv3
  have hbound : 4 * F (F (F n)) ≤ 3 * F (F n) + 1 := by
    calc
      4 * F (F (F n)) ≤
          2 ^ v2 (3 * F (F n) + 1) * F (F (F n)) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * F (F n) + 1 := two_pow_v2_mul_F (F (F n))
  change F (F (F n)) < n
  rw [hF2] at hbound ⊢
  omega

/-- The exact integer DESC inequality follows from the proved drop,
with explicit witness r = 3. -/
theorem DESC_mod32_11 (n : ℕ) (hn : 3 ≤ n)
    (hmod : n % 32 = 11) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by
  refine ⟨3, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff n 3).mp
    (Syracuse_descent_mod32_11 n hn hmod)


/-- The residual exact universal arithmetic DESC obligation after the
already verified mod-4, mod-16 and new mod-32 descent classes. This is
a PROP ONLY, not a theorem asserting existence of descent. -/
def RemainingDESCMod32Goal : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 23 ∨
     n % 32 = 27 ∨ n % 32 = 31) →
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ)

/-- Full arithmetic DESC is equivalent to its restriction to the five
unresolved odd residue classes modulo 32. This equivalence DOES NOT
prove the proposition on the right. -/
theorem DESCArithmeticProp_iff_remaining_five_mod32 :
    DESCArithmeticProp ↔ RemainingDESCMod32Goal := by
  constructor
  · intro hall n hn _
    have hodd : n % 2 = 1 := by omega
    exact hall n hodd hn
  · intro hrest n hodd hn
    by_cases hbase : n % 4 = 1 ∨ n % 16 = 3
    · rcases hbase with h4 | h16
      · refine ⟨1, by omega, ?_⟩
        exact (GARCD_4_2_Exact_Descent_Iff n 1).mp
          ((Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn).1 h4)
      · refine ⟨2, by omega, ?_⟩
        exact (GARCD_4_2_Exact_Descent_Iff n 2).mp
          ((Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn).2 h16)
    · by_cases h11 : n % 32 = 11
      · exact DESC_mod32_11 n hn h11
      · have hclasses : n % 32 = 7 ∨ n % 32 = 15 ∨
            n % 32 = 23 ∨ n % 32 = 27 ∨ n % 32 = 31 := by
          omega
        exact hrest n hn hclasses


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


/-- The remaining predicate after all verified mod 4, 16, 32 and 128
descent families have been removed. Declaring it is NOT a proof. -/
def RemainingDESCMod128Goal : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
    ¬ (n % 4 = 1 ∨ n % 16 = 3 ∨ n % 32 = 11 ∨
        n % 128 = 7 ∨ n % 128 = 15) →
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ)

/-- The EXACT remaining unsolved obligation is equivalent to full DESC.
This is a logically sound reduction, not a proof of the remaining premise. -/
theorem DESCArithmeticProp_iff_remaining_mod128 :
    DESCArithmeticProp ↔ RemainingDESCMod128Goal := by
  constructor
  · intro hall n hodd hn _
    exact hall n hodd hn
  · intro hrest n hodd hn
    by_cases hbase : n % 4 = 1 ∨ n % 16 = 3
    · rcases hbase with h4 | h16
      · refine ⟨1, by omega, ?_⟩
        exact (GARCD_4_2_Exact_Descent_Iff n 1).mp
          ((Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn).1 h4)
      · refine ⟨2, by omega, ?_⟩
        exact (GARCD_4_2_Exact_Descent_Iff n 2).mp
          ((Theorem_12_5_2_Mod4_And_Mod16_Universal_Descent n hn).2 h16)
    · by_cases h11 : n % 32 = 11
      · exact DESC_mod32_11 n hn h11
      · by_cases h7 : n % 128 = 7
        · exact DESC_mod128_7 n hn h7
        · by_cases h15 : n % 128 = 15
          · exact DESC_mod128_15 n hn h15
          · exact hrest n hodd hn (by omega)

/-- Proving the remaining residue classes would prove the full
Collatz conjecture. The direction is an equivalence only. -/
theorem RemainingDESCMod128Goal_iff_Collatz :
    RemainingDESCMod128Goal ↔ CollatzConjectureProp := by
  exact DESCArithmeticProp_iff_remaining_mod128.symm.trans
    (Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality.symm.trans
      Theorem_10_2_2_DESC_Iff_Collatz_Conjecture)

end GARCD

#print axioms GARCD.DESCArithmeticProp_iff_remaining_mod128
#print axioms GARCD.RemainingDESCMod128Goal_iff_Collatz

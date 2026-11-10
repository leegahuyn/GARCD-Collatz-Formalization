import GARCD.ResidualDESC

/-!
# Additional exact descending residue families

All quantified results in this file concern *proved* subclasses.
The final 13-residue DESC goal is deliberately represented as an
equivalence with the unresolved full Collatz conjecture, not as a proof.
-/

namespace GARCD

private lemma residue_v2_lower (x k : ℕ)
    (hdvd : 2 ^ k ∣ 3 * x + 1) :
    k ≤ v2 (3 * x + 1) := by
  unfold v2
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (by omega : 3 * x + 1 ≠ 0)).mp hdvd

/-- Every odd n ≡ 23 modulo 32 descends within three accelerated steps.
The conclusion is uniform over the infinite residue class. -/
theorem Syracuse_descent_mod32_23 (n : ℕ) (hn : 3 ≤ n)
    (hmod : n % 32 = 23) : x_seq n 3 < n := by
  let q := n / 32
  have hn_eq : n = 32 * q + 23 := by
    dsimp [q]
    omega
  have hv1 : v2 (3 * n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * n + 1) % 4 = 2
    omega
  have h3n : 3 * n + 1 = 2 * (48 * q + 35) := by omega
  have hFn : F n = 48 * q + 35 := by
    unfold F
    rw [hv1, pow_one, h3n, Nat.mul_div_right _ (by omega)]
  have hv2 : v2 (3 * F n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F n + 1) % 4 = 2
    rw [hFn]
    omega
  have h3Fn : 3 * F n + 1 = 2 * (72 * q + 53) := by
    rw [hFn]
    ring
  have hF2 : F (F n) = 72 * q + 53 := by
    change (3 * F n + 1) / 2 ^ v2 (3 * F n + 1) = _
    rw [hv2, pow_one, h3Fn, Nat.mul_div_right _ (by omega)]
  have hdvd : 2 ^ 3 ∣ 3 * F (F n) + 1 := by
    rw [hF2]
    refine ⟨27 * q + 20, by ring⟩
  have hv3 : 3 ≤ v2 (3 * F (F n) + 1) :=
    residue_v2_lower _ 3 hdvd
  have hpow : 8 ≤ 2 ^ v2 (3 * F (F n) + 1) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ v2 (3 * F (F n) + 1) :=
        Nat.pow_le_pow_right (by omega) hv3
  have hbound : 8 * F (F (F n)) ≤ 3 * F (F n) + 1 := by
    calc
      8 * F (F (F n)) ≤
          2 ^ v2 (3 * F (F n) + 1) * F (F (F n)) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * F (F n) + 1 := two_pow_v2_mul_F (F (F n))
  change F (F (F n)) < n
  rw [hF2] at hbound ⊢
  omega

/-- Every odd n ≡ 59 modulo 128 descends within four accelerated steps. -/
theorem Syracuse_descent_mod128_59 (n : ℕ) (hn : 3 ≤ n)
    (hmod : n % 128 = 59) : x_seq n 4 < n := by
  let q := n / 128
  have hn_eq : n = 128 * q + 59 := by
    dsimp [q]
    omega
  have hv1 : v2 (3 * n + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * n + 1) % 4 = 2
    omega
  have h3n : 3 * n + 1 = 2 * (192 * q + 89) := by omega
  have hFn : F n = 192 * q + 89 := by
    unfold F
    rw [hv1, pow_one, h3n, Nat.mul_div_right _ (by omega)]
  have hv2 : v2 (3 * F n + 1) = 2 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F n + 1) % 8 = 4
    rw [hFn]
    omega
  have h3Fn : 3 * F n + 1 = 4 * (144 * q + 67) := by
    rw [hFn]
    ring
  have hF2 : F (F n) = 144 * q + 67 := by
    change (3 * F n + 1) / 2 ^ v2 (3 * F n + 1) = _
    rw [hv2, show (2 : ℕ) ^ 2 = 4 by norm_num, h3Fn]
    omega
  have hv3 : v2 (3 * F (F n) + 1) = 1 := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    change (3 * F (F n) + 1) % 4 = 2
    rw [hF2]
    omega
  have h3F2 : 3 * F (F n) + 1 = 2 * (216 * q + 101) := by
    rw [hF2]
    ring
  have hF3 : F (F (F n)) = 216 * q + 101 := by
    change (3 * F (F n) + 1) / 2 ^ v2 (3 * F (F n) + 1) = _
    rw [hv3, pow_one, h3F2, Nat.mul_div_right _ (by omega)]
  have hdvd : 2 ^ 3 ∣ 3 * F (F (F n)) + 1 := by
    rw [hF3]
    refine ⟨81 * q + 38, by ring⟩
  have hv4 : 3 ≤ v2 (3 * F (F (F n)) + 1) :=
    residue_v2_lower _ 3 hdvd
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

/-- The exact arithmetic DESC consequence with a fixed witness r=3. -/
theorem DESC_mod32_23 (n : ℕ) (hn : 3 ≤ n) (hmod : n % 32 = 23) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by
  refine ⟨3, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff n 3).mp
    (Syracuse_descent_mod32_23 n hn hmod)

/-- The exact arithmetic DESC consequence with a fixed witness r=4. -/
theorem DESC_mod128_59 (n : ℕ) (hn : 3 ≤ n) (hmod : n % 128 = 59) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by
  refine ⟨4, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff n 4).mp
    (Syracuse_descent_mod128_59 n hn hmod)

/-- Exact unresolved proposition after the newly certified families
n ≡ 23 (mod 32) and n ≡ 59 (mod 128) are also removed. -/
def RemainingDESC13Mod128Goal : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
    ¬ (n % 4 = 1 ∨ n % 16 = 3 ∨ n % 32 = 11 ∨
        n % 128 = 7 ∨ n % 128 = 15 ∨
        n % 32 = 23 ∨ n % 128 = 59) →
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit n r : ℤ) <
        ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ)

/-- Exact remaining predicate is equivalent to full arithmetic DESC.
This equivalence DOES NOT assert or prove the remaining DESC obligation. -/
theorem DESCArithmeticProp_iff_remaining_thirteen_mod128 :
    DESCArithmeticProp ↔ RemainingDESC13Mod128Goal := by
  refine DESCArithmeticProp_iff_remaining_mod128.trans ?_
  constructor
  · intro h n hodd hn hrest
    exact h n hodd hn (by omega)
  · intro h n hodd hn hbase
    by_cases h23 : n % 32 = 23
    · exact DESC_mod32_23 n hn h23
    · by_cases h59 : n % 128 = 59
      · exact DESC_mod128_59 n hn h59
      · exact h n hodd hn (by omega)

/-- The last 13 classes still carry the full mathematical difficulty
of the Collatz conjecture. This is an equivalence, not a proof. -/
theorem RemainingDESC13Mod128Goal_iff_Collatz :
    RemainingDESC13Mod128Goal ↔ CollatzConjectureProp := by
  exact DESCArithmeticProp_iff_remaining_thirteen_mod128.symm.trans
    (Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality.symm.trans
      Theorem_10_2_2_DESC_Iff_Collatz_Conjecture)

/-- The explicit thirteen congruences are exactly the remaining odd
residue classes modulo 128. -/
theorem remaining_residues_exactly_thirteen (n : ℕ) :
    (n % 2 = 1 ∧
      ¬ (n % 4 = 1 ∨ n % 16 = 3 ∨ n % 32 = 11 ∨
          n % 128 = 7 ∨ n % 128 = 15 ∨
          n % 32 = 23 ∨ n % 128 = 59))
      ↔
    (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨
     n % 128 = 47 ∨ n % 128 = 63 ∨ n % 128 = 71 ∨
     n % 128 = 79 ∨ n % 128 = 91 ∨ n % 128 = 95 ∨
     n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨
     n % 128 = 127) := by
  omega

end GARCD

#print axioms GARCD.Syracuse_descent_mod32_23
#print axioms GARCD.Syracuse_descent_mod128_59
#print axioms GARCD.DESC_mod32_23
#print axioms GARCD.DESC_mod128_59
#print axioms GARCD.DESCArithmeticProp_iff_remaining_thirteen_mod128
#print axioms GARCD.RemainingDESC13Mod128Goal_iff_Collatz
#print axioms GARCD.remaining_residues_exactly_thirteen

import GARCD.ResidualDESCFurther

/-!
# Verified candidates for DESC in thirteen infinite residual subfamilies

Each result here quantifies over every t : ℕ in ONE congruence
class modulo 512, 2048 or 8192, and implies the exact arithmetic DESC
inequality with a fixed accelerated step r = 5, 6 or 7.
No claim of DESC for the whole remaining thirteen classes modulo 128
is made here. The Collatz conjecture is still unproved.
-/

namespace GARCD

/-- Obtain an exact accelerated Syracuse step from a certified
numerator factorization and exact 2-adic valuation. -/
private theorem F_from_exact_div (x y k : ℕ)
    (hnum : 3 * x + 1 = 2 ^ k * y)
    (hmod : (3 * x + 1) % (2 ^ (k + 1)) = 2 ^ k) :
    F x = y := by
  have hv : v2 (3 * x + 1) = k := by
    rw [v2_eq_iff_mod_two_pow_succ (by omega)]
    exact hmod
  unfold F
  rw [hv, hnum, Nat.mul_div_right _ (by positivity)]

/-- All n = 2048 * t + 1947 descend in exactly 6 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 27). -/
theorem Syracuse_descent_family_27 (t : ℕ) :
    x_seq (2048 * t + 1947) 6 < 2048 * t + 1947 := by
  have h1 : F (2048 * t + 1947) = 3072 * t + 2921 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (3072 * t + 2921) = 2304 * t + 2191 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (2304 * t + 2191) = 3456 * t + 3287 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (3456 * t + 3287) = 5184 * t + 4931 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (5184 * t + 4931) = 7776 * t + 7397 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h6 : F (7776 * t + 7397) = 1458 * t + 1387 := by
    apply F_from_exact_div _ _ 4
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (F (2048 * t + 1947)))))) < 2048 * t + 1947
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 2048 * t + 1947 class.
The witness is the fixed number of accelerated steps 6. -/
theorem DESC_family_27 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (2048 * t + 1947) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (2048 * t + 1947) r - (3 : ℤ) ^ r) *
          ((2048 * t + 1947) : ℤ) := by
  refine ⟨6, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (2048 * t + 1947) 6).mp
    (Syracuse_descent_family_27 t)

/-- All n = 2048 * t + 287 descend in exactly 6 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 31). -/
theorem Syracuse_descent_family_31 (t : ℕ) :
    x_seq (2048 * t + 287) 6 < 2048 * t + 287 := by
  have h1 : F (2048 * t + 287) = 3072 * t + 431 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (3072 * t + 431) = 4608 * t + 647 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (4608 * t + 647) = 6912 * t + 971 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (6912 * t + 971) = 10368 * t + 1457 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (10368 * t + 1457) = 7776 * t + 1093 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h6 : F (7776 * t + 1093) = 1458 * t + 205 := by
    apply F_from_exact_div _ _ 4
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (F (2048 * t + 287)))))) < 2048 * t + 287
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 2048 * t + 287 class.
The witness is the fixed number of accelerated steps 6. -/
theorem DESC_family_31 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (2048 * t + 287) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (2048 * t + 287) r - (3 : ℤ) ^ r) *
          ((2048 * t + 287) : ℤ) := by
  refine ⟨6, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (2048 * t + 287) 6).mp
    (Syracuse_descent_family_31 t)

/-- All n = 512 * t + 295 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 39). -/
theorem Syracuse_descent_family_39 (t : ℕ) :
    x_seq (512 * t + 295) 5 < 512 * t + 295 := by
  have h1 : F (512 * t + 295) = 768 * t + 443 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 443) = 1152 * t + 665 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (1152 * t + 665) = 864 * t + 499 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (864 * t + 499) = 1296 * t + 749 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (1296 * t + 749) = 486 * t + 281 := by
    apply F_from_exact_div _ _ 3
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 295))))) < 512 * t + 295
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 295 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_39 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 295) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 295) r - (3 : ℤ) ^ r) *
          ((512 * t + 295) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 295) 5).mp
    (Syracuse_descent_family_39 t)

/-- All n = 512 * t + 175 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 47). -/
theorem Syracuse_descent_family_47 (t : ℕ) :
    x_seq (512 * t + 175) 5 < 512 * t + 175 := by
  have h1 : F (512 * t + 175) = 768 * t + 263 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 263) = 1152 * t + 395 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (1152 * t + 395) = 1728 * t + 593 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (1728 * t + 593) = 1296 * t + 445 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (1296 * t + 445) = 486 * t + 167 := by
    apply F_from_exact_div _ _ 3
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 175))))) < 512 * t + 175
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 175 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_47 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 175) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 175) r - (3 : ℤ) ^ r) *
          ((512 * t + 175) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 175) 5).mp
    (Syracuse_descent_family_47 t)

/-- All n = 2048 * t + 1599 descend in exactly 6 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 63). -/
theorem Syracuse_descent_family_63 (t : ℕ) :
    x_seq (2048 * t + 1599) 6 < 2048 * t + 1599 := by
  have h1 : F (2048 * t + 1599) = 3072 * t + 2399 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (3072 * t + 2399) = 4608 * t + 3599 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (4608 * t + 3599) = 6912 * t + 5399 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (6912 * t + 5399) = 10368 * t + 8099 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (10368 * t + 8099) = 15552 * t + 12149 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h6 : F (15552 * t + 12149) = 1458 * t + 1139 := by
    apply F_from_exact_div _ _ 5
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (F (2048 * t + 1599)))))) < 2048 * t + 1599
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 2048 * t + 1599 class.
The witness is the fixed number of accelerated steps 6. -/
theorem DESC_family_63 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (2048 * t + 1599) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (2048 * t + 1599) r - (3 : ℤ) ^ r) *
          ((2048 * t + 1599) : ℤ) := by
  refine ⟨6, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (2048 * t + 1599) 6).mp
    (Syracuse_descent_family_63 t)

/-- All n = 512 * t + 455 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 71). -/
theorem Syracuse_descent_family_71 (t : ℕ) :
    x_seq (512 * t + 455) 5 < 512 * t + 455 := by
  have h1 : F (512 * t + 455) = 768 * t + 683 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 683) = 1152 * t + 1025 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (1152 * t + 1025) = 864 * t + 769 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (864 * t + 769) = 648 * t + 577 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (648 * t + 577) = 486 * t + 433 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 455))))) < 512 * t + 455
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 455 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_71 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 455) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 455) r - (3 : ℤ) ^ r) *
          ((512 * t + 455) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 455) 5).mp
    (Syracuse_descent_family_71 t)

/-- All n = 512 * t + 335 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 79). -/
theorem Syracuse_descent_family_79 (t : ℕ) :
    x_seq (512 * t + 335) 5 < 512 * t + 335 := by
  have h1 : F (512 * t + 335) = 768 * t + 503 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 503) = 1152 * t + 755 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (1152 * t + 755) = 1728 * t + 1133 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (1728 * t + 1133) = 648 * t + 425 := by
    apply F_from_exact_div _ _ 3
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (648 * t + 425) = 486 * t + 319 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 335))))) < 512 * t + 335
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 335 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_79 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 335) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 335) r - (3 : ℤ) ^ r) *
          ((512 * t + 335) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 335) 5).mp
    (Syracuse_descent_family_79 t)

/-- All n = 512 * t + 219 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 91). -/
theorem Syracuse_descent_family_91 (t : ℕ) :
    x_seq (512 * t + 219) 5 < 512 * t + 219 := by
  have h1 : F (512 * t + 219) = 768 * t + 329 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 329) = 576 * t + 247 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (576 * t + 247) = 864 * t + 371 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (864 * t + 371) = 1296 * t + 557 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (1296 * t + 557) = 486 * t + 209 := by
    apply F_from_exact_div _ _ 3
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 219))))) < 512 * t + 219
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 219 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_91 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 219) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 219) r - (3 : ℤ) ^ r) *
          ((512 * t + 219) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 219) 5).mp
    (Syracuse_descent_family_91 t)

/-- All n = 512 * t + 95 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 95). -/
theorem Syracuse_descent_family_95 (t : ℕ) :
    x_seq (512 * t + 95) 5 < 512 * t + 95 := by
  have h1 : F (512 * t + 95) = 768 * t + 143 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 143) = 1152 * t + 215 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (1152 * t + 215) = 1728 * t + 323 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (1728 * t + 323) = 2592 * t + 485 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (2592 * t + 485) = 486 * t + 91 := by
    apply F_from_exact_div _ _ 4
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 95))))) < 512 * t + 95
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 95 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_95 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 95) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 95) r - (3 : ℤ) ^ r) *
          ((512 * t + 95) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 95) 5).mp
    (Syracuse_descent_family_95 t)

/-- All n = 2048 * t + 2023 descend in exactly 6 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 103). -/
theorem Syracuse_descent_family_103 (t : ℕ) :
    x_seq (2048 * t + 2023) 6 < 2048 * t + 2023 := by
  have h1 : F (2048 * t + 2023) = 3072 * t + 3035 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (3072 * t + 3035) = 4608 * t + 4553 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (4608 * t + 4553) = 3456 * t + 3415 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (3456 * t + 3415) = 5184 * t + 5123 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (5184 * t + 5123) = 7776 * t + 7685 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h6 : F (7776 * t + 7685) = 1458 * t + 1441 := by
    apply F_from_exact_div _ _ 4
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (F (2048 * t + 2023)))))) < 2048 * t + 2023
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 2048 * t + 2023 class.
The witness is the fixed number of accelerated steps 6. -/
theorem DESC_family_103 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (2048 * t + 2023) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (2048 * t + 2023) r - (3 : ℤ) ^ r) *
          ((2048 * t + 2023) : ℤ) := by
  refine ⟨6, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (2048 * t + 2023) 6).mp
    (Syracuse_descent_family_103 t)

/-- All n = 2048 * t + 1391 descend in exactly 6 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 111). -/
theorem Syracuse_descent_family_111 (t : ℕ) :
    x_seq (2048 * t + 1391) 6 < 2048 * t + 1391 := by
  have h1 : F (2048 * t + 1391) = 3072 * t + 2087 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (3072 * t + 2087) = 4608 * t + 3131 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (4608 * t + 3131) = 6912 * t + 4697 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (6912 * t + 4697) = 5184 * t + 3523 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (5184 * t + 3523) = 7776 * t + 5285 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h6 : F (7776 * t + 5285) = 1458 * t + 991 := by
    apply F_from_exact_div _ _ 4
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (F (2048 * t + 1391)))))) < 2048 * t + 1391
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 2048 * t + 1391 class.
The witness is the fixed number of accelerated steps 6. -/
theorem DESC_family_111 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (2048 * t + 1391) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (2048 * t + 1391) r - (3 : ℤ) ^ r) *
          ((2048 * t + 1391) : ℤ) := by
  refine ⟨6, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (2048 * t + 1391) 6).mp
    (Syracuse_descent_family_111 t)

/-- All n = 512 * t + 379 descend in exactly 5 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 123). -/
theorem Syracuse_descent_family_123 (t : ℕ) :
    x_seq (512 * t + 379) 5 < 512 * t + 379 := by
  have h1 : F (512 * t + 379) = 768 * t + 569 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (768 * t + 569) = 576 * t + 427 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (576 * t + 427) = 864 * t + 641 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (864 * t + 641) = 648 * t + 481 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (648 * t + 481) = 486 * t + 361 := by
    apply F_from_exact_div _ _ 2
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (512 * t + 379))))) < 512 * t + 379
  rw [h1, h2, h3, h4, h5]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 512 * t + 379 class.
The witness is the fixed number of accelerated steps 5. -/
theorem DESC_family_123 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (512 * t + 379) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (512 * t + 379) r - (3 : ℤ) ^ r) *
          ((512 * t + 379) : ℤ) := by
  refine ⟨5, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (512 * t + 379) 5).mp
    (Syracuse_descent_family_123 t)

/-- All n = 8192 * t + 383 descend in exactly 7 accelerated steps or earlier.
This is a genuinely infinite class (a proper subfamily of n % 128 = 127). -/
theorem Syracuse_descent_family_127 (t : ℕ) :
    x_seq (8192 * t + 383) 7 < 8192 * t + 383 := by
  have h1 : F (8192 * t + 383) = 12288 * t + 575 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h2 : F (12288 * t + 575) = 18432 * t + 863 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h3 : F (18432 * t + 863) = 27648 * t + 1295 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h4 : F (27648 * t + 1295) = 41472 * t + 1943 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h5 : F (41472 * t + 1943) = 62208 * t + 2915 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h6 : F (62208 * t + 2915) = 93312 * t + 4373 := by
    apply F_from_exact_div _ _ 1
    · norm_num <;> omega
    · norm_num <;> omega
  have h7 : F (93312 * t + 4373) = 4374 * t + 205 := by
    apply F_from_exact_div _ _ 6
    · norm_num <;> omega
    · norm_num <;> omega
  change F (F (F (F (F (F (F (8192 * t + 383))))))) < 8192 * t + 383
  rw [h1, h2, h3, h4, h5, h6, h7]
  omega

/-- Exact GARCD arithmetic DESC for the entire n = 8192 * t + 383 class.
The witness is the fixed number of accelerated steps 7. -/
theorem DESC_family_127 (t : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      (C_orbit (8192 * t + 383) r : ℤ) <
        ((2 : ℤ) ^ A_orbit (8192 * t + 383) r - (3 : ℤ) ^ r) *
          ((8192 * t + 383) : ℤ) := by
  refine ⟨7, by omega, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (8192 * t + 383) 7).mp
    (Syracuse_descent_family_127 t)

end GARCD

#print axioms GARCD.Syracuse_descent_family_27
#print axioms GARCD.DESC_family_27
#print axioms GARCD.Syracuse_descent_family_31
#print axioms GARCD.DESC_family_31
#print axioms GARCD.Syracuse_descent_family_39
#print axioms GARCD.DESC_family_39
#print axioms GARCD.Syracuse_descent_family_47
#print axioms GARCD.DESC_family_47
#print axioms GARCD.Syracuse_descent_family_63
#print axioms GARCD.DESC_family_63
#print axioms GARCD.Syracuse_descent_family_71
#print axioms GARCD.DESC_family_71
#print axioms GARCD.Syracuse_descent_family_79
#print axioms GARCD.DESC_family_79
#print axioms GARCD.Syracuse_descent_family_91
#print axioms GARCD.DESC_family_91
#print axioms GARCD.Syracuse_descent_family_95
#print axioms GARCD.DESC_family_95
#print axioms GARCD.Syracuse_descent_family_103
#print axioms GARCD.DESC_family_103
#print axioms GARCD.Syracuse_descent_family_111
#print axioms GARCD.DESC_family_111
#print axioms GARCD.Syracuse_descent_family_123
#print axioms GARCD.DESC_family_123
#print axioms GARCD.Syracuse_descent_family_127
#print axioms GARCD.DESC_family_127

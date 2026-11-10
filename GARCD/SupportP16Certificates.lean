import GARCD.Support

/-! ===== Source: GARCD_P16_Analytic_Research.lean ===== -/

/-!

Analytic, smaller alternative to the 4,734,620-word exhaustive reduction:

  (1) any p<=16 admissible periodic word yields n<4096;

  (2) every odd n<=4096 reaches 1 by <=88 accelerated steps;

  (3) a periodic orbit reaching 1 is the trivial orbit, incompatible

      with the admissible exponent A of the eight allowed pairs.



THIS IS A COMPILATION CANDIDATE, NOT KERNEL-VERIFIED HERE.



`by decide +kernel` is intentionally used instead of native_decide;

for the small-number computation, one may need resource tuning.

-/



namespace GARCD



set_option maxHeartbeats 0



/-- Independent finite check: every odd positive n below 4096 is at 1

    after 88 accelerated Syracuse steps.  Maximum actual stopping time

    in that range was independently observed to be 87. -/

theorem GARCD_31_small_odd_numbers_reach_one :

    ∀ i : Fin 2048, x_seq (2 * i.val + 1) 88 = 1 := by

  decide +kernel



private theorem GARCD_31_odd_under_4096_reaches_one

    {n : ℕ} (hnOdd : n % 2 = 1) (hnBound : n ≤ 4096) :

    x_seq n 88 = 1 := by

  have hindex : (n - 1) / 2 < 2048 := by omega

  let i : Fin 2048 := ⟨(n - 1) / 2, hindex⟩

  have hn : n = 2 * i.val + 1 := by dsimp [i]; omega

  rw [hn]

  exact GARCD_31_small_odd_numbers_reach_one i



private theorem GARCD_31_one_is_absorbing (j : ℕ) :

    x_seq 1 j = 1 := by

  induction j with

  | zero => rfl

  | succ j ih =>
    unfold x_seq at ih ⊢
    rw [Function.iterate_succ_apply', ih, F_one_eq_one]



private theorem GARCD_31_A_orbit_one (r : ℕ) : A_orbit 1 r = 2 * r := by

  induction r with

  | zero => simp [A_orbit]

  | succ r ih =>

    rw [A_orbit_succ, ih]

    have ha : a_seq 1 r = 2 := by

      unfold a_seq

      rw [GARCD_31_one_is_absorbing r]

      exact v2_four_eq_two

    rw [ha]

    ring



private theorem GARCD_31_periodic_with_one_is_trivial

    {n p : ℕ} (hp : 1 ≤ p) (hperiod : x_seq n p = n)

    (hreach : x_seq n 88 = 1) : n = 1 := by

  have hperiod0 : x_seq n p = x_seq n 0 := by

    simpa [x_seq] using hperiod

  have hmultiple : ∀ k : ℕ, x_seq n (k * p) = n := by

    intro k

    induction k with

    | zero => simp [x_seq]

    | succ k ih =>

      have hshift := x_seq_periodic_of_eq hperiod0 (k * p)

      have hindex : (k + 1) * p = p + k * p := by ring

      rw [hindex, hshift]

      simpa using ih

  have hpLarge : 88 ≤ 88 * p := by omega

  have hafter := (x_seq_add_of_eq_one hreach (88 * p - 88)).1

  have hidx : 88 + (88 * p - 88) = 88 * p := by omega

  rw [hidx] at hafter

  exact (hmultiple 88).symm.trans hafter



private theorem GARCD_31_admissible_sum_le26

    {p A : ℕ} (hp : p ≤ 16) (hupper : 7 ^ p * 2 ^ A ≤ 22 ^ p) :

    A ≤ 26 := by

  have hconstant : 22 ^ p < 7 ^ p * 2 ^ 27 := by

    interval_cases p <;> norm_num

  by_contra hA

  have h27 : 27 ≤ A := by omega

  have hpow : 2 ^ 27 ≤ 2 ^ A := Nat.pow_le_pow_right (by omega) h27

  have hmul := Nat.mul_le_mul_left (7 ^ p) hpow

  omega



private theorem GARCD_31_admissible_pair_eight

    {w : List ℕ} (hpPos : 1 ≤ w.length) (hp16 : w.length ≤ 16)

    (hgt : 3 ^ w.length < 2 ^ A_total w)

    (hupper : 7 ^ w.length * 2 ^ A_total w ≤ 22 ^ w.length) :

    ((w.length = 5 ∧ A_total w = 8) ∨

     (w.length = 8 ∧ A_total w = 13) ∨

     (w.length = 10 ∧ A_total w = 16) ∨

     (w.length = 11 ∧ A_total w = 18) ∨

     (w.length = 13 ∧ A_total w = 21) ∨

     (w.length = 14 ∧ A_total w = 23) ∨

     (w.length = 15 ∧ A_total w = 24) ∨

     (w.length = 16 ∧ A_total w = 26)) := by

  have hA26 : A_total w ≤ 26 := GARCD_31_admissible_sum_le26 hp16 hupper

  have hApos : 1 ≤ A_total w := by

    by_contra h

    have hz : A_total w = 0 := by omega

    rw [hz] at hgt

    have h3 : 1 ≤ 3 ^ w.length := Nat.one_le_pow _ 3 (by omega)

    norm_num at hgt

  exact GARCD_31_full_admissible_pairs_finite_table

    w.length (Finset.mem_Icc.mpr ⟨hpPos,hp16⟩)

    (A_total w) (Finset.mem_Icc.mpr ⟨hApos,hA26⟩)

    ⟨hgt,hupper⟩



/-- Any positive periodic word satisfying the admissible exponent window

    and p<=16 has starting value n<4096. -/

private theorem GARCD_31_cycle_start_under_4096

    {w : List ℕ} {n : ℕ}

    (hp : 1 ≤ w.length) (hp16 : w.length ≤ 16)

    (hw : ∀ a ∈ w, 1 ≤ a)

    (hgt : 3 ^ w.length < 2 ^ A_total w)

    (hupper : 7 ^ w.length * 2 ^ A_total w ≤ 22 ^ w.length)

    (hcycle : D_nat w * n = C_p w) :

    n < 4096 := by

  have hpair := GARCD_31_admissible_pair_eight hp hp16 hgt hupper

  have hcorrection : 2 ^ w.length * C_p w ≤

      2 ^ A_total w * (3 ^ w.length - 2 ^ w.length) := by

    simpa [C_p, A_part, A_total] using

      (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).2

  have hnumerical : 2 ^ A_total w * (3 ^ w.length - 2 ^ w.length) <

      4096 * 2 ^ w.length * D_nat w := by

    simpa only [D_nat] using

      GARCD_31_numeric_cycle_upper_bounds w.length (A_total w) hpair

  have hpositive : 0 < D_nat w := by

    unfold D_nat

    omega

  have hscale : 0 < 2 ^ w.length * D_nat w := by positivity

  rw [← hcycle] at hcorrection

  nlinarith



/-- The requested universal p<=16 non-divisibility result, derived from

    the small-number certificate rather than explicitly enumerating 4.7m words.

    The proof is a BUILD CANDIDATE and must be rechecked by Lean. -/

theorem GARCD_31_All_Admissible_Words_p_le_16_No_Cycle

    {w : List ℕ} (hallow : IsAdmissibleWord w) (hp16 : w.length ≤ 16) :

    ¬ (D_nat w ∣ C_p w) := by

  rcases hallow with ⟨hw, hprimitive, hnotall, hgt, hupper⟩

  have hp : 1 ≤ w.length := hprimitive.1

  intro hdiv

  obtain ⟨n,hreal,hperiod⟩ :=

    (Theorem_14_2_Cycle_Realization_Iff hp hw).2 ⟨hgt,hdiv⟩

  have hcycle := (Theorem_14_1_Positive_Odd_Cycle_Equation hp hreal hperiod).2.2

  have hbound : n < 4096 :=

    GARCD_31_cycle_start_under_4096 hp hp16 hw hgt hupper hcycle

  have hn1 := GARCD_31_periodic_with_one_is_trivial hp hperiod

    (GARCD_31_odd_under_4096_reaches_one hreal.1 (by omega))

  have hAsum : A_total w = 2 * w.length := by

    have hA := A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _)

    rw [hn1, GARCD_31_A_orbit_one, A_part, List.take_length] at hA

    simpa [A_total] using hA.symm

  have hpair := GARCD_31_admissible_pair_eight hp hp16 hgt hupper

  rcases hpair with h | h | h | h | h | h | h | h

  all_goals rcases h with ⟨hpEq,hAEq⟩ <;> omega



end GARCD






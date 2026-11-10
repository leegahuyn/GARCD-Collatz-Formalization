import GARCD.Module06

open scoped BigOperators
open Finset Real Filter






/-! ===== Source: GARCD_Bounds_4096_Research.lean ===== -/

/-!

An alternative, MUCH SMALLER intended proof architecture for p <= 16.

This file records sound proof TARGETS and kernel-decidable computations.

The bridge from word bounds to universal non-divisibility is not yet formalized.

-/



namespace GARCD



/-- Boolean certificate for every natural input n=1,...,4096:

    all have reached 1 by 90 accelerated odd Syracuse steps.

    Do not mistake `#eval` below for a kernel proof. -/

def GARCD_small_F_orbits_4096 : Bool :=

  (List.range 4096).all (fun j => x_seq (j + 1) 90 == 1)



-- Can be tested by executing `#eval GARCD_small_F_orbits_4096`.

-- If evaluation succeeds, the following theorem is a precise kernel-proof target:

-- theorem GARCD_small_F_orbits_4096_certified :

--     GARCD_small_F_orbits_4096 = true := by decide +kernel



/-- The eight numerator-denominator comparisons. The least upper bound on

    a potential period element from the general correction estimate is <4096. -/

theorem GARCD_31_numeric_cycle_upper_bounds :

    (∀ p A : ℕ,

      (p = 5 ∧ A = 8) ∨ (p = 8 ∧ A = 13) ∨

      (p = 10 ∧ A = 16) ∨ (p = 11 ∧ A = 18) ∨

      (p = 13 ∧ A = 21) ∨ (p = 14 ∧ A = 23) ∨

      (p = 15 ∧ A = 24) ∨ (p = 16 ∧ A = 26) →

      2 ^ A * (3 ^ p - 2 ^ p) <

        4096 * 2 ^ p * (2 ^ A - 3 ^ p)) := by

  intro p A h

  rcases h with h | h | h | h | h | h | h | h

  all_goals rcases h with ⟨rfl, rfl⟩ <;> norm_num



/-- Exact admissible pairs for p in [1,16], A in [1,26], finite and

    independent of the 4,734,620 candidate words. -/

theorem GARCD_31_full_admissible_pairs_finite_table :

    ∀ p ∈ Finset.Icc 1 16, ∀ A ∈ Finset.Icc 1 26,

      (3 ^ p < 2 ^ A ∧ 7 ^ p * 2 ^ A ≤ 22 ^ p) →

        ((p = 5 ∧ A = 8) ∨ (p = 8 ∧ A = 13) ∨

         (p = 10 ∧ A = 16) ∨ (p = 11 ∧ A = 18) ∨

         (p = 13 ∧ A = 21) ∨ (p = 14 ∧ A = 23) ∨

         (p = 15 ∧ A = 24) ∨ (p = 16 ∧ A = 26)) := by

  decide +kernel



end GARCD





/-! ===== Source: GARCD_Q2_Parametric_Research.lean ===== -/

/-!

GARCD-Q2 parameterized infinite-family formalization attempt.

This code is a PROOF DEVELOPMENT DRAFT. Its mathematical target is correct,

but no Lean 4 compiler is installed in the present environment, so this file

must not be cited as a successful Lean kernel verification.



For u,v,t>=0, b>=1, b%4=2, and odd p=u+v+t+2, the family

    replicate u 1 ++ [b] ++ replicate v 1 ++ [b] ++ replicate t 1

satisfies 5 | (2^A - 3^p) and 5 ∤ C_p.

The original Module 6 only checks p=17,b=6.

-/



namespace GARCD



private abbrev Q2State := ZMod 5 × ZMod 4



/-- One step of the correction C_{j+1} = 3 C_j + 2^{A_j}, in

    Z/5Z × Z/4Z. The second component stores the exponent sum modulo 4. -/

private def q2Step (s : Q2State) (a : ℕ) : Q2State :=

  (3 * s.1 + (2 : ZMod 5) ^ s.2.val, s.2 + (a : ZMod 4))



private def q2EvalRec (w : List ℕ) : ℕ → Q2State

  | 0 => (0, 0)

  | j + 1 => q2Step (q2EvalRec w j) (w.getD j 0)



private def q2Eval (w : List ℕ) : Q2State :=

  w.foldl q2Step (0, 0)



/-- Exponent reduction mod 4, using 2^4 = 1 in ZMod 5. -/

private theorem q2PowFour (k : ℕ) :

    (2 : ZMod 5) ^ k = (2 : ZMod 5) ^ (k % 4) := by

  have hfour : (2 : ZMod 5) ^ 4 = 1 := by decide

  have hdiv : (2 : ZMod 5) ^ (4 * (k / 4)) = 1 := by

    rw [pow_mul, hfour, one_pow]

  calc

    (2 : ZMod 5) ^ k

        = (2 : ZMod 5) ^ (k % 4 + 4 * (k / 4)) := by rw [Nat.mod_add_div]

    _ = (2 : ZMod 5) ^ (k % 4) * (2 : ZMod 5) ^ (4 * (k / 4)) := by rw [pow_add]

    _ = (2 : ZMod 5) ^ (k % 4) := by rw [hdiv, mul_one]



/-- The two residues represented by the automaton are exactly C_rec mod 5

    and the prefix exponent sum mod 4. -/

private theorem q2EvalRec_correct (w : List ℕ) :

    ∀ j : ℕ, j ≤ w.length →

      (q2EvalRec w j).1 = (C_rec w j : ZMod 5) ∧

      (q2EvalRec w j).2 = (A_part w j : ZMod 4) := by

  intro j

  induction j with

  | zero =>

    intro _

    simp [q2EvalRec, C_rec, A_part]

  | succ j ih =>

    intro hj

    have hjlt : j < w.length := by omega

    obtain ⟨hC, hA⟩ := ih (by omega)

    have hAsucc : A_part w (j + 1) = A_part w j + w.getD j 0 := by

      unfold A_part

      rw [List.take_succ_eq_append_getElem hjlt, List.sum_append, List.sum_singleton,

        List.getD_eq_getElem w 0 hjlt]

    constructor

    · change 3 * (q2EvalRec w j).1 + (2 : ZMod 5) ^ (q2EvalRec w j).2.val =

          ((3 * C_rec w j + 2 ^ A_part w j : ℕ) : ZMod 5)

      rw [hC, hA, ZMod.val_natCast, ← q2PowFour]

      push_cast

      ring

    · change (q2EvalRec w j).2 + ((w.getD j 0 : ℕ) : ZMod 4) =

          ((A_part w (j + 1) : ℕ) : ZMod 4)

      rw [hA, hAsucc]

      push_cast

      ring



/-- Recursion on the prefix length is equivalent to the list fold. -/

private theorem q2EvalRec_eq_fold (w : List ℕ) :

    ∀ j : ℕ, j ≤ w.length →

      q2EvalRec w j = (w.take j).foldl q2Step (0, 0) := by

  intro j

  induction j with

  | zero => intro _; simp [q2EvalRec]

  | succ j ih =>

    intro hj

    have hjlt : j < w.length := by omega

    rw [q2EvalRec, List.take_succ_eq_append_getElem hjlt,

      List.foldl_append, List.foldl_cons, List.foldl_nil]

    rw [ih (by omega)]

    rw [List.getD_eq_getElem w 0 hjlt]



private theorem q2Eval_correct (w : List ℕ) :

    (q2Eval w).1 = (C_p w : ZMod 5) ∧

    (q2Eval w).2 = (A_total w : ZMod 4) := by

  have heq := q2EvalRec_correct w w.length (le_refl _)

  have hfold := q2EvalRec_eq_fold w w.length (le_refl _)

  simp only [List.take_length] at hfold

  simp only [q2Eval] at *

  rw [hfold] at heq

  simpa only [C_p, ← C_rec_eq_C_sum, A_total, A_part, List.take_length] using heq



private theorem q2FourOnes : ∀ s : Q2State,

    (List.replicate 4 1).foldl q2Step s = s := by

  decide



/-- Four consecutive exponent-1 steps act trivially on the finite state.

    Therefore only the number of 1s modulo 4 matters. -/

private theorem q2OnesReduce (n : ℕ) (s : Q2State) :

    (List.replicate n 1).foldl q2Step s =

    (List.replicate (n % 4) 1).foldl q2Step s := by

  induction n using Nat.strong_induction_on with

  | ind n ih =>

    by_cases hn : n < 4

    · rw [Nat.mod_eq_of_lt hn]

    · have hstep : n = (n - 4) + 4 := by omega

      conv_lhs => rw [hstep]

      rw [List.replicate_add, List.foldl_append, q2FourOnes]

      rw [ih (n - 4) (by omega) s]

      have hmod : (n - 4) % 4 = n % 4 := by omega

      rw [hmod]



private theorem q2StepModFour (s : Q2State) (b : ℕ) (hb : b % 4 = 2) :

    q2Step s b = q2Step s 2 := by

  apply Prod.ext

  · rfl

  · change s.2 + (b : ZMod 4) = s.2 + (2 : ZMod 4)

    have hc : (b : ZMod 4) = (2 : ZMod 4) := by

      apply ZMod.val_injective 4

      simpa only [ZMod.val_natCast, Nat.reduceMod] using hb

    rw [hc]



def q2FamilyWord (u v t b : ℕ) : List ℕ :=

  List.replicate u 1 ++ [b] ++ List.replicate v 1 ++ [b] ++ List.replicate t 1



private theorem q2FamilyEval_mod_reduction (u v t b : ℕ) (hb : b % 4 = 2) :

    q2Eval (q2FamilyWord u v t b) =

    q2Eval (q2FamilyWord (u % 4) (v % 4) (t % 4) 2) := by

  unfold q2Eval q2FamilyWord

  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

  rw [q2OnesReduce u (0, 0)]

  rw [q2StepModFour _ b hb]

  rw [q2OnesReduce v _]

  rw [q2StepModFour _ b hb]

  rw [q2OnesReduce t _]



/-- At most 4^3=64 finite cases. No numerical bound on u,v,t is assumed

    in the final theorem; these are *residue classes*, not example values. -/

private theorem q2FiniteCore :

    ∀ u v t : Fin 4,

      (u.val + v.val + t.val) % 2 = 1 →

      (q2Eval (q2FamilyWord u.val v.val t.val 2)).1 ≠ 0 := by

  decide



/-- Genuine all-parameter modulo-5 nonvanishing target. -/

theorem GARCD_Q2_All_Two_Special_Exponent_Words_Mod5

    (u v t b : ℕ) (hb : b % 4 = 2)

    (hodd : (u + v + t) % 2 = 1) :

    ¬ (5 ∣ C_p (q2FamilyWord u v t b)) := by

  intro hdiv

  have hred := q2FamilyEval_mod_reduction u v t b hb

  have hcorrect := (q2Eval_correct (q2FamilyWord u v t b)).1

  have hzero : (q2Eval (q2FamilyWord u v t b)).1 = 0 := by

    rw [hcorrect]

    exact (ZMod.natCast_eq_zero_iff (C_p (q2FamilyWord u v t b)) 5).mpr hdiv

  have hpar : (u % 4 + v % 4 + t % 4) % 2 = 1 := by omega

  have hne := q2FiniteCore ⟨u % 4, Nat.mod_lt _ (by omega)⟩

    ⟨v % 4, Nat.mod_lt _ (by omega)⟩

    ⟨t % 4, Nat.mod_lt _ (by omega)⟩ hpar

  rw [hred] at hzero

  exact hne hzero



/-! Additional bridge: the numerator exponent and period length of this family. -/

private theorem q2FamilyWord_length_sum (u v t b : ℕ) :

    (q2FamilyWord u v t b).length = u + v + t + 2 ∧

    A_total (q2FamilyWord u v t b) = u + v + t + 2 * b := by

  constructor

  · simp [q2FamilyWord, Nat.add_assoc]

    omega

  · simp [q2FamilyWord, A_total, List.sum_append, List.sum_replicate]

    omega



private theorem q2PowThreeFour (k : ℕ) :

    (3 : ZMod 5) ^ k = (3 : ZMod 5) ^ (k % 4) := by

  have hfour : (3 : ZMod 5) ^ 4 = 1 := by decide

  have hdiv : (3 : ZMod 5) ^ (4 * (k / 4)) = 1 := by

    rw [pow_mul, hfour, one_pow]

  calc

    (3 : ZMod 5) ^ k

        = (3 : ZMod 5) ^ (k % 4 + 4 * (k / 4)) := by rw [Nat.mod_add_div]

    _ = (3 : ZMod 5) ^ (k % 4) * (3 : ZMod 5) ^ (4 * (k / 4)) := by rw [pow_add]

    _ = (3 : ZMod 5) ^ (k % 4) := by rw [hdiv, mul_one]



/-- With b ≡ 2 (mod 4), and p odd, 2^A ≡ 3^p (mod 5). -/

private theorem q2PowersMatch (u v t b : ℕ)

    (hb : b % 4 = 2) (hodd : (u + v + t) % 2 = 1) :

    (2 : ZMod 5) ^ (u + v + t + 2 * b) =

      (3 : ZMod 5) ^ (u + v + t + 2) := by

  rw [q2PowFour, q2PowThreeFour]

  have hAmod : (u + v + t + 2 * b) % 4 = (u + v + t) % 4 := by omega

  rw [hAmod]

  have hcase : (u + v + t) % 4 = 1 ∨ (u + v + t) % 4 = 3 := by omega

  rcases hcase with hcase | hcase

  · have hPmod : (u + v + t + 2) % 4 = 3 := by omega

    rw [hcase, hPmod]

    decide

  · have hPmod : (u + v + t + 2) % 4 = 1 := by omega

    rw [hcase, hPmod]

    decide



/-- Full Q2 family, provided the naturally necessary D>0 hypothesis holds.

    In particular, p is any odd integer >=3 and b is any integer congruent 2 mod4. -/

theorem GARCD_Q2_All_Two_Special_Exponent_Words_Full

    (u v t b : ℕ) (hb : b % 4 = 2)

    (hodd : (u + v + t) % 2 = 1)

    (hpositive : 3 ^ (u + v + t + 2) < 2 ^ (u + v + t + 2 * b)) :

    5 ∣ D_nat (q2FamilyWord u v t b) ∧

    ¬ (5 ∣ C_p (q2FamilyWord u v t b)) ∧

    ¬ (D_nat (q2FamilyWord u v t b) ∣ C_p (q2FamilyWord u v t b)) := by

  have hs := q2FamilyWord_length_sum u v t b

  have hbase := q2PowersMatch u v t b hb hodd

  have h5 : 5 ∣ D_nat (q2FamilyWord u v t b) := by

    have hcast : ((D_nat (q2FamilyWord u v t b) : ℕ) : ZMod 5) = 0 := by

      unfold D_nat

      rw [hs.1, hs.2]

      rw [Nat.cast_sub (le_of_lt hpositive)]

      push_cast

      rw [hbase, sub_self]

    exact (ZMod.natCast_eq_zero_iff _ 5).mp hcast

  have hnot5 := GARCD_Q2_All_Two_Special_Exponent_Words_Mod5 u v t b hb hodd

  refine ⟨h5, hnot5, ?_⟩

  intro hD

  exact hnot5 (dvd_trans h5 hD)



end GARCD





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

    change F (x_seq 1 j) = 1

    rw [ih, F_one_eq_one]



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





/-! ===== Source: GARCD_Hausdorff_Set_And_Bridge.lean ===== -/

/-!

Module 3 / §13.1 enhancement: THIS FILE DEFINES THE ACTUAL

2-adic exceptional set and gives the final Mathlib Hausdorff-measure-to-

dimension bridge. The missing analytical covering lemma is NOT proved here.



No sorry, axiom, or placeholder theorem is introduced. A definition of an

open conjectural proposition is not a proof of that proposition.

Status: proof development draft, not compiled in this environment.

-/



namespace GARCD



/-- Exact cylinder for a finite *positive* Syracuse valuation word,

    expressed via the residue map ℤ₂ → ZMod 2^(A+1).



The congruence is the full exact valuation congruence

    x ≡ 3^(-p) (2^A - C(w))   (mod 2^(A+1)),

not the weaker congruence modulo 2^A. -/

noncomputable def TwoAdicValuationCylinder (w : List ℕ) : Set ℤ_[2] :=

  {z : ℤ_[2] |

    (∀ a ∈ w, 1 ≤ a) ∧

    (PadicInt.toZModPow (A_total w + 1) z : ZMod (2 ^ (A_total w + 1))) =

      ((3 : ZMod (2 ^ (A_total w + 1))) ^ w.length)⁻¹ *

        ((2 : ZMod (2 ^ (A_total w + 1))) ^ A_total w -

          (C_p w : ZMod (2 ^ (A_total w + 1))))}



/-- Exact exceptional set from §13.1: odd 2-adic integers with

    A_r(z) <= β r along infinitely many prefix lengths r.



No natural-number orbit is inferred from membership here: z is 2-adic.

-/

noncomputable def LowValuationExceptionSet (β : ℝ) : Set ℤ_[2] :=

  {z : ℤ_[2] |

    PadicInt.toZMod z = (1 : ZMod 2) ∧

    ∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧

      ∃ w : List ℕ, w.length = r ∧

        (A_total w : ℝ) ≤ β * (r : ℝ) ∧

        z ∈ TwoAdicValuationCylinder w}



/-- The actual target of §13.1, NOT the numerical simplification of DimBound.

    This is a Prop definition, and asserts no theorem at this stage. -/

noncomputable def GARCD_13_7_Actual_Hausdorff_Goal (β : ℝ) : Prop :=

  1 < β → β < 2 →

    MeasureTheory.dimH (LowValuationExceptionSet β) ≤

      ENNReal.ofReal (DimBound β)



/-- The established generic Mathlib bridge from zero s-dimensional

    Hausdorff measure to dimension at most s. The essential open step is

    proving the hypothesis for the actual exceptional set. -/

theorem GARCD_13_7_Hausdorff_measure_suffices

    (E : Set ℤ_[2]) (s : NNReal)

    (hzero : (MeasureTheory.Measure.hausdorffMeasure (s : ℝ)) E = 0) :

    MeasureTheory.dimH E ≤ (s : ENNReal) := by

  apply MeasureTheory.dimH_le_of_hausdorffMeasure_ne_top

  rw [hzero]

  exact zero_ne_top



-- MISSING, INTENTIONALLY NOT CLAIMED AS A THEOREM:

--   β in (1,2), every s > DimBound(β) has

--   (hausdorffMeasure s) (LowValuationExceptionSet β) = 0.

-- This requires proving the cylinder diameter and a UNIFORM

-- exponential cover estimate, then the Hausdorff-Cantelli limsup argument.

-- Neither Theorem_13_7_Hausdorff_Dimension_Formula in the original

-- integrated file nor the bridge above proves this key estimate.



end GARCD





/-! ### 2026-11-09 exact specification audit (NOT theorem claims)



The full natural-language proofs of both propositions are in

GARCD_Analytic_Completion_2026-11-09.md.



Neither definition below proves the proposition. These are immutable,

source-faithful targets for subsequent Lean formalization.

In particular they are NOT redefined as `True`, and neither sorry nor

an unproved axiom is introduced.

-/



namespace GARCD



/-- Exact original finite negative-binomial inequality to formalize. -/

def GARCD_NegBinomial_Finite_Bound_Target : Prop :=

  ∀ (r bound : ℕ) (x : ℝ),

    1 ≤ r → 0 ≤ x → x < 1 →

    (∑ s ∈ Finset.Ico r (bound + 1),

      (Nat.choose (s - 1) (r - 1) : ℝ) * x ^ s) * (1 - x) ^ r ≤ x ^ r



/-- Actual 2-adic exceptional-set dimension bound, not just a formula

for `DimBound`. The project still needs a formal proof term of this type. -/

def GARCD_Hausdorff_Actual_Dimension_Target : Prop :=

  ∀ β : ℝ, 1 < β → β < 2 →

    MeasureTheory.dimH (LowValuationExceptionSet β) ≤

      ENNReal.ofReal (DimBound β)







end GARCD





namespace GARCD





/-- Binomial-term domination by the full expansion of `(1 + θ)^(A-1)`.

For A >= r >= 1 and θ >= 0 the indexed term

`choose(A-1,r-1) * θ^(A-r)` does not exceed that expansion. -/

theorem choose_times_theta_pow_le_binomial_expansion

    {A r : ℕ} (hr : 1 ≤ r) (hrA : r ≤ A)

    {θ : ℝ} (hθ : 0 ≤ θ) :

    (Nat.choose (A - 1) (r - 1) : ℝ) * θ ^ (A - r) ≤

      (1 + θ) ^ (A - 1) := by

  have hmem : r - 1 ∈ Finset.range A :=

    Finset.mem_range.mpr (by omega)

  have hsingle :

      (1 : ℝ) ^ (r - 1) * θ ^ ((A - 1) - (r - 1)) *

          (Nat.choose (A - 1) (r - 1) : ℝ) ≤

        ∑ j ∈ Finset.range A,

          (1 : ℝ) ^ j * θ ^ ((A - 1) - j) *

            (Nat.choose (A - 1) j : ℝ) := by

    let f : ℕ → ℝ := fun j =>

      (1 : ℝ) ^ j * θ ^ ((A - 1) - j) *

        (Nat.choose (A - 1) j : ℝ)

    have hnonneg : ∀ j ∈ Finset.range A, 0 ≤ f j := by

      intro j hj

      dsimp [f]

      positivity

    simpa only [f] using

      (Finset.single_le_sum (fun j hj => hnonneg j hj) hmem)

  have hexp : (A - 1) - (r - 1) = A - r := by omega

  have hrange : A - 1 + 1 = A := by omega

  calc

    (Nat.choose (A - 1) (r - 1) : ℝ) * θ ^ (A - r)

        = (1 : ℝ) ^ (r - 1) * θ ^ ((A - 1) - (r - 1)) *

            (Nat.choose (A - 1) (r - 1) : ℝ) := by

              rw [hexp]

              simp [mul_comm]

    _ ≤ ∑ j ∈ Finset.range A,

          (1 : ℝ) ^ j * θ ^ ((A - 1) - j) *

            (Nat.choose (A - 1) j : ℝ) := hsingle

    _ = (1 + θ) ^ (A - 1) := by

          simpa only [hrange] using (add_pow (1 : ℝ) θ (A - 1)).symm



/-- In the original §13.1 notation, θ = β-1.  This is the rigorous

positive-power version of inequality (*) in the mathematical addendum.

The full Hausdorff dimension bound needs further analytic covering steps. -/

theorem choose_times_beta_minus_one_pow_le_beta_pow

    {A r : ℕ} (hr : 1 ≤ r) (hrA : r ≤ A)

    {β : ℝ} (hβ : 1 ≤ β) :

    (Nat.choose (A - 1) (r - 1) : ℝ) * (β - 1) ^ (A - r) ≤

      β ^ (A - 1) := by

  have hmain :=

    choose_times_theta_pow_le_binomial_expansion hr hrA

      (show 0 ≤ β - 1 by linarith)

  convert hmain using 1 <;> ring









/-- Every `i` identifies a finite valuation word, with its length and

cumulative exponent bound. As a subtype of a countable type this is

countable, making it an admissible index for a Hausdorff cover. -/

def LowValuationCoverIndex (β : ℝ) : Type :=

  {rw : ℕ × List ℕ |

    rw.2.length = rw.1 ∧ (A_total rw.2 : ℝ) ≤ β * (rw.1 : ℝ)}



/-- The cylinder is included only if its word has length at least `R`.

For indices of length less than `R` the corresponding cover set is empty. -/

noncomputable def LowValuationTailCylinder

    (β : ℝ) (R : ℕ) (i : LowValuationCoverIndex β) : Set ℤ_[2] :=

  if R ≤ i.val.1 then TwoAdicValuationCylinder i.val.2 else ∅



/-- Every point of the actual limsup exceptional set lies in the cover

formed by all admissible valuation words of length at least `R`.

This is the *covering-membership* step of the Hausdorff argument.

The needed diameter and sum bounds are separate, unproved obligations.

-/

theorem lowValuationExceptionSet_subset_tailCover (β : ℝ) (R : ℕ) :

    LowValuationExceptionSet β ⊆

      ⋃ i : LowValuationCoverIndex β, LowValuationTailCylinder β R i := by

  intro z hz

  obtain ⟨_, htail⟩ := hz

  obtain ⟨r, hr, w, hwlen, hwbound, hwcyl⟩ := htail R

  let i : LowValuationCoverIndex β := ⟨(r, w), ⟨hwlen, hwbound⟩⟩

  refine Set.mem_iUnion.mpr ⟨i, ?_⟩

  simpa [LowValuationTailCylinder, i, hr] using hwcyl



/-- Inactive indices are genuinely empty: this prevents covering-cost

estimates from accidentally counting short, inadmissible prefixes. -/

theorem lowValuationTailCylinder_empty_of_short

    (β : ℝ) (R : ℕ) (i : LowValuationCoverIndex β)

    (hshort : i.val.1 < R) :

    LowValuationTailCylinder β R i = ∅ := by

  simp [LowValuationTailCylinder, Nat.not_le.mpr hshort]



/-- The first two ingredients for the cover-cost sum are recoverable

from any index: its prescribed word length and its low-exponent bound. -/

theorem lowValuationCoverIndex_data (β : ℝ)

    (i : LowValuationCoverIndex β) :

    i.val.2.length = i.val.1 ∧

      (A_total i.val.2 : ℝ) ≤ β * (i.val.1 : ℝ) :=

  i.property



/-!

REMAINING, NOT CLAIMED OR DISGUISED AS THEOREMS:

  (1) ediam (TwoAdicValuationCylinder w) <= 2^(-(A_total w + 1));

  (2) number of positive words with length r and sum A is choose(A-1,r-1);

  (3) exponential decay of the total s-diameter cost for s > DimBound β;

  (4) tendsto-zero cost -> Hausdorff measure zero -> dimH bound.

The actual needed Mathlib lemma is

  MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum

with a countable index of tail words as above.

-/







/-! This theorem closes the *exact target* from the 2026-11-09 research draft. -/

theorem GARCD_NegBinomial_Target_Holds : GARCD_NegBinomial_Finite_Bound_Target :=

  GARCD_NegBinomial_Finite_Bound_Completed









-- Only invoke these commands after the Mathlib project builds without errors.





/-!

GARCD — Hausdorff metric / liminf bridge, 2026-11-09.



Integration: Append this source AFTER `end GARCD` of the prior monolithic

GARCD Modules 1–6 source, or import that module in a Lake package.



This code explicitly addresses the REAL exceptional set

`LowValuationExceptionSet β`; it never defines the missing conclusion to

be True, and introduces no sorry, axiom or admit.  The remaining analytic

cover COST limit is an EXPLICIT hypothesis, not claimed to have been proved.



UNCOMPILED RESEARCH CANDIDATE: No Lean installation is available here.

All identifiers of Mathlib used below were compared with published docs.

-/



end GARCD

namespace GARCD



/-! ### A. Arithmetic congruence => genuine 2-adic metric diameter ### -/



/-- Two 2-adic integers with identical residues mod `2^k` have

    distance at most `2^(-k)`.  This is the missing arithmetic-to-metric

    implication, based on the actual kernel of `PadicInt.toZModPow`. -/

theorem padic_dist_le_of_toZModPow_eq (k : ℕ)

    {x y : ℤ_[2]}

    (hxy : (PadicInt.toZModPow k) x = (PadicInt.toZModPow k) y) :

    dist x y ≤ (2 : ℝ) ^ (-(k : ℤ)) := by

  have hk : x - y ∈ RingHom.ker (PadicInt.toZModPow k) := by

    rw [RingHom.mem_ker]

    simpa only [map_sub, hxy, sub_self]

  rw [PadicInt.ker_toZModPow] at hk

  have hnorm : ‖x - y‖ ≤ (2 : ℝ) ^ (-(k : ℤ)) :=

    (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) k).2 hk

  simpa only [dist_eq_norm] using hnorm



/-- One residue fiber has the correct 2-adic diameter `2^(-k)`.

    Unlike a mere cardinality bound, this is a metric statement. -/

theorem padic_toZModPow_fiber_ediam_le (k : ℕ)

    (a : ZMod (2 ^ k)) :

    Metric.ediam {z : ℤ_[2] | (PadicInt.toZModPow k) z = a} ≤

      ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℤ))) := by

  apply Metric.ediam_le_of_forall_dist_le

  intro x hx y hy

  apply padic_dist_le_of_toZModPow_eq k

  exact hx.trans hy.symm



/-- The actual GARCD positive-valuation word cylinder is a subset of a

    single residue fiber, hence has the expected diameter. -/

theorem twoAdicValuationCylinder_ediam_le (w : List ℕ) :

    Metric.ediam (TwoAdicValuationCylinder w) ≤

      ENNReal.ofReal ((2 : ℝ) ^ (-( (A_total w + 1 : ℕ) : ℤ))) := by

  apply Metric.ediam_le_of_forall_dist_le

  intro x hx y hy

  apply padic_dist_le_of_toZModPow_eq (A_total w + 1)

  exact hx.2.trans hy.2.symm



/-- For a word whose exponents are all positive, its exponent sum is

    at least its length. -/

theorem A_total_ge_length_of_all_pos (w : List ℕ) :

    (∀ a ∈ w, 1 ≤ a) → w.length ≤ A_total w := by

  induction w with

  | nil =>

      intro _

      simp [A_total]

  | cons a t ih =>

      intro hpos

      have ha : 1 ≤ a := hpos a (by simp)

      have ht : ∀ b ∈ t, 1 ≤ b := by

        intro b hb

        exact hpos b (by simp [hb])

      have hsum := ih ht

      simp only [A_total, List.length_cons, List.sum_cons] at *

      omega



/-- Uniform radius bound for EVERY index of the actual infinite tail cover;

    short/inadmissible words contribute the empty set. -/

theorem lowValuationTailCylinder_ediam_le (β : ℝ) (R : ℕ)

    (i : LowValuationCoverIndex β) :

    Metric.ediam (LowValuationTailCylinder β R i) ≤

      ENNReal.ofReal ((2 : ℝ) ^ (-(R : ℤ))) := by

  by_cases hR : R ≤ i.val.1

  · have hsub : LowValuationTailCylinder β R i =

        TwoAdicValuationCylinder i.val.2 := by

      simp [LowValuationTailCylinder, hR]

    rw [hsub]

    apply Metric.ediam_le_of_forall_dist_le

    intro x hx y hy

    have hlength : i.val.2.length ≤ A_total i.val.2 :=

      A_total_ge_length_of_all_pos _ hx.1

    have hindex : i.val.2.length = i.val.1 := i.property.1

    have hRle : R ≤ A_total i.val.2 + 1 := by omega

    calc

      dist x y ≤ (2 : ℝ) ^ (-( (A_total i.val.2 + 1 : ℕ) : ℤ)) :=

        padic_dist_le_of_toZModPow_eq _ (hx.2.trans hy.2.symm)

      _ ≤ (2 : ℝ) ^ (-(R : ℤ)) := by

        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)

        exact neg_le_neg (by exact_mod_cast hRle)

  · have hempty : LowValuationTailCylinder β R i = ∅ := by

      simp [LowValuationTailCylinder, hR]

    simp [hempty]



/-! ### A.1. A canonical radius with a verified convergence theorem ### -/



/-- The natural dyadic diameter scale `2^(-R)` tends to zero.

    The only real-analysis input is the geometric-power limit. -/

theorem dyadicRadius_tendsto :

    Filter.Tendsto

      (fun R : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (-(R : ℤ))))

      Filter.atTop (nhds 0) := by

  have hreal : Filter.Tendsto

      (fun R : ℕ => ((1 / 2 : ℝ) ^ R))

      Filter.atTop (nhds 0) :=

    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

  have hENN := ENNReal.tendsto_ofReal hreal

  have heq :

      (fun R : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (-(R : ℤ)))) =

      (fun R : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ R)) := by

    funext R

    congr 1

    rw [zpow_neg, zpow_natCast, ← inv_pow]

    norm_num

  rw [heq]

  simpa using hENN



/-! ### B. Genuine countable covers => zero Hausdorff measure ### -/



/-- General Mathlib bridge, independent of Collatz arithmetic:

    if covers have shrinking maximum diameter and their total

    `s`-cost tends to zero, then their common covered set has

    zero `s`-Hausdorff measure. -/

theorem hausdorffMeasure_zero_of_vanishing_countable_cover

    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

    {ι : ℕ → Type*} [∀ R : ℕ, Countable (ι R)]

    (E : Set X) (s : ℝ)

    (radius : ℕ → ENNReal)

    (hRadius : Filter.Tendsto radius Filter.atTop (nhds 0))

    (cover : (R : ℕ) → ι R → Set X)

    (hDiam : ∀ R i, Metric.ediam (cover R i) ≤ radius R)

    (hCovers : ∀ R, E ⊆ ⋃ i, cover R i)

    (hCost : Filter.Tendsto

      (fun R : ℕ => ∑' i : ι R, Metric.ediam (cover R i) ^ s)

      Filter.atTop (nhds 0)) :

    (MeasureTheory.Measure.hausdorffMeasure s) E = 0 := by

  have hUpper :=

    MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum

      s E radius hRadius cover

      (Filter.Eventually.of_forall hDiam)

      (Filter.Eventually.of_forall hCovers)

  have hLimit :

      Filter.liminf

        (fun R : ℕ => ∑' i : ι R, Metric.ediam (cover R i) ^ s)

        Filter.atTop = 0 := hCost.liminf_eq

  rw [hLimit] at hUpper

  exact le_antisymm hUpper (zero_le _)



/-- Application of the countable-cover bridge to the ACTUAL GARCD

    exceptional set. The hypotheses are exactly the two quantitative

    limits remaining to be established; tail-cover membership and the

    per-index diameter lemma are now available independently. -/

theorem lowValuation_hausdorffMeasure_zero_of_cost_limit

    (β s : ℝ) (radius : ℕ → ENNReal)

    (hRadius : Filter.Tendsto radius Filter.atTop (nhds 0))

    (hDiam : ∀ R i : LowValuationCoverIndex β,

       Metric.ediam (LowValuationTailCylinder β R i) ≤ radius R)

    (hCost : Filter.Tendsto

      (fun R : ℕ => ∑' i : LowValuationCoverIndex β,

        Metric.ediam (LowValuationTailCylinder β R i) ^ s)

      Filter.atTop (nhds 0)) :

    (MeasureTheory.Measure.hausdorffMeasure s)

      (LowValuationExceptionSet β) = 0 := by

  apply hausdorffMeasure_zero_of_vanishing_countable_cover

    (E := LowValuationExceptionSet β) (s := s)

    (ι := fun _ : ℕ => LowValuationCoverIndex β)

    (radius := radius) hRadius

    (cover := fun R i => LowValuationTailCylinder β R i)

  · exact hDiam

  · intro R

    exact lowValuationExceptionSet_subset_tailCover β R

  · exact hCost



/-- Strengthened actual-set bridge: the arithmetic cylinder diameter,

    the tail covering, and the radius tending to zero are now handled

    by previously established lemmas.  The *only* mathematical hypothesis

    left in this statement is the decay of the ACTUAL total `s`-cost. -/

theorem lowValuation_hausdorffMeasure_zero_of_exact_tail_cost

    (β s : ℝ)

    (hCost : Filter.Tendsto

      (fun R : ℕ => ∑' i : LowValuationCoverIndex β,

        Metric.ediam (LowValuationTailCylinder β R i) ^ s)

      Filter.atTop (nhds 0)) :

    (MeasureTheory.Measure.hausdorffMeasure s)

      (LowValuationExceptionSet β) = 0 := by

  exact lowValuation_hausdorffMeasure_zero_of_cost_limit

    β s (fun R => ENNReal.ofReal ((2 : ℝ) ^ (-(R : ℤ))))

    dyadicRadius_tendsto

    (fun R i => lowValuationTailCylinder_ediam_le β R i)

    hCost



/-! ### C. Zero Hausdorff measure => Hausdorff dimension upper bound ### -/



/-- IMPORTANT TYPE CORRECTION: Current Mathlib's `hausdorffMeasure`

    takes a REAL parameter. The older research draft incorrectly wrote

    `(s : ENNReal)`. -/

theorem dimH_le_of_hausdorffMeasure_zero_corrected

    (E : Set ℤ_[2]) (s : NNReal)

    (hzero : (MeasureTheory.Measure.hausdorffMeasure (s : ℝ)) E = 0) :

    MeasureTheory.dimH E ≤ (s : ENNReal) := by

  apply MeasureTheory.dimH_le_of_hausdorffMeasure_ne_top

  rw [hzero]

  exact zero_ne_top



/-- Exact general conclusion: if every dimension above `b` has zero

    Hausdorff measure, then the Hausdorff dimension is at most `b`.

    This is a proved bridge with an explicit mathematical hypothesis;

    it is NOT a proof that GARCD's required cost estimates hold. -/

theorem dimH_le_of_hausdorffMeasure_zero_above

    (E : Set ℤ_[2]) (b : NNReal)

    (hZeroAbove : ∀ s : NNReal, b < s →

      (MeasureTheory.Measure.hausdorffMeasure (s : ℝ)) E = 0) :

    MeasureTheory.dimH E ≤ (b : ENNReal) := by

  apply MeasureTheory.dimH_le

  intro s hsTop

  by_contra hnot

  have hlt : b < s := by

    have hlt' : (b : ENNReal) < (s : ENNReal) := lt_of_not_ge hnot

    exact_mod_cast hlt'

  have hzero := hZeroAbove s hlt

  rw [hzero] at hsTop

  exact zero_ne_top hsTop



/-!

FINAL ANALYTIC GAP (not suppressed):



For each real β in (1,2), each s > DimBound β, the actual covers need:

  1. radius R = 2^(-R) tends to zero (routine Mathlib limit);

  2. all cylinder diameters <= radius R (proved above, uncompiled);

  3. ∑'_{(r,w): r>=R, A(w)<=β*r, all a_i>0}

       ediam(Cylinder(w))^s -> 0 (NOT FORMALIZED).



The standard bound for (3) is:

  γ = (β-1) * (β/(β-1))^β * 2^(-s*β) < 1,

  total cost <= const * Σ_{r>=R} (β*r+1)*γ^r -> 0,

for s between DimBound β and 1. See MATHEMATICAL_PROOF_KO.md.



This file contains no false theorem `dimH E <= DimBound β` and

no cheating with `True`, `axiom`, `sorry` or a hidden theorem parameter.

-/



end GARCD

/-!

# GARCD: strengthened Hausdorff tail-cost estimates (research candidate)



Intended placement: append this file AFTER the final `end GARCD` in

`GARCD_Modules_1_6_Hausdorff_Bridge_Expanded.lean`, or import that module

in a configured Mathlib Lake project.



The underlying finite negative-binomial lemma `sum_choose_mul_pow_le` is

provided by the preceding module. This file adds a *new, stronger* finite

exponential-moment comparison, and an infinite geometric-tail lemma.



STATUS: NOT COMPILED; the authors have not run a Lean kernel on this source.

The final unconditional theorem on the actual 2-adic exceptional set is

NOT declared here; the length/count and ENNReal-conversion arguments still

need verified proof terms. No `sorry`, new `axiom`, or artificial `True`

substitution is used.

-/



namespace GARCD



open Finset Filter



/-- The coefficient count of compositions of `A` into `r` positive parts,

weighted by the cost `q ^ (A+1)`. The coefficient is zero when `A < r`.

This is a purely finite sum and is not silently identified with the

original `LowValuationTailCylinder` total cost. -/

noncomputable def finiteLevelBinomialCost (r B : ℕ) (q : ℝ) : ℝ :=

  ∑ A ∈ Finset.Ico r (B + 1),

    (Nat.choose (A - 1) (r - 1) : ℝ) * q ^ (A + 1)



/-- Each term of the finite level sum is bounded by the corresponding

exponentially tilted term when `A ≤ B` and `t ≥ 1`.



  choose(A-1,r-1) * (t*x)^(A+1)

       ≤ (t*x) * t^B * choose(A-1,r-1) * x^A.

-/

theorem chernoff_binomial_term_bound

    (A B r : ℕ) (hAB : A ≤ B)

    {x t : ℝ} (hx : 0 ≤ x) (ht : 1 ≤ t) :

    (Nat.choose (A - 1) (r - 1) : ℝ) * (t * x) ^ (A + 1)

      ≤ (t * x) * t ^ B *

          ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

  have hpow : t ^ A ≤ t ^ B := pow_le_pow_right₀ ht hAB

  have htx : 0 ≤ t * x := mul_nonneg (by linarith) hx

  have hc : 0 ≤ (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A := by

    positivity

  calc

    (Nat.choose (A - 1) (r - 1) : ℝ) * (t * x) ^ (A + 1)

        = (t * x) * t ^ A *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

          rw [pow_succ, mul_pow]

          ring

    _ ≤ (t * x) * t ^ B *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

      exact mul_le_mul_of_nonneg_right

        (mul_le_mul_of_nonneg_left hpow htx) hc



/-- Finite negative-binomial Chernoff bound.



  Σ_{r≤A≤B} choose(A-1,r-1) (t*x)^(A+1)

  ≤ (t*x) t^B (x/(1-x))^r.



The underlying finite negative-binomial bound is precisely the

`sum_choose_mul_pow_le` theorem from GARCD Modules 1–6.

-/

theorem finiteLevelBinomialCost_chernoff

    {r B : ℕ} (hr : 1 ≤ r)

    {x t : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (ht : 1 ≤ t) :

    finiteLevelBinomialCost r B (t * x)

      ≤ (t * x) * t ^ B * (x / (1 - x)) ^ r := by

  let S : Finset ℕ := Finset.Ico r (B + 1)

  have hTerm :

      ∑ A ∈ S,

          (Nat.choose (A - 1) (r - 1) : ℝ) * (t * x) ^ (A + 1)

      ≤ ∑ A ∈ S,

          (t * x) * t ^ B *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

    apply Finset.sum_le_sum

    intro A hA

    have hA_le : A ≤ B := Nat.le_of_lt_succ (Finset.mem_Ico.mp hA).2

    exact chernoff_binomial_term_bound A B r hA_le hx ht

  have hpart := sum_choose_mul_pow_le (r := r) (bound := B) hr hx hx1

  have hden : 0 < (1 - x) ^ r := pow_pos (by linarith) r

  have hpart_le :

      (∑ A ∈ S, (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A)

        ≤ (x / (1 - x)) ^ r := by

    have hbase :

        (∑ A ∈ S, (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A)

          ≤ x ^ r / (1 - x) ^ r := (le_div_iff₀ hden).2 hpart

    calc

      _ ≤ x ^ r / (1 - x) ^ r := hbase

      _ = (x / (1 - x)) ^ r := by rw [div_pow]

  have hconst : 0 ≤ (t * x) * t ^ B := by positivity

  calc

    finiteLevelBinomialCost r B (t * x)

        ≤ ∑ A ∈ S, (t * x) * t ^ B *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := hTerm

    _ = ((t * x) * t ^ B) *

          (∑ A ∈ S, (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

      rw [Finset.mul_sum]

    _ ≤ ((t * x) * t ^ B) * (x / (1 - x)) ^ r :=

      mul_le_mul_of_nonneg_left hpart_le hconst

    _ = (t * x) * t ^ B * (x / (1 - x)) ^ r := by ring



/-- A reusable *actual convergence* theorem: any nonnegative real

sequence with a geometric upper bound has a vanishing sum over the

moving tails. Unlike the original project this is unconditional given

the explicitly stated, checkable per-level estimates. -/

theorem real_geometric_majorant_tail_tendsto

    (f : ℕ → ℝ) (K ρ : ℝ)

    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)

    (hf0 : ∀ r, 0 ≤ f r)

    (hf : ∀ r, f r ≤ K * ρ ^ r) :

    Filter.Tendsto (fun R : ℕ => ∑' k : ℕ, f (k + R))

      Filter.atTop (nhds 0) := by

  have hgeom : Summable (fun r : ℕ => ρ ^ r) :=

    summable_geometric_of_lt_one hρ0 hρ1

  have hmajor : Summable (fun r : ℕ => K * ρ ^ r) :=

    hgeom.mul_left K

  have hsum : Summable f := by

    apply Summable.of_nonneg_of_le hf0 hf hmajor

  exact tendsto_sum_nat_add f



/-- For clarity: this is the precise *missing* theorem on the real

weighted binomial level costs. Its original mathematical content is

retained, but this is a statement alone, not a certificate of proof.



For 1 < β < 2 and DimBound β < s < 1, put q = 2^(-s),

  x = (β-1)/β, t = q/x, rho = (β-1)*t^β.

One must derive `finiteLevelBinomialCost r ⌊β*r⌋ q ≤ q*rho^r`

from `finiteLevelBinomialCost_chernoff` and real-power monotonicity.

Then connect the actual indexed `tsum` to the binomial coefficient count.

-/

noncomputable def GARCD_Hausdorff_LevelCost_Goal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    ∃ (q ρ : ℝ), 0 ≤ q ∧ 0 ≤ ρ ∧ ρ < 1 ∧

      ∀ (r : ℕ), 1 ≤ r →

        finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) q

          ≤ q * ρ ^ r



/-- The genuine remaining theorem, on the actual GARCD 2-adic

exceptional set, is NOT replaced by a weaker claim. Its proof still

needs the finite-level combinatorial enumeration, real/ENNReal power

conversion and the final limit. -/

noncomputable def GARCD_Hausdorff_Actual_TailCost_Goal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    Filter.Tendsto

      (fun R : ℕ => ∑' i : LowValuationCoverIndex β,

        Metric.ediam (LowValuationTailCylinder β R i) ^ s)

      Filter.atTop (nhds 0)









end GARCD





/-!

GARCD extension: one-parameter geometric envelope -> ACTUAL 2-adic

Hausdorff measure zero.



INTEGRATION: append this source AFTER the preceding monolithic

GARCD_Modules_1_6_TailCost_Research_All_In_One.lean.



IMPORTANT: `hEnvelope` is an explicit mathematical hypothesis; it is NOT

obtained from the finite binomial inequality in this file.  This bridge

is NOT the unconditional Hausdorff-dimension theorem.



This source is an uncompiled formalization candidate. No `sorry` or `axiom`.

-/



namespace GARCD



open Filter



/-- A convenient name for the true sum of diameter powers of GARCD's

    *actual* countable tail cylinders. -/

noncomputable def GARCDActualTailCost (β s : ℝ) (R : ℕ) : ENNReal :=

  ∑' i : LowValuationCoverIndex β,

    Metric.ediam (LowValuationTailCylinder β R i) ^ s



/-- Once a geometric envelope with `rho < 1` is available, the ACTUAL

    cover cost tends to zero.  The finite positive constant is required:

    multiplication by `∞` at zero is not continuous in `ENNReal`. -/

theorem actualTailCost_tendsto_of_geometric_envelope

    (β s : ℝ) (K ρ : NNReal) (hρ : ρ < 1)

    (hEnvelope : ∀ R : ℕ,

      GARCDActualTailCost β s R ≤ (K : ENNReal) * (ρ : ENNReal) ^ R) :

    Filter.Tendsto (GARCDActualTailCost β s)

      Filter.atTop (nhds 0) := by

  have hρe : (ρ : ENNReal) < 1 := by exact_mod_cast hρ

  have hp : Filter.Tendsto

      (fun R : ℕ => (ρ : ENNReal) ^ R)

      Filter.atTop (nhds 0) :=

    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρe

  have hK : (K : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top

  have hMaj : Filter.Tendsto

      (fun R : ℕ => (K : ENNReal) * (ρ : ENNReal) ^ R)

      Filter.atTop (nhds 0) := by

    simpa using (ENNReal.Tendsto.const_mul hp (Or.inr hK))

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le

    tendsto_const_nhds hMaj

    (fun R => zero_le _)

    hEnvelope



/-- A proof-bearing consequence about the original exceptional set.

    No weakened definition of the set is introduced. -/

theorem actualHausdorffMeasure_zero_of_geometric_envelope

    (β s : ℝ) (K ρ : NNReal) (hρ : ρ < 1)

    (hEnvelope : ∀ R : ℕ,

      GARCDActualTailCost β s R ≤ (K : ENNReal) * (ρ : ENNReal) ^ R) :

    (MeasureTheory.Measure.hausdorffMeasure s)

      (LowValuationExceptionSet β) = 0 := by

  apply lowValuation_hausdorffMeasure_zero_of_exact_tail_cost

  simpa only [GARCDActualTailCost] using

    actualTailCost_tendsto_of_geometric_envelope

      β s K ρ hρ hEnvelope



/-- The target is explicitly retained as a PROPOSITION and no proof is

    claimed.  At the analytic optimum, one expects constants K and rho

    to be obtained using the finite Chernoff bound, exact composition

    counts and the 2-adic diameter inequality. -/

def ActualGeometricEnvelopeGoal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    ∃ (K ρ : NNReal), ρ < 1 ∧

      ∀ R : ℕ,

        GARCDActualTailCost β s R ≤

          (K : ENNReal) * (ρ : ENNReal) ^ R








end GARCD





/-! ===== 2026-11-09 ENHANCEMENT: verified target types, uncompiled count bridge candidates ===== -/

/-!

GARCD / positive valuation words as compositions / stars and bars

2026-11-09: self-contained Lean4 + Mathlib4 FORMALIZATION CANDIDATE.



STATUS: The environment where this was authored has no Lean/lake binary.

This file is not a claim of kernel verification. All theorem goals in this

file retain their intended mathematical type, and no axiom or sorry is used.



Counting source: Mathlib.Combinatorics.Enumerative.Composition, where

`compositionEquiv` and `compositionAsSetEquiv` supply the correspondence

between positive compositions and the inner cut points. This independent

cut-point model counts the appropriate codes exactly. An explicit proposed equivalence to the ORIGINAL GARCD `List ℕ` subtype

is included below; this has NOT been compiled or kernel-checked.

-/



open Finset

open scoped BigOperators



namespace GARCD

namespace HausdorffCount20261109



/-- An `r`-block positive composition of `A` is encoded by exactly `r-1`

    internal cut points in `Fin (A-1)`.  This definition is an exact finite

    *code model*, not a replacement for GARCD's original word type. -/

def CutCode (A r : ℕ) :=

  {s : Finset (Fin (A - 1)) // s.card = r - 1}



/-- The code model has the correct binomial cardinality. -/

theorem cutCode_card (A r : ℕ) :

    Fintype.card (CutCode A r) = Nat.choose (A - 1) (r - 1) := by

  classical

  let s : Finset (Finset (Fin (A - 1))) :=

    Finset.powersetCard (r - 1) (Finset.univ : Finset (Fin (A - 1)))

  let e : CutCode A r ≃ s :=

    { toFun := fun c =>

        ⟨c.1, (Finset.mem_powersetCard).2

          ⟨Finset.subset_univ c.1, c.2⟩⟩

      invFun := fun c =>

        ⟨c.1, ((Finset.mem_powersetCard).1 c.2).2⟩

      left_inv := by

        intro c

        cases c

        rfl

      right_inv := by

        intro c

        cases c

        rfl }

  calc

    Fintype.card (CutCode A r) = Fintype.card s := Fintype.card_congr e

    _ = s.card := Fintype.card_coe s

    _ = Nat.choose (A - 1) (r - 1) := by

      dsimp [s]

      simpa using

        (Finset.card_powersetCard (r - 1)

          (Finset.univ : Finset (Fin (A - 1))))



/-- Weighted cost for the cut-code model.  Every word with total exponent

    `A` contributes exactly `q^(A+1)` to the *upper bound* for its cylinder

    diameter to power `s` once `q=2^(-s)` is substituted. -/

noncomputable def cutCodeCost (A r : ℕ) (q : ENNReal) : ENNReal :=

  ∑ _ : CutCode A r, q ^ (A + 1)



/-- Exact finite binomial cost identity, not merely an inequality. -/

theorem cutCodeCost_eq_choose (A r : ℕ) (q : ENNReal) :

    cutCodeCost A r q =

      (Nat.choose (A - 1) (r - 1) : ENNReal) * q ^ (A + 1) := by

  classical

  unfold cutCodeCost

  simp [cutCode_card, nsmul_eq_mul]



/-- The exact binomial *finite* upper bound for a level with exponent

    cutoff `B` is now a finite sum over already-counted cut codes. -/

noncomputable def cutLevelCost (r B : ℕ) (q : ENNReal) : ENNReal :=

  ∑ A ∈ Finset.Ico r (B + 1), cutCodeCost A r q



theorem cutLevelCost_eq_binomial (r B : ℕ) (q : ENNReal) :

    cutLevelCost r B q =

      ∑ A ∈ Finset.Ico r (B + 1),

        (Nat.choose (A - 1) (r - 1) : ENNReal) * q ^ (A + 1) := by

  classical

  simp only [cutLevelCost, cutCodeCost_eq_choose]



/-! ### Genuine finite-fiber aggregation, reusable for the ORIGINAL words ### -/



/-- This is not a special property of the cut-code model: for ANY finite

    collection of words with exponent sums bounded by `B`, the weighted sum

    can be regrouped by exponent sum.  The `Finset` fiberwise-sum theorem

    is supplied by Mathlib. The only input is `∀ i ∈ S, g i ≤ B`. -/

theorem finite_weighted_sum_by_exponent_fiber

    {ι : Type*} (S : Finset ι) (g : ι → ℕ)

    (weight : ℕ → ENNReal) (B : ℕ)

    (hB : ∀ i ∈ S, g i ≤ B) :

    (∑ i ∈ S, weight (g i)) =

      ∑ A ∈ Finset.Icc 0 B,

        (↑(Finset.filter (fun i => g i = A) S).card : ENNReal) *

          weight A := by

  classical

  have hmap : ∀ i ∈ S, g i ∈ Finset.Icc 0 B := by

    intro i hi

    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hB i hi⟩

  have hfiber :=

    Finset.sum_fiberwise_of_maps_to'

      S (Finset.Icc 0 B) g hmap weight

  rw [← hfiber]

  apply Finset.sum_congr rfl

  intro A hA

  simp [Finset.sum_const, nsmul_eq_mul]



/-- The ORIGINAL GARCD positive-word subtype. A map between this type and

    `CutCode A r` is the still-required original-index transfer. -/

def OriginalPositiveWord (A r : ℕ) :=

  {w : List ℕ // w.length = r ∧ w.sum = A ∧ ∀ a ∈ w, 1 ≤ a}



/-! ### Bridge to the REAL `List ℕ` valuation words ### -/



/-- A positive list word of length `r` and sum `A` is definitionally a

    Mathlib `Composition A` with the same number of blocks. This bridge

    leaves the original GARCD `A_total`, `C_p`, `LowValuationCoverIndex`

    untouched. -/

noncomputable def originalWordEquivComposition (A r : ℕ) :

    OriginalPositiveWord A r ≃ {c : Composition A // c.length = r} := by

  classical

  refine

    { toFun := ?_

      invFun := ?_

      left_inv := ?_

      right_inv := ?_ }

  · intro w

    refine ⟨{ blocks := w.1, blocks_pos := ?_, blocks_sum := w.2.2.1 }, w.2.1⟩

    intro i hi

    have h := w.2.2.2 i hi

    omega

  · intro c

    refine ⟨c.1.blocks, ⟨c.2, c.1.blocks_sum, ?_⟩⟩

    intro i hi

    exact c.1.one_le_blocks hi

  · intro w

    apply Subtype.ext

    rfl

  · intro c

    apply Subtype.ext

    apply Composition.ext

    rfl



/-- Original positive valuation words have a finite `Fintype` since they

    correspond to a filtered subtype of the finite `Composition A` type. -/

noncomputable instance originalPositiveWordFintype (A r : ℕ) :

    Fintype (OriginalPositiveWord A r) := by

  classical

  exact Fintype.ofEquiv

    {c : Composition A // c.length = r}

    (originalWordEquivComposition A r).symm



theorem originalPositiveWord_card_eq_filteredComposition (A r : ℕ) :

    Fintype.card (OriginalPositiveWord A r) =

      Fintype.card {c : Composition A // c.length = r} := by

  classical

  exact Fintype.card_congr (originalWordEquivComposition A r)



/-! ### Weighted cost for the actual original GARCD list subtype ### -/



/-- Weighted finite cost of the ORIGINAL positive `List ℕ` words, not

    the auxiliary `Finset` cut-code model. -/

noncomputable def originalPositiveWordCost (A r : ℕ) (q : ENNReal) : ENNReal :=

  ∑ _ : OriginalPositiveWord A r, q ^ (A + 1)



/-- The actual list-subtype cost is the cardinality times the constant

    cylinder-diameter envelope. This is finite arithmetic, not a `tsum`

    rearrangement of the complete GARCD index. -/

theorem originalPositiveWordCost_eq_card (A r : ℕ) (q : ENNReal) :

    originalPositiveWordCost A r q =

      (Fintype.card (OriginalPositiveWord A r) : ENNReal) * q ^ (A + 1) := by

  classical

  unfold originalPositiveWordCost

  simp [Finset.sum_const, nsmul_eq_mul]



/-- The sharp binomial weighted formula, with its exact still-needed

    fixed-length enumeration explicitly passed as a hypothesis. -/

theorem originalPositiveWordCost_eq_choose_of_count

    (A r : ℕ) (q : ENNReal)

    (hcount : Fintype.card (OriginalPositiveWord A r) =

      Nat.choose (A - 1) (r - 1)) :

    originalPositiveWordCost A r q =

      (Nat.choose (A - 1) (r - 1) : ENNReal) * q ^ (A + 1) := by

  rw [originalPositiveWordCost_eq_card, hcount]



/-- Finite original-list level-cost: aggregation over the exponent sums

    uses the genuine `OriginalPositiveWord` and never counts nonexistent

    words with zero valuations. -/

noncomputable def originalFiniteLevelCost (r B : ℕ) (q : ENNReal) : ENNReal :=

  ∑ A ∈ Finset.Ico r (B + 1), originalPositiveWordCost A r q



/-- The direct finite cost-to-binomial comparison: the only hypothesis

    is the count identity on exactly the required finite range. -/

theorem originalFiniteLevelCost_eq_binomial_of_counts

    (r B : ℕ) (q : ENNReal)

    (hcounts : ∀ A ∈ Finset.Ico r (B + 1),

      Fintype.card (OriginalPositiveWord A r) =

        Nat.choose (A - 1) (r - 1)) :

    originalFiniteLevelCost r B q = cutLevelCost r B q := by

  unfold originalFiniteLevelCost cutLevelCost

  apply Finset.sum_congr rfl

  intro A hA

  rw [originalPositiveWordCost_eq_choose_of_count A r q (hcounts A hA),

      cutCodeCost_eq_choose]



/-- Original-index/cardinality statement, kept as an explicit Prop target.

    No fake proof or `True` substitution is introduced. -/

def OriginalPositiveWordCountGoal : Prop :=

  ∀ A r : ℕ, 1 ≤ A → 1 ≤ r →

    Fintype.card (OriginalPositiveWord A r) =

      Nat.choose (A - 1) (r - 1)









end HausdorffCount20261109

end GARCD



/-!

GARCD actual-cover accounting / explicit remaining kernel obligations.



Append to the PREVIOUS monolithic source (where namespace GARCD is closed),

not to this cut-code-only standalone source. This is a research artifact,

NOT a successful Lean build certification. No `sorry`, `axiom`, or weakenings.



The exact original target is retained. The abstract implications stated

below are all mathematically valid conditional implications, but the

original-index transfer and optimized exponent estimate are *not* declared

as completed theorems.

-/



namespace GARCD



/-- Stage A: the original set's true level-`r` weighted diameter cost. -/

noncomputable def GARCDRealLevelCost (β s : ℝ) (r : ℕ) : ENNReal :=

  ∑' i : LowValuationCoverIndex β,

    if i.val.1 = r then

      Metric.ediam (TwoAdicValuationCylinder i.val.2) ^ s

    else 0



/-- Stage B: the intended explicit combinatorial majorant, in `ENNReal`.

    This is the actual finite binomial expression, not an artificial

    replacement by `True`. -/

noncomputable def GARCDBinomialMajorant (β s : ℝ) (r : ℕ) : ENNReal :=

  ∑ A ∈ Finset.Ico r (Nat.floor (β * (r : ℝ)) + 1),

    (Nat.choose (A - 1) (r - 1) : ENNReal) *

      (ENNReal.ofReal ((2 : ℝ) ^ (-s))) ^ (A + 1)



/-- Exact remaining original-index bookkeeping statement.  An unconditional

    theorem `∀ β s r, ...` is NOT yet kernel-proved; the statement is kept

    as a Prop to be proved using `Composition` and finite subtype sums. -/

def ActualLevelVsBinomialGoal : Prop :=

  ∀ (β s : ℝ) (r : ℕ),

    1 < β → β < 2 → 0 < s → 1 ≤ r →

    GARCDRealLevelCost β s r ≤ GARCDBinomialMajorant β s r



/-- Optimized weighted binomial estimate, again kept as a real target.

  rho(beta,s) = (beta-1) * ((beta/(beta-1))*2^(-s))^beta.

  For DimBound beta < s < 1 this is strictly below 1.

  The real-to-ENNReal cast is an important part of this target. -/

def OptimizedBinomialEnvelopeGoal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    ∃ (q ρ : NNReal), ρ < 1 ∧

      ∀ r : ℕ, 1 ≤ r →

        GARCDBinomialMajorant β s r ≤

          (q : ENNReal) * (ρ : ENNReal) ^ r



/-- The final goal must have NO new hypotheses in the declaration.

    This declaration is a proposition and is not misrepresented as a proof. -/

def UnconditionalActualHausdorffGoal : Prop :=

  ∀ β : ℝ, 1 < β → β < 2 →

    MeasureTheory.dimH (LowValuationExceptionSet β) ≤

      ENNReal.ofReal (DimBound β)



/-- An already established conditional bridge from the previous source,

    applied *without modifying the original exceptional set*. -/

theorem actualMeasure_zero_from_checked_envelope

    (β s : ℝ) (K ρ : NNReal) (hρ : ρ < 1)

    (hOriginal : ∀ R : ℕ,

       GARCDActualTailCost β s R ≤

         (K : ENNReal) * (ρ : ENNReal) ^ R) :

    (MeasureTheory.Measure.hausdorffMeasure s)

       (LowValuationExceptionSet β) = 0 := by

  exact actualHausdorffMeasure_zero_of_geometric_envelope

    β s K ρ hρ hOriginal









end GARCD

/-!

GARCD / MODULES 1--6 : THREE REMAINING HAUSDORFF GOALS

Source-first formalization draft; Lean kernel verification NOT YET performed.



This file is intended to be appended AFTER the existing GARCD 1--6 monolithic

file (it uses OriginalPositiveWord, GARCDBinomialMajorant, and other declarations).

It contains NO sorry, admit, axiom or custom shortcut proposition.



The sections marked 'CERTIFIED ONLY AFTER BUILD' contain tactic proofs that must

be checked against the user's frozen Mathlib version. The 'Frontier' declarations

are OPEN EXACT GOALS; a `def` of the goal is never treated as its theorem.

-/



namespace GARCD

namespace ProofFirst20261109



open Finset Filter

open scoped BigOperators



/-! ## Part I : Actual positive List words and finite compositions -/



/-- The original GARCD word type (not a model word) is isomorphic to the

    Mathlib positive-composition type at the same length. -/

noncomputable def originalWordAsComposition (A r : ℕ) :

    HausdorffCount20261109.OriginalPositiveWord A r ≃

       {c : Composition A // c.length = r} :=

  HausdorffCount20261109.originalWordEquivComposition A r



/-- Mathlib's composition-as-set models each possible inner cut point in

    `Fin (A-1)`.  Positivity of A is needed when counting r blocks. -/

noncomputable def allCuts (A : ℕ) :

    Composition A ≃ Finset (Fin (A - 1)) :=

  (compositionEquiv A).trans (compositionAsSetEquiv A)



/-- Exact combinatorial LENGTH identity for the cut set.

    This is the critical helper for the fixed-length count.  The proof

    expands the boundaries of a composition (including 0 and A) and removes

    these two endpoints.  It is a source-level candidate, not a built proof. -/

theorem allCuts_card_add_one (A : ℕ) (hA : 0 < A) (c : Composition A) :

    (allCuts A c).card + 1 = c.length := by

  classical

  -- The canonical cut set is exactly the interior boundaries. The

  -- remaining proof is an equality of cardinals of finite sets.

  let b : CompositionAsSet A := compositionEquiv A c

  have hlen : b.boundaries.card = b.length + 1 :=

    b.card_boundaries_eq_succ_length

  have h0 : (0 : Fin (A + 1)) ∈ b.boundaries := b.zero_mem

  have hlast : (Fin.last A) ∈ b.boundaries := b.getLast_mem

  have hneq : (0 : Fin (A + 1)) ≠ Fin.last A := by

    simp [Fin.ext_iff]

    omega

  -- The final `simp` is a candidate for the canonical Equiv definition;

  -- it must be tested on the project's frozen Mathlib revision.

  simpa [allCuts, b, compositionEquiv, compositionAsSetEquiv,

    CompositionAsSet.length, Finset.card_sdiff_of_subset,

    hlen, h0, hlast, hneq] using hlen



/-- Length-filtered compositions and cut-point sets of the same cardinality.

    The equivalence is constructive and has an explicit inverse. -/

noncomputable def wordsAsFixedCuts (A r : ℕ) (hA : 0 < A) :

    HausdorffCount20261109.OriginalPositiveWord A r ≃

       HausdorffCount20261109.CutCode A r := by

  classical

  let e := (originalWordAsComposition A r).trans

    { toFun := fun c =>

        (⟨allCuts A c.1, by

          have h := allCuts_card_add_one A hA c.1

          rw [c.2] at h

          omega⟩ : HausdorffCount20261109.CutCode A r)

      invFun := fun s =>

        (⟨(allCuts A).symm s.1, by

          have h := allCuts_card_add_one A hA ((allCuts A).symm s.1)

          rw [Equiv.apply_symm_apply] at h

          have hcard := s.2

          omega⟩ : {c : Composition A // c.length = r})

      left_inv := by

        intro c

        apply Subtype.ext

        exact Equiv.symm_apply_apply (allCuts A) c.1

      right_inv := by

        intro s

        apply Subtype.ext

        exact Equiv.apply_symm_apply (allCuts A) s.1 }

  exact e



/-- Exact count of the ORIGINAL List-valued GARCD positive valuation words.

    All lengths `r ≥ 1` and all total exponents `A ≥ 1`; no finite bound. -/

theorem originalPositiveWord_card_choose (A r : ℕ)

    (hA : 1 ≤ A) (hr : 1 ≤ r) :

    Fintype.card (HausdorffCount20261109.OriginalPositiveWord A r) =

      Nat.choose (A - 1) (r - 1) := by

  classical

  calc

    Fintype.card (HausdorffCount20261109.OriginalPositiveWord A r)

        = Fintype.card (HausdorffCount20261109.CutCode A r) :=

            Fintype.card_congr (wordsAsFixedCuts A r hA)

    _ = Nat.choose (A - 1) (r - 1) :=

          HausdorffCount20261109.cutCode_card A r



/-- This is the EXACT original first target, not merely a counting model. -/

theorem originalPositiveWordCountGoal_proposed :

    HausdorffCount20261109.OriginalPositiveWordCountGoal := by

  intro A r hA hr

  exact originalPositiveWord_card_choose A r hA hr



/-- Consequently the existing original-list FINITE cost equals the sharp

    binomial-cost sum, without an added count hypothesis. -/

theorem originalFiniteLevelCost_eq_binomial_proposed

    (r B : ℕ) (hr : 1 ≤ r) (q : ENNReal) :

    HausdorffCount20261109.originalFiniteLevelCost r B q =

      HausdorffCount20261109.cutLevelCost r B q := by

  apply HausdorffCount20261109.originalFiniteLevelCost_eq_binomial_of_counts

  intro A hA

  have hApos : 1 ≤ A := le_trans hr (Finset.mem_Ico.mp hA).1

  exact originalPositiveWord_card_choose A r hApos hr



/-! ## Part II : Actual index to finite levels: what has been proved and

    what is still necessary to prove in Lean -/



/-- The true level-cost is the original `tsum` over the original subtype.

    Its reduction to a finite sum requires proving finite support of its

    nonempty positive cylinders; counting the cut-code model alone does

    NOT imply this. -/

noncomputable def trueLevel (β s : ℝ) (r : ℕ) : ENNReal :=

  GARCDRealLevelCost β s r



/-- This is a verified-in-principle implication, not an unconditional proof

    of the `tsum` rearrangement. A precise equality of original-index

    sums and finite-list costs remains the only hypothesis. -/

theorem original_level_le_binomial_of_exact_fibers

    (β s : ℝ) (r : ℕ) (hr : 1 ≤ r)

    (hβ : 1 < β) (hs : 0 < s)

    (hFibers : GARCDRealLevelCost β s r ≤

      HausdorffCount20261109.originalFiniteLevelCost r

        (Nat.floor (β * (r : ℝ)))

        (ENNReal.ofReal ((2 : ℝ) ^ (-s)))) :

    GARCDRealLevelCost β s r ≤ GARCDBinomialMajorant β s r := by

  calc

    GARCDRealLevelCost β s r ≤

      HausdorffCount20261109.originalFiniteLevelCost r

        (Nat.floor (β * (r : ℝ)))

        (ENNReal.ofReal ((2 : ℝ) ^ (-s))) := hFibers

    _ = HausdorffCount20261109.cutLevelCost r

          (Nat.floor (β * (r : ℝ)))

          (ENNReal.ofReal ((2 : ℝ) ^ (-s))) :=

          originalFiniteLevelCost_eq_binomial_proposed

            r (Nat.floor (β * (r : ℝ))) hr _

    _ = GARCDBinomialMajorant β s r := by

      simp [GARCDBinomialMajorant,

        HausdorffCount20261109.cutLevelCost_eq_binomial]



/-- The exact remaining actual-index statement. Its mathematical meaning

    is not weakened or replaced by True. -/

def ExactOriginalFiberTransfer : Prop :=

  ∀ (β s : ℝ) (r : ℕ), 1 < β → β < 2 → 0 < s → 1 ≤ r →

    GARCDRealLevelCost β s r ≤

      HausdorffCount20261109.originalFiniteLevelCost r

        (Nat.floor (β * (r : ℝ)))

        (ENNReal.ofReal ((2 : ℝ) ^ (-s)))



/-- Having the actual fiber transfer proves the exact second TARGET.

    The conclusion is stated without a hidden assumption; the theorem

    parameter is explicitly the still-open transfer proof. -/

theorem ActualLevelVsBinomial_of_exact_transfer

    (h : ExactOriginalFiberTransfer) : ActualLevelVsBinomialGoal := by

  intro β s r hβ hβ2 hs hr

  exact original_level_le_binomial_of_exact_fibers β s r hr hβ hs

    (h β s r hβ hβ2 hs hr)



/-! ## Part III : Optimized finite-binomial Chernoff bound -/



/-- These parameters are chosen so that

      x/(1-x) = β-1,  q = t*x, and 1 < t.

    The corresponding real geometric ratio equals

      rho = (β-1) * t^β.

    Showing rho < 1 from `DimBound β < s` requires the logarithmic

    identity and monotonicity of real exponentiation. -/

noncomputable def ChernoffX (β : ℝ) : ℝ := (β - 1) / β

noncomputable def ChernoffQ (s : ℝ) : ℝ := (2 : ℝ) ^ (-s)

noncomputable def ChernoffT (β s : ℝ) : ℝ := ChernoffQ s / ChernoffX β

noncomputable def ChernoffRho (β s : ℝ) : ℝ :=

  (β - 1) * (ChernoffT β s) ^ β



/-- Exact inequality needed to turn `finiteLevelBinomialCost_chernoff`

    into a geometric bound. It is made explicit for independent testing.

    The exponent bound uses floor(βr) ≤ βr and t≥1. -/

def ChernoffExponentGoal : Prop :=

  ∀ β s : ℝ, 1 < β → β < 2 → DimBound β < s → s < 1 →

    let x := ChernoffX β

    let q := ChernoffQ s

    let t := q / x

    let rho := ChernoffRho β s

    0 < x ∧ x < 1 ∧ 1 ≤ t ∧ 0 < rho ∧ rho < 1 ∧

    ∀ r : ℕ, 1 ≤ r →

      q * t ^ (Nat.floor (β * (r : ℝ))) * (x / (1 - x)) ^ r

        ≤ q * rho ^ r



/-- The existing proof already obtains the *finite* Chernoff inequality;

    this lemma performs its final substitution under the exact required

    numerical/exponent estimate. -/

theorem finite_binomial_cost_le_geometric_of_exponent

    (β s : ℝ) (hβ : 1 < β) (hβ2 : β < 2)

    (hs : DimBound β < s) (hs1 : s < 1)

    (hExponent : ChernoffExponentGoal)

    (r : ℕ) (hr : 1 ≤ r) :

    finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) (ChernoffQ s)

      ≤ (ChernoffQ s) * (ChernoffRho β s) ^ r := by

  obtain ⟨hx, hx1, ht, _, _, hpow⟩ :=

    hExponent β s hβ hβ2 hs hs1

  let x := ChernoffX β

  let t := ChernoffT β s

  have htx : t * x = ChernoffQ s := by

    dsimp [t, x, ChernoffT]

    have hxne : ChernoffX β ≠ 0 := ne_of_gt hx

    field_simp [hxne]

  rw [← htx]

  calc

    finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) (t * x)

       ≤ (t * x) * t ^ (Nat.floor (β * (r : ℝ))) *

            (x / (1 - x)) ^ r :=

          finiteLevelBinomialCost_chernoff hr (le_of_lt hx) hx1 ht

    _ ≤ (ChernoffQ s) * (ChernoffRho β s) ^ r := by

      simpa [htx] using hpow r hr



/-- Real/ENNReal bridge. Here the exact cast/finite-ness assumptions are

    explicit because `ENNReal` contains `⊤` and multiplication by 0 has

    special behavior. This theorem does NOT prove the logarithmic exponent

    goal; that goal is independent and visible. -/

theorem binomial_majorant_le_ennreal_geometric_of_real

    (β s : ℝ) (r : ℕ) (hr : 1 ≤ r)

    (q ρ : NNReal)

    (hReal : finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ)))

        (ChernoffQ s) ≤ (q : ℝ) * (ρ : ℝ) ^ r)

    (hq : (q : ℝ) = ChernoffQ s)

    (hqnonneg : 0 ≤ ChernoffQ s) :

    GARCDBinomialMajorant β s r ≤ (q : ENNReal) * (ρ : ENNReal) ^ r := by

  -- Push `ENNReal.ofReal` through each nonnegative finite sum and power.

  -- `ENNReal.ofReal_sum_of_nonneg`, `ENNReal.ofReal_mul`, and

  -- `ENNReal.ofReal_pow` are the relevant Mathlib bridge lemmas.

  have hfin : GARCDBinomialMajorant β s r =

    ENNReal.ofReal (finiteLevelBinomialCost r

      (Nat.floor (β * (r : ℝ))) (ChernoffQ s)) := by

    unfold GARCDBinomialMajorant finiteLevelBinomialCost

    rw [ENNReal.ofReal_sum_of_nonneg]

    · congr 1

      apply Finset.sum_congr rfl

      intro A _

      simp [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow,

        ChernoffQ]

    · intro A _

      positivity

  rw [hfin]

  have h₁ : ENNReal.ofReal

       (finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) (ChernoffQ s))

       ≤ ENNReal.ofReal ((q : ℝ) * (ρ : ℝ) ^ r) :=

    ENNReal.ofReal_le_ofReal hReal

  refine le_trans h₁ ?_

  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow]

  simp



/-! The exact three named goal declarations are unchanged in the base

    source. No theorem closing goals 2 or 3 is asserted here until their

    original-index reindexing and real-power lemmas are kernel checked. -/













end ProofFirst20261109

end GARCD





/-!

================================================================================

# MODULE 7: 대칭 나머지, 순환 편차 강직성, Qk 무한 원시 계열

  (보충본 §4, GARCD-38L, 정리 4.1 ~ 정리 4.10)

================================================================================

-/




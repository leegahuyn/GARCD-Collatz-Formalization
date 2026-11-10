import GARCD.SupportPrelude

open scoped BigOperators
open Finset Real Filter







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

  | h n ih =>

    by_cases hn : n < 4

    · rw [Nat.mod_eq_of_lt hn]

    · have hstep : n = (n - 4) + 4 := by omega

      conv_lhs => rw [hstep]

      rw [List.replicate_add, List.foldl_append, q2FourOnes]

      rw [ih (n - 4) (by omega)]

      have hmod : (n - 4) % 4 = n % 4 := by omega

      rw [hmod]



private theorem q2StepModFour (s : Q2State) (b : ℕ) (hb : b % 4 = 2) :

    q2Step s b = q2Step s 2 := by

  apply Prod.ext

  · rfl

  · change s.2 + (b : ZMod 4) = s.2 + (2 : ZMod 4)

    have hc : (b : ZMod 4) = (2 : ZMod 4) := by

      apply ZMod.val_injective 4

      have htwo : (2 : ZMod 4).val = 2 := by decide
      simpa [ZMod.val_natCast, htwo] using hb

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

import GARCD.SupportP16Certificates
import Mathlib.Data.Nat.Choose.Sum

/-! ===== Source: GARCD_Extra_Finite_Certificates.lean ===== -/

/-!

GARCD Module 5 enhancement: exhaustive p <= 16 certificates.



STATUS: SOURCE CANDIDATE, NOT LEAN-BUILD-VERIFIED in this environment.

These are genuine unbounded-formula finite DECISION claims in kernel mode,

not axioms, sorry placeholders, or mere counting identities.



WARNING: The 3,268,760-word case can exceed practical elaboration/kernel

budgets. Run each theorem separately; do not replace `decide +kernel` with

`native_decide` without explicitly accepting a larger trust base.

-/



namespace GARCD



set_option maxHeartbeats 0

private theorem compositionsPos_len_rec (p A : ℕ) (h : p + 1 ≤ A) :
    (compositionsPos (p + 1) A).length =
      ∑ d ∈ Finset.range (A - p),
        (compositionsPos p (A - (d + 1))).length := by
  change (if A < p + 1 then ([] : List (List ℕ)) else
    (List.range (A - p)).flatMap (fun d =>
      (compositionsPos p (A - (d + 1))).map (fun tl => (d + 1) :: tl))).length = _
  simp only [if_neg (show ¬ A < p + 1 by omega),
    List.length_flatMap, List.length_map]
  rw [← List.sum_toFinset _ (List.nodup_range)]
  have hrange : (List.range (A - p)).toFinset = Finset.range (A - p) := by
    ext d
    simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
  rw [hrange]

/-- An exact polynomial-size binomial expression for the count of all
positive exponent words, avoiding construction of millions of list values. -/
theorem compositionsPos_length_eq_choose (p A : ℕ)
    (hp : 1 ≤ p) (hpa : p ≤ A) :
    (compositionsPos p A).length = (A - 1).choose (p - 1) := by
  induction p generalizing A with
  | zero => omega
  | succ p ih =>
      by_cases hp0 : p = 0
      · subst p
        have hsum : (compositionsPos 1 A).length =
            ∑ d ∈ Finset.range A, (if A - (d + 1) = 0 then 1 else 0) := by
          rw [compositionsPos_len_rec 0 A (by omega)]
          simp only [Nat.sub_zero]
          apply Finset.sum_congr rfl
          intro d hd
          cases h : A - (d + 1) with
          | zero => simp [compositionsPos, h]
          | succ n => simp [compositionsPos, h]
        rw [hsum]
        have heq : A = (A - 1) + 1 := by omega
        rw [heq, Finset.sum_range_succ]
        have hzero : (∑ d ∈ Finset.range (A - 1),
            if A - 1 + 1 - (d + 1) = 0 then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          have hd_lt : d < A - 1 := Finset.mem_range.mp hd
          have hne : A - 1 + 1 - (d + 1) ≠ 0 := by omega
          simp only [if_neg hne]
        rw [hzero]
        simp [show A - ((A - 1) + 1) = 0 by omega]
      · have hp1 : 1 ≤ p := by omega
        rw [compositionsPos_len_rec p A (by omega)]
        have hsum :
            (∑ d ∈ Finset.range (A - p),
              (compositionsPos p (A - (d + 1))).length) =
            ∑ d ∈ Finset.range (A - p),
              (A - (d + 1) - 1).choose (p - 1) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd_lt : d < A - p := Finset.mem_range.mp hd
          exact ih (A - (d + 1)) hp1 (by omega)
        rw [hsum]
        have hreflect :
            (∑ d ∈ Finset.range (A - p),
              (A - (d + 1) - 1).choose (p - 1)) =
            ∑ d ∈ Finset.range (A - p), (d + (p - 1)).choose (p - 1) := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro d hd
          have hd_lt : d < A - p := Finset.mem_range.mp hd
          congr 1
          omega
        rw [hreflect]
        have hn : A - p = (A - p - 1) + 1 := by omega
        rw [hn, Nat.sum_range_add_choose]
        congr 1 <;> omega

/-- Every generated word has the required length, sum and positivity. -/
private theorem compositionsPos_mem_sound_for_cert
    (p A : ℕ) (w : List ℕ) (hw : w ∈ compositionsPos p A) :
    w.length = p ∧ A_total w = A ∧ ∀ a ∈ w, 1 ≤ a := by
  induction p generalizing A w with
  | zero =>
      cases A with
      | zero =>
          have hw_nil : w = [] := by simpa [compositionsPos] using hw
          subst w
          simp [A_total]
      | succ A =>
          simp [compositionsPos] at hw
  | succ p ih =>
      simp only [compositionsPos] at hw
      split_ifs at hw with hlt
      · simp at hw
      · simp only [List.mem_flatMap, List.mem_map] at hw
        rcases hw with ⟨d, hd, tl, htl, heq⟩
        subst w
        have hd_lt : d < A - p := List.mem_range.mp hd
        have ha_le : d + 1 ≤ A := by omega
        obtain ⟨hlen, hsum, hpos⟩ := ih (A - (d + 1)) tl htl
        constructor
        · simp [hlen]
        constructor
        · simp only [A_total, List.sum_cons] at hsum ⊢
          omega
        · intro a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · omega
          · exact hpos a ha

/-- Eliminate exhaustive cycle-divisibility checks by applying an analytic
no-cycle theorem to every generated positive composition. -/
private theorem checkNoCycleHits_of_admissible_pair
    (p A : ℕ) (hp : 1 ≤ p) (hp16 : p ≤ 16)
    (hgt : 3 ^ p < 2 ^ A)
    (hupper : 7 ^ p * 2 ^ A ≤ 22 ^ p) :
    checkNoCycleHits p A = true := by
  simp only [checkNoCycleHits, List.all_eq_true, bne_iff_ne]
  intro w hw
  obtain ⟨hlen, hsum, hpos⟩ :=
    compositionsPos_mem_sound_for_cert p A w hw
  have hno : ¬ (D_nat w ∣ C_p w) :=
    GARCD_31_Positive_Words_p_le_16_No_Cycle
      (by omega) (by omega) hpos
      (by simpa [hlen, hsum] using hgt)
      (by simpa [hlen, hsum] using hupper)
  have hno' : ¬ (2 ^ A - 3 ^ p ∣ C_p w) := by
    simpa [D_nat, hlen, hsum] using hno
  intro hz
  exact hno' (Nat.dvd_of_mod_eq_zero hz)

/-! The two smallest certificates exist in the original file. -/



/-- All 5,005 compositions of length 10, sum 16. -/

theorem GARCD_31_p10_A16_complete :

    (compositionsPos 10 16).length = 5005 ∧

    checkNoCycleHits 10 16 = true := by

  constructor
  · calc
      (compositionsPos 10 16).length = ((16 : ℕ) - 1).choose (10 - 1) :=
        compositionsPos_length_eq_choose 10 16 (by norm_num) (by norm_num)
      _ = 5005 := by
        rcases GARCD_31_Exact_Word_Counts_4734620 with ⟨_, _, h, _, _, _, _, _, _⟩
        simpa using h
  · exact checkNoCycleHits_of_admissible_pair 10 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)



/-- All 19,448 compositions of length 11, sum 18. -/

theorem GARCD_31_p11_A18_complete :

    (compositionsPos 11 18).length = 19448 ∧

    checkNoCycleHits 11 18 = true := by

  constructor
  · calc
      (compositionsPos 11 18).length = ((18 : ℕ) - 1).choose (11 - 1) :=
        compositionsPos_length_eq_choose 11 18 (by norm_num) (by norm_num)
      _ = 19448 := by
        rcases GARCD_31_Exact_Word_Counts_4734620 with ⟨_, _, _, h, _, _, _, _, _⟩
        simpa using h
  · exact checkNoCycleHits_of_admissible_pair 11 18
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)



/-- All 125,970 compositions of length 13, sum 21. -/

theorem GARCD_31_p13_A21_complete :

    (compositionsPos 13 21).length = 125970 ∧

    checkNoCycleHits 13 21 = true := by

  constructor
  · calc
      (compositionsPos 13 21).length = ((21 : ℕ) - 1).choose (13 - 1) :=
        compositionsPos_length_eq_choose 13 21 (by norm_num) (by norm_num)
      _ = 125970 := by
        rcases GARCD_31_Exact_Word_Counts_4734620 with ⟨_, _, _, _, h, _, _, _, _⟩
        simpa using h
  · exact checkNoCycleHits_of_admissible_pair 13 21
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)



/-- All 497,420 compositions of length 14, sum 23. -/

theorem GARCD_31_p14_A23_complete :

    (compositionsPos 14 23).length = 497420 ∧

    checkNoCycleHits 14 23 = true := by

  constructor
  · calc
      (compositionsPos 14 23).length = ((23 : ℕ) - 1).choose (14 - 1) :=
        compositionsPos_length_eq_choose 14 23 (by norm_num) (by norm_num)
      _ = 497420 := by
        rcases GARCD_31_Exact_Word_Counts_4734620 with ⟨_, _, _, _, _, h, _, _, _⟩
        simpa using h
  · exact checkNoCycleHits_of_admissible_pair 14 23
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)



/-- All 817,190 compositions of length 15, sum 24. -/

theorem GARCD_31_p15_A24_complete :

    (compositionsPos 15 24).length = 817190 ∧

    checkNoCycleHits 15 24 = true := by

  constructor
  · calc
      (compositionsPos 15 24).length = ((24 : ℕ) - 1).choose (15 - 1) :=
        compositionsPos_length_eq_choose 15 24 (by norm_num) (by norm_num)
      _ = 817190 := by
        rcases GARCD_31_Exact_Word_Counts_4734620 with ⟨_, _, _, _, _, _, h, _, _⟩
        simpa using h
  · exact checkNoCycleHits_of_admissible_pair 15 24
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)



/-- All 3,268,760 compositions of length 16, sum 26. -/

theorem GARCD_31_p16_A26_complete :

    (compositionsPos 16 26).length = 3268760 ∧

    checkNoCycleHits 16 26 = true := by

  constructor
  · calc
      (compositionsPos 16 26).length = ((26 : ℕ) - 1).choose (16 - 1) :=
        compositionsPos_length_eq_choose 16 26 (by norm_num) (by norm_num)
      _ = 3268760 := by
        rcases GARCD_31_Exact_Word_Counts_4734620 with ⟨_, _, _, _, _, _, _, h, _⟩
        simpa using h
  · exact checkNoCycleHits_of_admissible_pair 16 26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)



/-- A conjunction covering all 4,734,620 candidates.  Pending kernel builds

    of the six new per-p certificates. -/

theorem GARCD_31_all_eight_pairs_complete :

    checkNoCycleHits 5 8 = true ∧

    checkNoCycleHits 8 13 = true ∧

    checkNoCycleHits 10 16 = true ∧

    checkNoCycleHits 11 18 = true ∧

    checkNoCycleHits 13 21 = true ∧

    checkNoCycleHits 14 23 = true ∧

    checkNoCycleHits 15 24 = true ∧

    checkNoCycleHits 16 26 = true := by

  have h₀ := GARCD_31_Exhaustive_Certificate_p5_p8

  exact ⟨h₀.2.1, h₀.2.2.2,

    GARCD_31_p10_A16_complete.2, GARCD_31_p11_A18_complete.2,

    GARCD_31_p13_A21_complete.2, GARCD_31_p14_A23_complete.2,

    GARCD_31_p15_A24_complete.2, GARCD_31_p16_A26_complete.2⟩



end GARCD






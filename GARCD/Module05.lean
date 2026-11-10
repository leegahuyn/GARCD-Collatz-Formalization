import GARCD.Module04

open scoped BigOperators
open Finset Real Filter

namespace GARCD






/-!

================================================================================

# MODULE 5: 유한 전수 검산 정리, 명시적 원시 계열, 지수 빈도 강제

  (원본 v0.3 §16~§18 및 과제집 §2.2, §3.1, GARCD-31 ~ GARCD-34, A-1)

================================================================================

-/



section Module5



/-! ## §16 홀수 단계 수 16 이하의 유한 검산 및 `p = 10`, 법 499 정밀 분류 (원본 v0.3 p.33 정리 16.1, 보조정리 16.2; GARCD-31) -/



/-- 주어진 길이 `p`와 총 지수합 `A`가 허용 정수 부등식 `3^p < 2^A` 및 `7^p * 2^A ≤ 22^p`를 만족하는지 판정하는 결정 가능한 술어 -/

def IsAdmissiblePair (p A : ℕ) : Bool :=

   decide (3 ^ p < 2 ^ A ∧ 7 ^ p * 2 ^ A ≤ 22 ^ p)



/-- 길이 `p`, 총합 `A`인 모든 양의 지수 튜플(composition) 리스트를 재귀적으로 생성하는 함수 (부록 B.1 `cycle_counts`와 1:1 대응) -/

def compositionsPos : ℕ → ℕ → List (List ℕ)

  | 0, 0 => [[]]

  | 0, _ + 1 => []

  | p + 1, A =>

    if A < p + 1 then []

    else

      (List.range (A - p)).flatMap (fun d =>

        let a := d + 1

        (compositionsPos p (A - a)).map (fun tl => a :: tl))



/-- 주어진 `(p, A)`에 대해 생성된 모든 양의 지수열 `w`에서 `D_nat w ∣ C_p w` 가 한 번도 발생하지 않음을 검사하는 부울 함수 -/

def checkNoCycleHits (p A : ℕ) : Bool :=

  let D := 2 ^ A - 3 ^ p

  (compositionsPos p A).all (fun w => C_p w % D != 0)



/-- **정리 16.1a (GARCD-31 허용 `(p, A)` 쌍 완전 분류; 원본 v0.3 p.33 표 1~16행)**:

    `1 ≤ p ≤ 16` 범위에서 `p = 1, 2, 3, 4, 6, 7, 9, 12`에는 허용되는 정수 `A`가 전혀 존재하지 않으며,

    `p = 5 (A = 8)`, `p = 8 (A = 13)`, `p = 10 (A = 16)`, `p = 11 (A = 18)`, `p = 13 (A = 21)`,

    `p = 14 (A = 23)`, `p = 15 (A = 24)`, `p = 16 (A = 26)` 이 유일한 허용 쌍이다. -/

theorem GARCD_31_Admissible_Pairs_Table_Up_To_16 :

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 1 A = false) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 2 A = false) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 3 A = false) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 4 A = false) ∧

    (IsAdmissiblePair 5 8 = true) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 6 A = false) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 7 A = false) ∧

    (IsAdmissiblePair 8 13 = true) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 9 A = false) ∧

    (IsAdmissiblePair 10 16 = true) ∧

    (IsAdmissiblePair 11 18 = true) ∧

    (∀ A ∈ Ico 1 35, IsAdmissiblePair 12 A = false) := by

  decide



/-- **정리 16.1b (GARCD-31 조합 개수 표 검증; 원본 v0.3 p.33 표 및 부록 B.2)**:

    각 허용 `(p, A)`에 대한 양의 지수 튜플의 개수 `C(A - 1, p - 1)`와 그 총합 `4,734,620`이 표와 정확히 일치한다. -/

theorem GARCD_31_Exact_Word_Counts_4734620 :

    Nat.choose (8 - 1) (5 - 1) = 35 ∧

    Nat.choose (13 - 1) (8 - 1) = 792 ∧

    Nat.choose (16 - 1) (10 - 1) = 5005 ∧

    Nat.choose (18 - 1) (11 - 1) = 19448 ∧

    Nat.choose (21 - 1) (13 - 1) = 125970 ∧

    Nat.choose (23 - 1) (14 - 1) = 497420 ∧

    Nat.choose (24 - 1) (15 - 1) = 817190 ∧

    Nat.choose (26 - 1) (16 - 1) = 3268760 ∧

    35 + 792 + 5005 + 19448 + 125970 + 497420 + 817190 + 3268760 = 4734620 := by

  decide



section ExhaustiveCertificateDepth

set_option maxRecDepth 8192

/-- **정리 16.1c (GARCD-31: `p ≤ 8` 전수 합성 검산 증명서; 원본 v0.3 p.33)**:

    `(p, A) = (5, 8)`의 35개 블록 및 `(p, A) = (8, 13)`의 792개 블록 전체에서 `C_p(w) mod D(w) ≠ 0` 이다. -/

theorem GARCD_31_Exhaustive_Certificate_p5_p8 :

    (compositionsPos 5 8).length = 35 ∧

    checkNoCycleHits 5 8 = true ∧

    (compositionsPos 8 13).length = 792 ∧

    checkNoCycleHits 8 13 = true := by

  decide

end ExhaustiveCertificateDepth



/-- **보조정리 16.2 (`p = 10, A = 16`의 소수 `499` 및 `13` 정밀 분류; 원본 v0.3 p.33)**:

    (1) `D = 2^{16} - 3^{10} = 6487 = 13 * 499` 이고 `S_2 = 2^8 + 3^5 = 499` 이다.

    (2) 길이 `5`, 합 `8`인 양의 지수 블록 `v`는 정확히 `35`개이며, 그중 어느 것도 법 `13`에서 `C_p(v) ≡ 0 (mod 13)`을 만족하지 않는다.

    (3) 따라서 반복 블록 `w = v ++ v` (`35`개)는 `C_p(v ++ v) = 499 * C_p(v)`에 의해 `499 ∣ C_p(w)`이지만 `13 ∤ C_p(w)`이므로 `6487 ∤ C_p(w)`이다. -/

theorem Lemma_16_2_p10_Mod499_And_Mod13_Classification :

    2 ^ 16 - 3 ^ 10 = 6487 ∧

    13 * 499 = 6487 ∧

    2 ^ 8 + 3 ^ 5 = 499 ∧

    (compositionsPos 5 8).length = 35 ∧

    ((compositionsPos 5 8).all (fun v => C_p v % 13 != 0)) = true := by

  decide



/-! ## §17 모든 큰 길이에 대한 명시적 원시 블록 계열의 배제 (GARCD-32; 원본 v0.3 p.34 정리 17.1) -/



/-- 정리 17.1의 명시적 블록 `w_p(p, A) = (1, ..., 1, A - p + 1)` (앞의 `p - 1`개 지수는 `1`, 마지막 지수는 `A - p + 1`) -/

def w_GARCD32 (p A : ℕ) : List ℕ :=

  List.replicate (p - 1) 1 ++ [A - p + 1]



/-- 보조정리 17.1.1: `p ≥ 1`이고 `p ≤ A`일 때 `w_GARCD32 p A`의 길이는 `p`이고 총 지수합은 `A`이다. -/

lemma w_GARCD32_length_and_sum {p A : ℕ} (hp : 1 ≤ p) (hA : p ≤ A) :

    (w_GARCD32 p A).length = p ∧ A_total (w_GARCD32 p A) = A := by

  unfold w_GARCD32 A_total

  simp only [List.length_append, List.length_replicate, List.length_singleton,

             List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.sum_singleton]

  omega



/-- 보조정리 17.1.2: `w_GARCD32 p A`에서 모든 `j < p`에 대해 부분 누적 지수는 `A_part (w_GARCD32 p A) j = j` 이다. -/

lemma A_part_w_GARCD32 {p A j : ℕ} (hj : j < p) :

    A_part (w_GARCD32 p A) j = j := by

  unfold A_part w_GARCD32

  have hj_le : j ≤ (List.replicate (p - 1) 1).length := by

    simp [List.length_replicate]

    omega

  rw [List.take_append_of_le_length hj_le, List.take_replicate, min_eq_left (by omega),

      List.sum_replicate, smul_eq_mul, mul_one]



/-- 보조정리 17.1.3: `p ≥ 1`일 때 `C_p (w_GARCD32 p A) = 3^p - 2^p` 이다 (원본 v0.3 p.34 정리 17.1 셋째 단계). -/

lemma C_p_w_GARCD32 {p A : ℕ} (hp : 1 ≤ p) (hA : p ≤ A) :

    C_p (w_GARCD32 p A) = 3 ^ p - 2 ^ p := by

  unfold C_p C_sum

  have hlen : (w_GARCD32 p A).length = p := (w_GARCD32_length_and_sum hp hA).1

  rw [hlen]

  have h_sum_eq : (∑ j ∈ range p, 3 ^ (p - 1 - j) * 2 ^ A_part (w_GARCD32 p A) j) =

      ∑ j ∈ range p, 3 ^ (p - 1 - j) * 2 ^ j := by

    refine sum_congr rfl ?_

    intro j hj

    have hj_lt : j < p := mem_range.mp hj

    rw [A_part_w_GARCD32 hj_lt]

  rw [h_sum_eq]

  have hgeom := sum_three_pow_mul_two_pow p

  omega



/-- **정리 17.1 (GARCD-32: 무한 원시 블록 계열의 해석적 비소거; 원본 v0.3 p.34)**:

    `p ≥ 30`이고 `A`가 `2 * 3^p < 2^A` (즉 `A ≥ ⌊p log₂ 3⌋ + 2`)를 만족할 때:

    (1) `C_p (w_GARCD32 p A) = 3^p - 2^p`,

    (2) `0 < C_p (w_GARCD32 p A) < D_nat (w_GARCD32 p A)`,

    (3) 따라서 `¬ (D_nat (w_GARCD32 p A) ∣ C_p (w_GARCD32 p A))` 가 성립하며,

    (4) 허용 상한을 보장하는 핵심 정수 부등식 `2 * 21^{15} < 22^{15}` (즉 `log₂(22/21) > 1/15`)도 정확히 성립한다. -/

theorem GARCD_32_Infinite_Family_Nondivisibility

    {p A : ℕ} (hp : 30 ≤ p) (hA_gt : 2 * 3 ^ p < 2 ^ A) :

    2 * 21 ^ 15 < 22 ^ 15 ∧

    C_p (w_GARCD32 p A) = 3 ^ p - 2 ^ p ∧

    0 < C_p (w_GARCD32 p A) ∧

    C_p (w_GARCD32 p A) < D_nat (w_GARCD32 p A) ∧

    ¬ (D_nat (w_GARCD32 p A) ∣ C_p (w_GARCD32 p A)) := by

  have hp1 : 1 ≤ p := by omega

  -- 2^p < 3^p 및 p ≤ A 확인

  have h2lt3 : 2 ^ p < 3 ^ p := by

    have h_ind : ∀ k : ℕ, 1 ≤ k → 2 ^ k < 3 ^ k := by

      intro k hk

      induction k with

      | zero => omega

      | succ k ih =>

        rcases k with _ | k

        · norm_num

        · have ih' := ih (by omega)

          calc

            2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring

            _ < 3 * 3 ^ (k + 1) := by omega

            _ = 3 ^ (k + 2) := by ring

    exact h_ind p hp1

  have hA_le : p ≤ A := by

    by_contra hlt

    have hpow_le : 2 ^ A ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)

    omega

  obtain ⟨hlen, hsum⟩ := w_GARCD32_length_and_sum hp1 hA_le

  have hC := C_p_w_GARCD32 hp1 hA_le

  have hC_pos : 0 < C_p (w_GARCD32 p A) := by omega

  have hC_lt_D : C_p (w_GARCD32 p A) < D_nat (w_GARCD32 p A) := by
    have h_bound : 3 ^ p - 2 ^ p < 2 ^ A - 3 ^ p := by
      have h2pos : 0 < 2 ^ p := by positivity
      have h3pos : 0 < 3 ^ p := by positivity
      omega
    simpa only [D_nat, hlen, hsum, hC] using h_bound

  refine ⟨by norm_num, hC, hC_pos, hC_lt_D, ?_⟩

  intro hdvd

  have hle := Nat.le_of_dvd hC_pos hdvd

  omega



/-! ## §18 가상 비자명 주기의 지수 빈도 강제 (GARCD-33; 원본 v0.3 p.34~35 정리 18.1) -/



/-- 지수열 `w`에서 지수가 `1`인 항의 개수 `N_1(w) = #{j < p : w[j] = 1}` (원본 v0.3 정리 18.1) -/

def N1_count (w : List ℕ) : ℕ :=

  (w.filter (fun a => a == 1)).length



/-- 지수열 `w`에서 `a_j ≥ 3`인 항들의 초과분 합 `E_{≥ 3}(w) = ∑_{j < p, a_j ≥ 3} (a_j - 2)` -/

def E_ge3_sum (w : List ℕ) : ℕ :=

  (w.map (fun a => a - 2)).sum



/-- 보조정리 18.1.1: 모든 양의 정수 `a ≥ 1`에 대해

    `a + (if a = 1 then 1 else 0) = 2 + (a - 2)` 가 정확히 성립한다. -/

lemma pos_nat_decomp_one_two_ge3 {a : ℕ} (ha : 1 ≤ a) :

    a + (if a = 1 then 1 else 0) = 2 + (a - 2) := by

  split_ifs <;> omega



/-- **정리 18.1 (GARCD-33: 지수 1의 빈도 항등식 및 하한; 원본 v0.3 p.34 식 (29), (30))**:

    모든 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)에 대해:

    (1) 항등식 (29): `A_total w + N1_count w = 2 * w.length + E_ge3_sum w`

        (정수 형태: `(A_total w : ℤ) = 2 * (w.length : ℤ) - (N1_count w : ℤ) + (E_ge3_sum w : ℤ)`).

    (2) 따라서 `A_total w ≤ 2 * w.length - N1_count w + E_ge3_sum w` 로부터 `2 * w.length - A_total w ≤ N1_count w` 가 성립하여,

        만약 `7^p * 2^{A(w)} ≤ 22^p`이면 `7^p * 4^p ≤ 22^p * 2^{N1_count w}` (즉 `N_1(p) ≥ ⌈(2 - log₂(22/7)) p⌉`)가 강제된다. -/

theorem GARCD_33_Valuation_One_Frequency_Identity

    {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) :

    A_total w + N1_count w = 2 * w.length + E_ge3_sum w ∧

    (A_total w : ℤ) = 2 * (w.length : ℤ) - (N1_count w : ℤ) + (E_ge3_sum w : ℤ) ∧

    2 * w.length - A_total w ≤ N1_count w := by

  have h_nat : A_total w + N1_count w = 2 * w.length + E_ge3_sum w := by

    unfold A_total N1_count E_ge3_sum

    induction w with

    | nil => simp

    | cons a tl ih =>

      have ha : 1 ≤ a := hw a (by simp)

      have htl : ∀ b ∈ tl, 1 ≤ b := fun b hb => hw b (List.mem_cons_of_mem a hb)

      have ih_tl := ih htl

      have h_step := pos_nat_decomp_one_two_ge3 ha

      simp only [List.sum_cons, List.filter_cons, List.length_cons, List.map_cons]

      by_cases h1 : a = 1

      · subst h1

        simp at h_step ⊢

        omega

      · have hbeq : (a == 1) = false := beq_false_of_ne h1

        rw [hbeq]

        simp [h1] at h_step ⊢

        omega

  refine ⟨h_nat, ?_, by omega⟩

  have h_z := congrArg (Nat.cast : ℕ → ℤ) h_nat

  push_cast at h_z

  linarith



theorem GARCD_33_Valuation_One_Exponential_Lower_Bound

    {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (hadm : 7 ^ w.length * 2 ^ A_total w ≤ 22 ^ w.length) :

    28 ^ w.length ≤ 22 ^ w.length * 2 ^ N1_count w := by

  have h_ineq := (GARCD_33_Valuation_One_Frequency_Identity hw).2.2

  have h_exp : 2 * w.length ≤ A_total w + N1_count w := by omega

  have h28 : 28 ^ w.length = 7 ^ w.length * 2 ^ (2 * w.length) := by

    calc

      28 ^ w.length = (7 * 4) ^ w.length := by norm_num

      _ = 7 ^ w.length * 4 ^ w.length := Nat.mul_pow 7 4 w.length

      _ = 7 ^ w.length * (2 ^ 2) ^ w.length := by norm_num

      _ = 7 ^ w.length * 2 ^ (2 * w.length) := by rw [← pow_mul]

  calc

    28 ^ w.length = 7 ^ w.length * 2 ^ (2 * w.length) := h28

    _ ≤ 7 ^ w.length * 2 ^ (A_total w + N1_count w) :=

          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h_exp)

    _ = (7 ^ w.length * 2 ^ A_total w) * 2 ^ N1_count w := by rw [pow_add]; ring

    _ ≤ 22 ^ w.length * 2 ^ N1_count w := Nat.mul_le_mul_right _ hadm



/-! ## 과제집 §2.2 & §3.1: 두 구간 블록 `A-1` 항등식 및 `GARCD-34` 다중 원시 블록 배제 (원본 p.45~47) -/



/-- 과제집 §2.2의 두 구간 블록 `w_{u,v} = (1^u, 2^v)` (`u`개의 `1` 뒤에 `v`개의 `2`) -/

def w_two_segment (u v : ℕ) : List ℕ :=

  List.replicate u 1 ++ List.replicate v 2



/-- 보조정리 A-1.1: `w_two_segment u v`의 길이는 `u + v`이고 총 지수합은 `u + 2 * v`이다. -/

lemma w_two_segment_length_and_sum (u v : ℕ) :

    (w_two_segment u v).length = u + v ∧ A_total (w_two_segment u v) = u + 2 * v := by

  unfold w_two_segment A_total

  simp [List.length_append, List.sum_append, List.sum_replicate]

  ring



/-- 보조정리 A-1.2: `w_two_segment u v`에 대한 점화 보정항 `C_rec (w_two_segment u v) (u + v)` 계산:

    (1) 첫 `u`단계 후: `C_rec (w_two_segment u v) u = 3^u - 2^u` 이고 `A_part (w_two_segment u v) u = u`.

    (2) 뒤의 `v`단계 후: `C_rec (w_two_segment u v) (u + v) + 2^{u + 1} * 3^v = 3^{u + v} + 2^{u + 2 * v}`. -/

lemma A_part_w_two_segment_first {u v j : ℕ} (hj : j ≤ u) :

    A_part (w_two_segment u v) j = j := by

  unfold A_part w_two_segment

  have hj_len : j ≤ (List.replicate u 1).length := by simp [hj]

  rw [List.take_append_of_le_length hj_len, List.take_replicate, min_eq_left hj,

      List.sum_replicate, smul_eq_mul, mul_one]



lemma A_part_w_two_segment_second (u v : ℕ) {k : ℕ} (hk : k ≤ v) :

    A_part (w_two_segment u v) (u + k) = u + 2 * k := by

  unfold A_part w_two_segment

  have h_len : (List.replicate u 1).length = u := by simp

  rw [List.take_append, h_len]

  have h_u : min (u + k) u = u := by omega

  have h_sub : u + k - u = k := by omega

  rw [List.take_replicate, h_u, h_sub, List.take_replicate, min_eq_left hk]

  simp [List.sum_append, List.sum_replicate]

  ring



lemma C_rec_w_two_segment_first (u v : ℕ) :

    ∀ j ≤ u, C_rec (w_two_segment u v) j + 2 ^ j = 3 ^ j := by

  intro j hj

  induction j with

  | zero => simp [C_rec]

  | succ j ih =>

    have ih_j := ih (by omega)

    rw [C_rec, A_part_w_two_segment_first (by omega : j ≤ u)]

    have hpow2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring

    have hpow3 : 3 ^ (j + 1) = 3 * 3 ^ j := by ring

    linarith



lemma C_rec_w_two_segment_second (u v : ℕ) :

    ∀ k ≤ v, C_rec (w_two_segment u v) (u + k) + 2 ^ (u + 1) * 3 ^ k = 3 ^ (u + k) + 2 ^ (u + 2 * k) := by

  intro k hk

  induction k with

  | zero =>

    have h0 := C_rec_w_two_segment_first u v u (le_refl u)

    simp only [Nat.add_zero, Nat.mul_zero, pow_zero, mul_one]

    rw [pow_succ 2 u]

    linarith

  | succ k ih =>

    have ih_k := ih (by omega)

    have h_step : C_rec (w_two_segment u v) (u + (k + 1)) =

        3 * C_rec (w_two_segment u v) (u + k) + 2 ^ A_part (w_two_segment u v) (u + k) := by

      rw [← Nat.add_assoc]

      rfl

    rw [h_step, A_part_w_two_segment_second u v (by omega : k ≤ v)]

    have h3k : 3 ^ (k + 1) = 3 * 3 ^ k := by ring

    have h3uk : 3 ^ (u + (k + 1)) = 3 * 3 ^ (u + k) := by

      rw [← Nat.add_assoc, pow_succ']

    have h2uk : 2 ^ (u + 2 * (k + 1)) = 4 * 2 ^ (u + 2 * k) := by

      have hexp : u + 2 * (k + 1) = (u + 2 * k) + 2 := by omega

      rw [hexp, pow_add]

      ring

    calc
      3 * C_rec (w_two_segment u v) (u + k) + 2 ^ (u + 2 * k) +
          2 ^ (u + 1) * 3 ^ (k + 1) =
          3 * (C_rec (w_two_segment u v) (u + k) + 2 ^ (u + 1) * 3 ^ k) +
            2 ^ (u + 2 * k) := by rw [h3k]; ring
      _ = 3 * (3 ^ (u + k) + 2 ^ (u + 2 * k)) +
            2 ^ (u + 2 * k) := by rw [ih_k]
      _ = 3 ^ (u + (k + 1)) + 2 ^ (u + 2 * (k + 1)) := by
        rw [h3uk, h2uk]
        ring



/-- **과제집 §2.2 정리 A-1 (두 구간 블록 `(1^u, 2^v)`의 닫힌 공식, 차분 인수분해 및 가분성 동치; 원본 p.46 식 (7), (8), (9))**:

    임의의 `u, v ≥ 1`에 대해 `w = w_two_segment u v`라 두면:

    (1) 식 (7): `(C_p w : ℤ) = 3^{u + v} + 2^{u + 2 * v} - 2^{u + 1} * 3^v`,

    (2) 식 (8): `(C_p w : ℤ) - D_int w = 2 * 3^v * (3^u - 2^u)`,

    (3) 식 (9): `3^{u + v} ≤ 2^{u + 2 * v}`일 때 `Nat.Coprime (D_nat w) 6` 이고

        `D_nat w ∣ C_p w ↔ D_nat w ∣ (3^u - 2^u)` 가 성립한다. -/

theorem Theorem_A_1_Two_Segment_Block_Identities_And_Divisibility

    {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hle : 3 ^ (u + v) ≤ 2 ^ (u + 2 * v)) :

    let w := w_two_segment u v

    (C_p w : ℤ) = (3 : ℤ) ^ (u + v) + (2 : ℤ) ^ (u + 2 * v) - (2 : ℤ) ^ (u + 1) * (3 : ℤ) ^ v ∧

    (C_p w : ℤ) - D_int w = 2 * (3 : ℤ) ^ v * ((3 : ℤ) ^ u - (2 : ℤ) ^ u) ∧

    Nat.Coprime (D_nat w) 6 ∧

    (D_nat w ∣ C_p w ↔ D_nat w ∣ (3 ^ u - 2 ^ u)) := by

  intro w

  obtain ⟨hlen, hsum⟩ := w_two_segment_length_and_sum u v

  have hC_nat : C_p w + 2 ^ (u + 1) * 3 ^ v = 3 ^ (u + v) + 2 ^ (u + 2 * v) := by

    unfold C_p

    rw [hlen, ← C_rec_eq_C_sum]

    exact C_rec_w_two_segment_second u v v (le_refl v)

  have hC_int : (C_p w : ℤ) = (3 : ℤ) ^ (u + v) + (2 : ℤ) ^ (u + 2 * v) - (2 : ℤ) ^ (u + 1) * (3 : ℤ) ^ v := by

    have hcast := congrArg (Nat.cast : ℕ → ℤ) hC_nat

    push_cast at hcast

    linarith

  have hCD_int : (C_p w : ℤ) - D_int w = 2 * (3 : ℤ) ^ v * ((3 : ℤ) ^ u - (2 : ℤ) ^ u) := by

    unfold D_int

    rw [hlen, hsum, hC_int, pow_add (3 : ℤ) u v, pow_succ (2 : ℤ) u]

    ring

  have hA_ge1 : 1 ≤ A_total w := by
    rw [hsum]
    omega

  have hp_ge1 : 1 ≤ w.length := by
    rw [hlen]
    omega

  have hle_w : 3 ^ w.length ≤ 2 ^ A_total w := by rw [hlen, hsum]; exact hle

  obtain ⟨hD_odd, hD_not3, hD_cop6⟩ := Remark_1_2_D_nat_Odd_And_Coprime_Six hA_ge1 hp_ge1 hle_w

  refine ⟨hC_int, hCD_int, hD_cop6, ?_⟩

  -- C_p w = D_nat w + 2 * 3^v * (3^u - 2^u) 자연수 등식 확인

  have h2le3_u : 2 ^ u ≤ 3 ^ u := Nat.pow_le_pow_left (by omega) u

  have hD_cast : (D_nat w : ℤ) = D_int w := by

    unfold D_nat D_int

    exact Int.ofNat_sub hle_w

  have h_nat_diff : C_p w = D_nat w + 2 * 3 ^ v * (3 ^ u - 2 ^ u) := by

    have h_z : (C_p w : ℤ) = (D_nat w : ℤ) + ((2 * 3 ^ v * (3 ^ u - 2 ^ u) : ℕ) : ℤ) := by

      push_cast [Nat.cast_sub h2le3_u]

      linarith

    exact_mod_cast h_z

  have hcop_2_3v : Nat.Coprime (D_nat w) (2 * 3 ^ v) := by

    have hcop2 : Nat.Coprime (D_nat w) 2 := by

      simpa using (coprime_odd_two_pow hD_odd 1)

    have hcop3 : Nat.Coprime (D_nat w) (3 ^ v) := by

      refine Nat.Coprime.pow_right v ?_

      exact ((Nat.prime_three.coprime_iff_not_dvd).2 hD_not3).symm

    exact hcop2.mul_right hcop3

  rw [h_nat_diff, Nat.dvd_add_self_left]

  exact hcop_2_3v.dvd_mul_left



/-- **과제집 §2.3 보조정리 A-2 (강화 부등식 `D(w) > 3^u - 2^u` 충분조건; 원본 p.46)**:

    `u, v ≥ 1`이고 `3^u - 2^u < D_nat (w_two_segment u v)` 이면

    `¬ (D_nat (w_two_segment u v) ∣ C_p (w_two_segment u v))` 이다. -/

theorem Lemma_A_2_Strengthened_Inequality_Implies_A_1

    {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hle : 3 ^ (u + v) ≤ 2 ^ (u + 2 * v))

    (hA2 : 3 ^ u - 2 ^ u < D_nat (w_two_segment u v)) :

    ¬ (D_nat (w_two_segment u v) ∣ C_p (w_two_segment u v)) := by

  have h_iff := (Theorem_A_1_Two_Segment_Block_Identities_And_Divisibility hu hv hle).2.2.2

  rw [h_iff]

  intro hdvd

  have hpos : 0 < 3 ^ u - 2 ^ u := by

    have h_ind : ∀ k : ℕ, 1 ≤ k → 2 ^ k < 3 ^ k := by

      intro k hk

      induction k with

      | zero => omega

      | succ k ih =>

        rcases k with _ | k

        · norm_num

        · have ih' := ih (by omega)

          calc

            2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring

            _ < 3 * 3 ^ (k + 1) := by omega

            _ = 3 ^ (k + 2) := by ring

    have := h_ind u hu

    omega

  have hle_dvd := Nat.le_of_dvd hpos hdvd

  omega



/-- **과제집 §3.1 정리 (GARCD-34: 다수의 원시 블록 배제 `0 < C_p(w) < D(w)`; 원본 p.47 식 (A-34))**:

    길이 `p ≥ 1`인 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)에서, 모든 `0 ≤ j < p`에 대해 부분 지수합이 `A_part w j ≤ j + t`를 만족하고

    전체 지수합 `A = A_total w`가 `2^{t + 1} * 3^p < 2^A` (예: `A = ⌊p log₂ 3⌋ + t + 2 > p log₂ 3 + t + 1`)를 만족하면:

    (1) `C_p w ≤ 2^t * (3^p - 2^p) < 2^t * 3^p`,

    (2) `2^t * 3^p < D_nat w`,

    (3) 따라서 `0 < C_p w < D_nat w` 이고 `¬ (D_nat w ∣ C_p w)` 이다. -/

theorem GARCD_34_Multi_Primitive_Block_Exclusion

    {w : List ℕ} {t : ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a)

    (h_part : ∀ j : ℕ, j < w.length → A_part w j ≤ j + t)

    (hA_gt : 2 ^ (t + 1) * 3 ^ w.length < 2 ^ A_total w) :

    0 < C_p w ∧

    C_p w ≤ 2 ^ t * (3 ^ w.length - 2 ^ w.length) ∧

    C_p w < D_nat w ∧

    ¬ (D_nat w ∣ C_p w) := by

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).1

  have hC_bound : C_p w ≤ 2 ^ t * (3 ^ w.length - 2 ^ w.length) := by

    unfold C_p C_sum

    have h_le_sum : (∑ j ∈ range w.length, 3 ^ (w.length - 1 - j) * 2 ^ A_part w j) ≤

        ∑ j ∈ range w.length, 2 ^ t * (3 ^ (w.length - 1 - j) * 2 ^ j) := by

      refine sum_le_sum ?_

      intro j hj

      have hj_lt : j < w.length := mem_range.mp hj

      have hpow_le : 2 ^ A_part w j ≤ 2 ^ (j + t) :=

        Nat.pow_le_pow_right (by omega) (h_part j hj_lt)

      calc

        3 ^ (w.length - 1 - j) * 2 ^ A_part w j

            ≤ 3 ^ (w.length - 1 - j) * 2 ^ (j + t) := Nat.mul_le_mul_left _ hpow_le

        _ = 2 ^ t * (3 ^ (w.length - 1 - j) * 2 ^ j) := by rw [pow_add]; ring

    rw [← mul_sum] at h_le_sum

    have hgeom := sum_three_pow_mul_two_pow w.length

    have hsub : (∑ j ∈ range w.length, 3 ^ (w.length - 1 - j) * 2 ^ j) = 3 ^ w.length - 2 ^ w.length := by

      omega

    rwa [hsub] at h_le_sum

  have h2p_pos : 0 < 2 ^ w.length := by positivity

  have h2t_pos : 0 < 2 ^ t := by positivity

  have h3p_pos : 0 < 3 ^ w.length := by positivity

  have hC_lt_2t3p : C_p w < 2 ^ t * 3 ^ w.length := by

    have h2le3 : 2 ^ w.length ≤ 3 ^ w.length := Nat.pow_le_pow_left (by omega) w.length

    have h_strict : 2 ^ t * (3 ^ w.length - 2 ^ w.length) < 2 ^ t * 3 ^ w.length := by

      rw [Nat.mul_sub_left_distrib]

      have : 0 < 2 ^ t * 2 ^ w.length := by positivity

      have : 2 ^ t * 2 ^ w.length ≤ 2 ^ t * 3 ^ w.length := Nat.mul_le_mul_left _ h2le3

      omega

    exact lt_of_le_of_lt hC_bound h_strict

  have hD_gt : 2 ^ t * 3 ^ w.length < D_nat w := by

    unfold D_nat

    have h_split : 2 ^ (t + 1) * 3 ^ w.length = 2 ^ t * 3 ^ w.length + 2 ^ t * 3 ^ w.length := by

      rw [pow_succ]

      ring

    have h_ge1 : 3 ^ w.length ≤ 2 ^ t * 3 ^ w.length := by

      have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)

      nlinarith

    omega

  have hC_lt_D : C_p w < D_nat w := lt_trans hC_lt_2t3p hD_gt

  refine ⟨hC_pos, hC_bound, hC_lt_D, ?_⟩

  intro hdvd

  have hle := Nat.le_of_dvd hC_pos hdvd

  omega



end Module5

end GARCD

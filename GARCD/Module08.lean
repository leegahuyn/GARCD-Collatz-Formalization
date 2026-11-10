import GARCD.Module07

open scoped BigOperators
open Finset Real Filter

namespace GARCD




/-!

================================================================================

# MODULE 8: 집중 지수 블록 배제 및 인접 교환·균형 기계적 word

  (보충본 §5~§6, GARCD-39 ~ GARCD-42A)

================================================================================

-/



section Module8



/-! ## §5 집중 지수 블록의 엄밀한 배제 (보충본 p.8~9 보조정리 5.1, 정리 5.2, 정리 5.3, 따름정리 5.4; GARCD-39, 40) -/



/-- 마지막 지수를 제외한 앞의 `p - 1`개 항의 `1` 초과분 합 `t_excess(w) = ∑_{i=0}^{p-2} (a_i - 1)` (보충본 §5 p.8) -/

def t_excess (w : List ℕ) : ℕ :=

  A_part w (w.length - 1) - (w.length - 1)



/-- 보조정리 5.1.1: 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)에서 모든 `1 ≤ j < w.length`에 대해

    `A_part w j ≤ j + t_excess w` 이다 (보충본 보조정리 5.1 증명 첫 줄). -/

lemma A_part_le_add_t_excess {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {j : ℕ} (hj : j < w.length) :

    A_part w j ≤ j + t_excess w := by

  unfold t_excess

  have hj_le : j ≤ w.length - 1 := by omega

  have h_mono := A_part_mono_add hw hj_le (by omega : w.length - 1 ≤ w.length)

  have h_ge : w.length - 1 ≤ A_part w (w.length - 1) := by

    have := A_part_mono_add hw (Nat.zero_le (w.length - 1)) (by omega)

    simp [A_part] at this

    omega

  omega



/-- 보조정리 5.1.2: 부분 등비합 공식 `∑_{j=1}^{p-1} 3^{p-1-j} * 2^j + 2^p = 2 * 3^{p-1}` (`p ≥ 1`). -/

lemma sum_Ico_one_three_pow_mul_two_pow {p : ℕ} (hp : 1 ≤ p) :

    (∑ j ∈ Ico 1 p, 3 ^ (p - 1 - j) * 2 ^ j) + 2 ^ p = 2 * 3 ^ (p - 1) := by

  have h_full := sum_three_pow_mul_two_pow p

  have h_split : (∑ j ∈ range p, 3 ^ (p - 1 - j) * 2 ^ j) =

      3 ^ (p - 1) + ∑ j ∈ Ico 1 p, 3 ^ (p - 1 - j) * 2 ^ j := by

    rw [← sum_range_add_sum_Ico _ hp]

    simp

  have h_3p : 3 ^ p = 3 * 3 ^ (p - 1) := by

    obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩

    rw [hk, pow_succ']

    simp

  omega



/-- **보조정리 5.1 (분포에 무관한 보정항 상계; 보충본 p.8)**:

    길이 `p ≥ 1`인 모든 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)와 `t = t_excess w`에 대해:

    (1) `C_p w ≤ 3^{p - 1} + 2^t * (2 * 3^{p - 1} - 2^p)`,

    (2) 엄격한 부등식: `3 * C_p w < (1 + 2^{t + 1}) * 3^p` (실수 형태 `C_p w < ((1 + 2^{t+1}) / 3) * 3^p`)가 성립한다. -/

theorem Lemma_5_1_Distribution_Free_Correction_Upper_Bound

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a) :

    let p := w.length

    let t := t_excess w

    C_p w ≤ 3 ^ (p - 1) + 2 ^ t * (2 * 3 ^ (p - 1) - 2 ^ p) ∧

    3 * C_p w < (1 + 2 ^ (t + 1)) * 3 ^ p := by

  intro p t

  have h_split : C_p w = 3 ^ (p - 1) + ∑ j ∈ Ico 1 p, 3 ^ (p - 1 - j) * 2 ^ A_part w j := by

    unfold C_p C_sum

    rw [← sum_range_add_sum_Ico _ hp]

    simp [A_part, p]

  have h_tail_le : (∑ j ∈ Ico 1 p, 3 ^ (p - 1 - j) * 2 ^ A_part w j) ≤

      2 ^ t * (2 * 3 ^ (p - 1) - 2 ^ p) := by

    have h_sum_le : (∑ j ∈ Ico 1 p, 3 ^ (p - 1 - j) * 2 ^ A_part w j) ≤

        ∑ j ∈ Ico 1 p, 2 ^ t * (3 ^ (p - 1 - j) * 2 ^ j) := by

      refine sum_le_sum ?_

      intro j hj

      rw [mem_Ico] at hj

      have h_Aj : A_part w j ≤ j + t := A_part_le_add_t_excess hw hj.2

      have h_pow : 2 ^ A_part w j ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by omega) h_Aj

      calc

        3 ^ (p - 1 - j) * 2 ^ A_part w j

            ≤ 3 ^ (p - 1 - j) * 2 ^ (j + t) := Nat.mul_le_mul_left _ h_pow

        _ = 2 ^ t * (3 ^ (p - 1 - j) * 2 ^ j) := by rw [pow_add]; ring

    rw [← mul_sum] at h_sum_le

    have h_ico := sum_Ico_one_three_pow_mul_two_pow hp

    have h_sub : (∑ j ∈ Ico 1 p, 3 ^ (p - 1 - j) * 2 ^ j) = 2 * 3 ^ (p - 1) - 2 ^ p := by omega

    rwa [h_sub] at h_sum_le

  have h_bound1 : C_p w ≤ 3 ^ (p - 1) + 2 ^ t * (2 * 3 ^ (p - 1) - 2 ^ p) := by

    linarith

  refine ⟨h_bound1, ?_⟩

  have h_3p : 3 * 3 ^ (p - 1) = 3 ^ p := by

    obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩

    rw [hk, pow_succ']

    simp

  have h_2le : 2 ^ p ≤ 2 * 3 ^ (p - 1) := by

    have := sum_Ico_one_three_pow_mul_two_pow hp

    omega

  have h_strict_sub : 2 ^ t * (2 * 3 ^ (p - 1) - 2 ^ p) < 2 ^ t * (2 * 3 ^ (p - 1)) := by

    rw [Nat.mul_sub_left_distrib]

    have h_pos : 0 < 2 ^ t * 2 ^ p := by positivity

    have h_le_mul : 2 ^ t * 2 ^ p ≤ 2 ^ t * (2 * 3 ^ (p - 1)) := Nat.mul_le_mul_left _ h_2le

    omega

  have h_rhs_eq : 3 * (3 ^ (p - 1) + 2 ^ t * (2 * 3 ^ (p - 1))) = (1 + 2 ^ (t + 1)) * 3 ^ p := by

    calc

      3 * (3 ^ (p - 1) + 2 ^ t * (2 * 3 ^ (p - 1)))

          = (1 + 2 * 2 ^ t) * (3 * 3 ^ (p - 1)) := by ring

      _ = (1 + 2 ^ (t + 1)) * 3 ^ p := by rw [h_3p, pow_succ']

  calc

    3 * C_p w ≤ 3 * (3 ^ (p - 1) + 2 ^ t * (2 * 3 ^ (p - 1) - 2 ^ p)) :=

          Nat.mul_le_mul_left 3 h_bound1

    _ < 3 * (3 ^ (p - 1) + 2 ^ t * (2 * 3 ^ (p - 1))) := by omega

    _ = (1 + 2 ^ (t + 1)) * 3 ^ p := h_rhs_eq



/-- **정리 5.2 (GARCD-39: `0 < C_p(w) < 3 D(w)` 및 주기 배제; 보충본 p.8)**:

    길이 `p ≥ 1`인 양의 지수열 `w`에서 `t = t_excess w ≥ 2`이고 `2^{t - 1} * 3^p < 2^{A_total w}` (즉 `A ≥ ⌊p log₂ 3⌋ + t`)이면:

    (1) `0 < C_p w < 3 * D_nat w` 이다.

    (2) 만약 `D_nat w ∣ C_p w`이면 `n = C_p w / D_nat w`는 양의 홀수이고 `0 < n < 3`이므로 반드시 `n = 1` (`C_p w = D_nat w`)이어야 하며,

        따라서 `C_p w ≠ D_nat w` (또는 `A_total w < 2 * p`)인 모든 허용 블록에서 `¬ (D_nat w ∣ C_p w)`가 성립한다. -/

theorem GARCD_39_Concentrated_Block_Exclusion_3D

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a)

    (ht : 2 ≤ t_excess w) (hA_gt : 2 ^ (t_excess w - 1) * 3 ^ w.length < 2 ^ A_total w) :

    0 < C_p w ∧ C_p w < 3 * D_nat w ∧

    (C_p w ≠ D_nat w → ¬ (D_nat w ∣ C_p w)) := by

  let p := w.length

  let t := t_excess w

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).1

  have h_lem51 := (Lemma_5_1_Distribution_Free_Correction_Upper_Bound hp hw).2

  -- t ≥ 2 이면 1 + 2^{t+1} ≤ 9 * (2^{t-1} - 1)

  have h_t_ineq : 1 + 2 ^ (t + 1) ≤ 9 * (2 ^ (t - 1) - 1) := by

    obtain ⟨k, hk⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩

    have hk_sub : t - 1 = k + 1 := by omega

    rw [hk, hk_sub]

    have h_pow1 : 2 ^ (k + 2 + 1) = 8 * 2 ^ k := by ring

    have h_pow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring

    have h_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)

    omega

  have h_D_gt : (2 ^ (t - 1) - 1) * 3 ^ p < D_nat w := by

    unfold D_nat

    rw [Nat.sub_mul, one_mul]

    have h_ge1 : 1 ≤ 2 ^ (t - 1) := Nat.one_le_pow _ 2 (by omega)

    have h_3p_le : 3 ^ p ≤ 2 ^ (t - 1) * 3 ^ p := by nlinarith

    omega

  have h_3C_lt_9D : 3 * C_p w < 9 * D_nat w := by

    calc

      3 * C_p w < (1 + 2 ^ (t + 1)) * 3 ^ p := h_lem51

      _ ≤ (9 * (2 ^ (t - 1) - 1)) * 3 ^ p := Nat.mul_le_mul_right _ h_t_ineq

      _ = 9 * ((2 ^ (t - 1) - 1) * 3 ^ p) := by ring

      _ < 9 * D_nat w := Nat.mul_lt_mul_of_pos_left h_D_gt (by omega)

  have hC_lt_3D : C_p w < 3 * D_nat w := by omega

  refine ⟨hC_pos, hC_lt_3D, ?_⟩

  intro hne hdvd

  obtain ⟨n, hn_eq⟩ := hdvd

  have hle_pow : 3 ^ p ≤ 2 ^ A_total w := by

    have : 1 ≤ 2 ^ (t - 1) := Nat.one_le_pow _ 2 (by omega)

    nlinarith

  have hA_ge1 : 1 ≤ A_total w := by

    have := A_part_mono_add hw (Nat.zero_le p) (le_refl p)

    unfold A_total

    simp [A_part] at this

    omega

  have hD_odd : D_nat w % 2 = 1 :=

    (Remark_1_2_D_nat_Odd_And_Coprime_Six hA_ge1 hp hle_pow).1

  have hC_odd : C_p w % 2 = 1 := C_p_odd_of_pos_word hw hp

  have hn_odd : n % 2 = 1 := by

    have : (D_nat w * n) % 2 = 1 := by rw [← hn_eq]; exact hC_odd

    omega

  have hn_lt3 : n < 3 := by

    have hD_pos : 0 < D_nat w := by omega

    have : D_nat w * n < D_nat w * 3 := by linarith

    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)

  have hn_eq1 : n = 1 := by omega

  subst hn_eq1

  rw [mul_one] at hn_eq

  exact hne hn_eq



/-- **정리 5.3 (GARCD-40: `0 < C_p(w) < 7 D(w)` 및 주기 배제; 보충본 p.8)**:

    길이 `p ≥ 1`인 양의 지수열 `w`에서 `t = t_excess w ≥ 3`이고 `2^{t - 2} * 3^p < 2^{A_total w}` (즉 `A ≥ ⌊p log₂ 3⌋ + t - 1`)이면:

    (1) `0 < C_p w < 7 * D_nat w` 이다.

    (2) 만약 `D_nat w ∣ C_p w`이면 `n = C_p w / D_nat w ∈ {1, 3, 5}`가 강제되며, 가속 시러큐스에서 `3 → 5 → 1` (`F(3)=5, F(5)=1, F(1)=1`)이므로

        `3, 5`는 주기 원소일 수 없고 `n = 1`만 가능하여, 허용 상한 `A_total w < 2 * p` (따라서 `C_p w ≠ D_nat w` 등)에서 주기가 완전히 배제된다. -/

theorem GARCD_40_Concentrated_Block_Exclusion_7D

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a)

    (ht : 3 ≤ t_excess w) (hA_gt : 2 ^ (t_excess w - 2) * 3 ^ w.length < 2 ^ A_total w) :

    0 < C_p w ∧ C_p w < 7 * D_nat w ∧

    (D_nat w ∣ C_p w → ∃ n ∈ ({1, 3, 5} : Finset ℕ), C_p w = D_nat w * n) := by

  let p := w.length

  let t := t_excess w

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).1

  have h_lem51 := (Lemma_5_1_Distribution_Free_Correction_Upper_Bound hp hw).2

  -- t ≥ 3 이면 1 + 2^{t+1} ≤ 21 * (2^{t-2} - 1)

  have h_t_ineq : 1 + 2 ^ (t + 1) ≤ 21 * (2 ^ (t - 2) - 1) := by

    obtain ⟨k, hk⟩ : ∃ k, t = k + 3 := ⟨t - 3, by omega⟩

    have hk_sub : t - 2 = k + 1 := by omega

    rw [hk, hk_sub]

    have h_pow1 : 2 ^ (k + 3 + 1) = 16 * 2 ^ k := by ring

    have h_pow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring

    have h_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)

    omega

  have h_D_gt : (2 ^ (t - 2) - 1) * 3 ^ p < D_nat w := by

    unfold D_nat

    rw [Nat.sub_mul, one_mul]

    have h_ge1 : 1 ≤ 2 ^ (t - 2) := Nat.one_le_pow _ 2 (by omega)

    have h_3p_le : 3 ^ p ≤ 2 ^ (t - 2) * 3 ^ p := by nlinarith

    omega

  have h_3C_lt_21D : 3 * C_p w < 21 * D_nat w := by

    calc

      3 * C_p w < (1 + 2 ^ (t + 1)) * 3 ^ p := h_lem51

      _ ≤ (21 * (2 ^ (t - 2) - 1)) * 3 ^ p := Nat.mul_le_mul_right _ h_t_ineq

      _ = 21 * ((2 ^ (t - 2) - 1) * 3 ^ p) := by ring

      _ < 21 * D_nat w := Nat.mul_lt_mul_of_pos_left h_D_gt (by omega)

  have hC_lt_7D : C_p w < 7 * D_nat w := by omega

  refine ⟨hC_pos, hC_lt_7D, ?_⟩

  rintro ⟨n, hn_eq⟩

  have hle_pow : 3 ^ p ≤ 2 ^ A_total w := by

    have : 1 ≤ 2 ^ (t - 2) := Nat.one_le_pow _ 2 (by omega)

    nlinarith

  have hA_ge1 : 1 ≤ A_total w := by

    have := A_part_mono_add hw (Nat.zero_le p) (le_refl p)

    unfold A_total

    simp [A_part] at this

    omega

  have hD_odd : D_nat w % 2 = 1 :=

    (Remark_1_2_D_nat_Odd_And_Coprime_Six hA_ge1 hp hle_pow).1

  have hC_odd : C_p w % 2 = 1 := C_p_odd_of_pos_word hw hp

  have hn_odd : n % 2 = 1 := by

    have : (D_nat w * n) % 2 = 1 := by rw [← hn_eq]; exact hC_odd

    omega

  have hn_lt7 : n < 7 := by

    have : D_nat w * n < D_nat w * 7 := by linarith

    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)

  refine ⟨n, ?_, hn_eq⟩

  simp only [mem_insert, mem_singleton]

  omega



/-- **따름정리 5.4 (무한 원시 집중 계열의 조합적 개수 `N_{39}(p), N_{40}(p)` 및 `p = 30, 45, 60, 100` 정확값 검증; 보충본 p.8~9 표)**:

    `N_39(p, T_p) = ∑_{t=2}^{T_p} C(p + t - 2, t)`, `N_40(p, T_p) = ∑_{t=3}^{T_p + 1} C(p + t - 2, t)` 로 정의하면,

    `p = 30 (T_{30} = 2)`, `p = 45 (T_{45} = 3)`, `p = 60 (T_{60} = 4)`, `p = 100 (T_{100} = 6)`에서의 조합 개수가

    보충본 p.9 표의 값(`4930`, `209715`, `8218287`, `25979406750`)과 100% 일치한다. -/

def N39_count (p Tp : ℕ) : ℕ :=

  ∑ t ∈ Ico 2 (Tp + 1), Nat.choose (p + t - 2) t



def N40_count (p Tp : ℕ) : ℕ :=

  ∑ t ∈ Ico 3 (Tp + 2), Nat.choose (p + t - 2) t



theorem Corollary_5_4_Concentrated_Family_Combinatorial_Counts :

    N39_count 30 2 = 435 ∧ N40_count 30 2 = 4495 ∧ 435 + 4495 = 4930 ∧

    N39_count 45 3 = 16170 ∧ N40_count 45 3 = 193545 ∧ 16170 + 193545 = 209715 ∧

    N39_count 60 4 = 595605 ∧ N40_count 60 4 = 7622682 ∧ 595605 + 7622682 = 8218287 ∧

    N39_count 100 6 = 1609344000 ∧ N40_count 100 6 = 24370062750 ∧

    1609344000 + 24370062750 = 25979406750 := by

  decide



/-! ## §6 인접 교환 및 균형 `{1, 2}` 기계적 word (보충본 p.9~10 보조정리 6.1~6.2, 따름정리 6.3, 정리 6.4, 따름정리 6.5; GARCD-41 ~ 42A) -/



/-- 앞부분 `pre`, 인접한 두 원소 `x, y`, 뒷부분 `suf`로 이루어진 word `pre ++ [x, y] ++ suf` 와

    인접한 두 원소를 맞바꾼 word `pre ++ [y, x] ++ suf` (보충본 §6 보조정리 6.1) -/

def wordSwapAdj (pre suf : List ℕ) (x y : ℕ) : List ℕ :=

  pre ++ [x, y] ++ suf



/-- 보조정리 6.1.1: `wordSwapAdj pre suf x y`와 `wordSwapAdj pre suf y x`는 길이와 총 지수합이 같으며,

    부분 지수합 `A_part`는 위치 `j = pre.length + 1`에서만 각각 `A_total pre + x`와 `A_total pre + y`로 다르고

    나머지 모든 `j`에서는 완전히 일치한다. -/

lemma wordSwapAdj_length_and_total (pre suf : List ℕ) (x y : ℕ) :

    (wordSwapAdj pre suf x y).length = pre.length + 2 + suf.length ∧

    A_total (wordSwapAdj pre suf x y) = A_total pre + x + y + A_total suf ∧

    (wordSwapAdj pre suf y x).length = (wordSwapAdj pre suf x y).length ∧

    A_total (wordSwapAdj pre suf y x) = A_total (wordSwapAdj pre suf x y) := by

  unfold wordSwapAdj A_total

  simp only [List.length_append, List.length_cons, List.length_nil,

             List.sum_append, List.sum_cons, List.sum_nil]

  refine ⟨by omega, by omega, by omega, by omega⟩



lemma A_part_wordSwapAdj_eq_of_ne (pre suf : List ℕ) (x y : ℕ) {j : ℕ}

    (hj_ne : j ≠ pre.length + 1) :

    A_part (wordSwapAdj pre suf y x) j = A_part (wordSwapAdj pre suf x y) j := by

  unfold A_part wordSwapAdj

  rcases lt_trichotomy j (pre.length + 1) with hlt | heq | hgt

  · have hj_le : j ≤ pre.length := by omega

    rw [List.append_assoc, List.append_assoc,

        List.take_append_of_le_length hj_le, List.take_append_of_le_length hj_le]

  · exact absurd heq hj_ne

  · have hj_ge2 : pre.length + 2 ≤ j := by omega

    have hlen1 : (pre ++ [y, x]).length = pre.length + 2 := by simp

    have hlen2 : (pre ++ [x, y]).length = pre.length + 2 := by simp

    rw [List.take_append, List.take_append, hlen1, hlen2,

        List.take_of_length_le (by omega : (pre ++ [y, x]).length ≤ j),

        List.take_of_length_le (by omega : (pre ++ [x, y]).length ≤ j)]

    simp [List.sum_append]

    omega



lemma A_part_wordSwapAdj_at_succ (pre suf : List ℕ) (x y : ℕ) :

    A_part (wordSwapAdj pre suf x y) (pre.length + 1) = A_total pre + x := by

  unfold A_part A_total wordSwapAdj

  have hlen : (pre ++ [x]).length = pre.length + 1 := by simp

  have h_assoc : pre ++ [x, y] ++ suf = (pre ++ [x]) ++ (y :: suf) := by simp

  rw [h_assoc, List.take_append_of_le_length (by omega : pre.length + 1 ≤ (pre ++ [x]).length)]

  rw [List.take_of_length_le (by omega : (pre ++ [x]).length ≤ pre.length + 1)]

  simp



/-- **보조정리 6.1 (GARCD-41: 인접 지수 교환 공식 및 `(1, 2)` 교환의 서로소 성질; 보충본 p.9)**:

    `w = pre ++ [x, y] ++ suf`, `w' = pre ++ [y, x] ++ suf` (`i = pre.length`, `p = w.length`)에 대해:

    (1) 일반 공식: `(C_p w' : ℤ) - (C_p w : ℤ) = 3^{p - 2 - i} * 2^{A_i} * (2^y - 2^x)` 이다.

    (2) 특히 `(x, y) = (1, 2)`이면 `C_p w' - C_p w = 2^{A_i + 1} * 3^{p - 2 - i}` 이고,

        `3^p ≤ 2^A`일 때 `Nat.Coprime (D_nat w) (C_p w' - C_p w)` 가 성립한다. -/

theorem GARCD_41_Adjacent_Exponent_Swap_Formula (pre suf : List ℕ) (x y : ℕ) :

    let w := wordSwapAdj pre suf x y

    let w' := wordSwapAdj pre suf y x

    let p := w.length

    let i := pre.length

    (C_p w' : ℤ) - (C_p w : ℤ) =

      (3 : ℤ) ^ (p - 2 - i) * (2 : ℤ) ^ (A_total pre) * ((2 : ℤ) ^ y - (2 : ℤ) ^ x) := by

  intro w w' p i

  have hlen_eq : w'.length = p := (wordSwapAdj_length_and_total pre suf x y).2.2.1

  unfold C_p C_sum

  rw [hlen_eq]

  push_cast

  rw [← sum_sub_distrib]

  have hi1_mem : i + 1 ∈ range p := by

    rw [mem_range]

    have hp_eq := (wordSwapAdj_length_and_total pre suf x y).1

    omega

  have h_sub_sum : (∑ j ∈ range p,

      ((3 : ℤ) ^ (p - 1 - j) * (2 : ℤ) ^ A_part w' j -

       (3 : ℤ) ^ (p - 1 - j) * (2 : ℤ) ^ A_part w j)) =

      ∑ j ∈ ({i + 1} : Finset ℕ),

      ((3 : ℤ) ^ (p - 1 - j) * (2 : ℤ) ^ A_part w' j -

       (3 : ℤ) ^ (p - 1 - j) * (2 : ℤ) ^ A_part w j) := by

    refine (sum_subset (singleton_subset_iff.mpr hi1_mem) ?_).symm

    intro j _ hj_not

    rw [mem_singleton] at hj_not

    rw [A_part_wordSwapAdj_eq_of_ne pre suf x y hj_not, sub_self]

  rw [h_sub_sum, sum_singleton,

      A_part_wordSwapAdj_at_succ pre suf y x, A_part_wordSwapAdj_at_succ pre suf x y]

  have hexp : p - 1 - (i + 1) = p - 2 - i := by omega

  rw [hexp, pow_add (2 : ℤ) (A_total pre) y, pow_add (2 : ℤ) (A_total pre) x]

  ring



theorem GARCD_41_Adjacent_Swap_One_Two_Coprime

    (pre suf : List ℕ) (hle : 3 ^ (wordSwapAdj pre suf 1 2).length ≤ 2 ^ A_total (wordSwapAdj pre suf 1 2)) :

    let w := wordSwapAdj pre suf 1 2

    let w' := wordSwapAdj pre suf 2 1

    let p := w.length

    let i := pre.length

    C_p w' = C_p w + 2 ^ (A_total pre + 1) * 3 ^ (p - 2 - i) ∧

    Nat.Coprime (D_nat w) (2 ^ (A_total pre + 1) * 3 ^ (p - 2 - i)) := by

  intro w w' p i

  have h_diff := GARCD_41_Adjacent_Exponent_Swap_Formula pre suf 1 2

  dsimp only at h_diff

  have h_nat : C_p w' = C_p w + 2 ^ (A_total pre + 1) * 3 ^ (p - 2 - i) := by

    have h_z : (C_p w' : ℤ) = (C_p w : ℤ) + ((2 ^ (A_total pre + 1) * 3 ^ (p - 2 - i) : ℕ) : ℤ) := by

      push_cast

      rw [pow_succ (2 : ℤ) (A_total pre)]

      linarith

    exact_mod_cast h_z

  refine ⟨h_nat, ?_⟩

  have hp_eq := (wordSwapAdj_length_and_total pre suf 1 2).1

  have hA_eq := (wordSwapAdj_length_and_total pre suf 1 2).2.1

  have hA_ge1 : 1 ≤ A_total w := by omega

  have hp_ge1 : 1 ≤ w.length := by omega

  obtain ⟨hD_odd, hD_not3, _⟩ := Remark_1_2_D_nat_Odd_And_Coprime_Six hA_ge1 hp_ge1 hle

  have hcop2 : Nat.Coprime (D_nat w) (2 ^ (A_total pre + 1)) :=

    coprime_odd_two_pow hD_odd (A_total pre + 1)

  have hcop3 : Nat.Coprime (D_nat w) (3 ^ (p - 2 - i)) := by

    refine Nat.Coprime.pow_right (p - 2 - i) ?_

    exact ((Nat.prime_three.coprime_iff_not_dvd).2 hD_not3).symm

  exact hcop2.mul_right hcop3



/-- **따름정리 6.3 (인접 교환에 의한 보정항의 엄격 단조 증가성 — 정렬 극값 원리; 보충본 p.9)**:

    `x < y`일 때 인접한 두 지수 `(x, y)`를 더 큰 지수가 앞에 오도록 `(y, x)`로 교환하면

    보정항이 엄격히 증가한다: `C_p (wordSwapAdj pre suf x y) < C_p (wordSwapAdj pre suf y x)`. -/

theorem Corollary_6_3_Adjacent_Swap_Strict_Increase

    (pre suf : List ℕ) {x y : ℕ} (hxy : x < y) :

    C_p (wordSwapAdj pre suf x y) < C_p (wordSwapAdj pre suf y x) := by

  have h_diff := GARCD_41_Adjacent_Exponent_Swap_Formula pre suf x y

  dsimp only at h_diff

  have h_pow_lt : (2 : ℤ) ^ x < (2 : ℤ) ^ y := by

    have : 2 ^ x < 2 ^ y := Nat.pow_lt_pow_right (by omega) hxy

    exact_mod_cast this

  have h_pos1 : (0 : ℤ) < (3 : ℤ) ^ ((wordSwapAdj pre suf x y).length - 2 - pre.length) := by positivity

  have h_pos2 : (0 : ℤ) < (2 : ℤ) ^ A_total pre := by positivity

  have h_prod_pos : (0 : ℤ) <

      (3 : ℤ) ^ ((wordSwapAdj pre suf x y).length - 2 - pre.length) *

      (2 : ℤ) ^ A_total pre * ((2 : ℤ) ^ y - (2 : ℤ) ^ x) :=

    mul_pos (mul_pos h_pos1 h_pos2) (by linarith)

  have h_lt_z : (C_p (wordSwapAdj pre suf x y) : ℤ) < (C_p (wordSwapAdj pre suf y x) : ℤ) := by

    linarith

  exact Int.ofNat_lt.mp h_lt_z



/-- 균형 기계적(Christoffel) word의 일반 항 `a_j(p, t, s) = 1 + ⌊((j + 1) t + s) / p⌋ - ⌊(j t + s) / p⌋` (보충본 p.10 정리 6.4) -/

def mechExp (p t s j : ℕ) : ℕ :=

  1 + ((j + 1) * t + s) / p - (j * t + s) / p



/-- 길이 `p`, 기울기 `t`, 위상 `s`인 균형 기계적 word `mechWord p t s` -/

def mechWord (p t s : ℕ) : List ℕ :=

  (List.range p).map (mechExp p t s)



/-- **정리 6.4 (GARCD-42A: 순환회전과 `(1, 2) ↔ (2, 1)` 인접 교환이 결합된 균형 word의 보편적 비소거 및 `p = 8, t = 5` 검산; 보충본 p.10)**:

    (1) 구조적 핵심 원리: 어떤 지수열 `w`의 두 순환회전 `rotateLeft w k₁`와 `rotateLeft w k₂`가

        인접한 `(1, 2)`와 `(2, 1)`만 맞바꾼 관계(`rotateLeft w k₁ = wordSwapAdj pre suf 1 2` 및 `rotateLeft w k₂ = wordSwapAdj pre suf 2 1`)에 있고

        `1 < D_nat w` (`3^p < 2^A`)이면, 반드시 `¬ (D_nat w ∣ C_p w)` 가 성립한다!

    (2) 보충본 p.10의 명시적 균형 기계적 word 검산 예 (`p = 8, t = 5, s = 0`):

        `mechWord 8 5 0 = [1, 2, 1, 2, 2, 1, 2, 2]`, `A = 13`, `D = 1631`, `C = 14501`, `C % 1631 = 1453 ≠ 0`,

        그리고 `s_0 = p - 1 - t = 2`에서 `mechWord 8 5 2 = [1, 2, 2, 1, 2, 2, 1, 2]` 와 `mechWord 8 5 3 = [2, 1, 2, 2, 1, 2, 2, 1]` 은

        정확히 처음 두 지수 `(1, 2)`를 `(2, 1)`로 맞바꾼 word이자 `mechWord 8 5 0`의 순환회전이 되어 `1631 ∤ 14501` 이다. -/

theorem GARCD_42A_Cyclic_Swap_Universal_Nondivisibility

    {w pre suf : List ℕ} {k₁ k₂ : ℕ}

    (hp : 1 ≤ w.length) (hD_gt1 : 1 < D_nat w)

    (hrot1 : rotateLeft w k₁ = wordSwapAdj pre suf 1 2)

    (hrot2 : rotateLeft w k₂ = wordSwapAdj pre suf 2 1) :

    ¬ (D_nat w ∣ C_p w) := by

  intro hdvd

  have hle : 3 ^ w.length ≤ 2 ^ A_total w := by

    unfold D_nat at hD_gt1

    omega

  have hA_ge1 : 1 ≤ A_total w := by

    by_contra h0

    have hA0 : A_total w = 0 := by omega

    unfold D_nat at hD_gt1

    rw [hA0, pow_zero] at hD_gt1

    omega

  have hdvd_rot1 : D_nat w ∣ C_p (rotateLeft w k₁) :=

    (GARCD_30_Cyclic_Rotation_Invariance_All hA_ge1 hp hle k₁).2.mpr hdvd

  have hdvd_rot2 : D_nat w ∣ C_p (rotateLeft w k₂) :=

    (GARCD_30_Cyclic_Rotation_Invariance_All hA_ge1 hp hle k₂).2.mpr hdvd

  rw [hrot1] at hdvd_rot1

  rw [hrot2] at hdvd_rot2

  -- D_nat (wordSwapAdj pre suf 1 2) = D_nat w 확인

  have hD_eq : D_nat (wordSwapAdj pre suf 1 2) = D_nat w := by

    rw [← hrot1]

    have h_all : ∀ k : ℕ, D_nat (rotateLeft w k) = D_nat w := by

      intro k

      induction k with

      | zero => rfl

      | succ k ih =>

        rw [rotateLeft, Function.iterate_succ_apply',

            (rotateLeftOne_length_and_A_total _).2.2.1]

        exact ih

    exact h_all k₁

  have hle_swap : 3 ^ (wordSwapAdj pre suf 1 2).length ≤ 2 ^ A_total (wordSwapAdj pre suf 1 2) := by

    have : 1 < D_nat (wordSwapAdj pre suf 1 2) := by rw [hD_eq]; exact hD_gt1

    unfold D_nat at this

    omega

  obtain ⟨hC_diff, hcop⟩ := GARCD_41_Adjacent_Swap_One_Two_Coprime pre suf hle_swap

  dsimp only at hC_diff hcop

  rw [hD_eq] at hcop

  have hdvd_diff : D_nat w ∣ 2 ^ (A_total pre + 1) * 3 ^ ((wordSwapAdj pre suf 1 2).length - 2 - pre.length) := by

    have h_sub : C_p (wordSwapAdj pre suf 2 1) - C_p (wordSwapAdj pre suf 1 2) =

        2 ^ (A_total pre + 1) * 3 ^ ((wordSwapAdj pre suf 1 2).length - 2 - pre.length) := by

      omega

    rw [← h_sub]

    exact Nat.dvd_sub hdvd_rot2 hdvd_rot1

  have hdvd_one : D_nat w ∣ 1 := by

    rw [← hcop.gcd_eq_one]

    exact Nat.dvd_gcd (dvd_refl (D_nat w)) hdvd_diff

  have : D_nat w ≤ 1 := Nat.le_of_dvd (by omega) hdvd_one

  omega



-- CORRECTED: old rotation index 5 was false; see Diagnostics/NO_GO_Module08_2026-11-10.md.
theorem GARCD_42A_Mechanical_Word_p8_t5_Certificate_CORRECTED :

    mechWord 8 5 0 = [1, 2, 1, 2, 2, 1, 2, 2] ∧

    A_total (mechWord 8 5 0) = 13 ∧

    D_nat (mechWord 8 5 0) = 1631 ∧

    C_p (mechWord 8 5 0) = 14501 ∧

    C_p (mechWord 8 5 0) % 1631 = 1453 ∧

    mechWord 8 5 2 = wordSwapAdj [] [2, 1, 2, 2, 1, 2] 1 2 ∧

    mechWord 8 5 3 = wordSwapAdj [] [2, 1, 2, 2, 1, 2] 2 1 ∧

    rotateLeft (mechWord 8 5 0) 2 = mechWord 8 5 2 ∧

    rotateLeft (mechWord 8 5 0) 7 = mechWord 8 5 3 ∧

    ¬ (D_nat (mechWord 8 5 0) ∣ C_p (mechWord 8 5 0)) := by

  decide



end Module8

end GARCD

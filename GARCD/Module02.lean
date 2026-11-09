import GARCD.Module01

open scoped BigOperators
open Finset Real Filter

namespace GARCD




/-!

================================================================================

# MODULE 2: 시러큐스 아핀 반복 산술, 유한 합동류, 하강 밀도

  (보충본 §1.1 및 원본 v0.3 §6~§9, 부록 A.1~A.2, GARCD-4.1 ~ GARCD-4.5)

================================================================================

-/



section Module2



/-! ## §6.1 & §6.2 아핀 반복 공식 (보충본 보조정리 1.1 및 원본 정리 6.2, GARCD-4.1) -/



/-- 보조정리 6.1.1: 임의의 지수 word `w`와 `r ≤ w.length`에 대해 점화식 `C_rec w r`과 명시적 합 `C_sum w r`은 일치한다. -/

lemma C_rec_eq_C_sum (w : List ℕ) (r : ℕ) :

    C_rec w r = C_sum w r := by

  induction r with

  | zero =>

    simp [C_rec, C_sum]

  | succ r ih =>

    rw [C_rec, ih]
    simp only [C_sum]
    rw [sum_range_succ, mul_sum]

    congr 1

    · refine sum_congr rfl ?_

      intro j hj

      have hj_lt : j < r := mem_range.mp hj

      have hexp : r - j = (r - 1 - j) + 1 := by omega

      have hshift : r + 1 - 1 - j = r - j := by omega
      rw [hshift, hexp, pow_succ']

      ring

    · have hexp : r - r = 0 := by omega

      simp [hexp]



/-- 보조정리 6.1.2: 시작값 `n`의 누적 지수 점화식 `A_orbit n 0 = 0`, `A_orbit n (r + 1) = A_orbit n r + a_seq n r`. -/

lemma A_orbit_zero (n : ℕ) : A_orbit n 0 = 0 := by

  simp [A_orbit]



lemma A_orbit_succ (n r : ℕ) : A_orbit n (r + 1) = A_orbit n r + a_seq n r := by

  unfold A_orbit

  exact sum_range_succ (a_seq n) r



/-- 보조정리 6.1.3: 시작값 `n`의 보정항 점화식 `C_orbit n 0 = 0`, `C_orbit n (r + 1) = 3 * C_orbit n r + 2^{A_orbit n r}`. -/

lemma C_orbit_zero (n : ℕ) : C_orbit n 0 = 0 := by

  simp [C_orbit]



lemma C_orbit_succ (n r : ℕ) :

    C_orbit n (r + 1) = 3 * C_orbit n r + 2 ^ A_orbit n r := by

  unfold C_orbit

  rw [sum_range_succ, mul_sum]

  congr 1

  · refine sum_congr rfl ?_

    intro j hj

    have hj_lt : j < r := mem_range.mp hj

    have hexp : r - j = (r - 1 - j) + 1 := by omega

    have hshift : r + 1 - 1 - j = r - j := by omega
    rw [hshift, hexp, pow_succ']

    ring

  · have hexp : r - r = 0 := by omega

    simp [hexp]



/-- **정리 6.2 (GARCD-4.1: 시러큐스 아핀 반복 공식; 보충본 보조정리 1.1 및 원본 v0.3 p.21 식 (9))**:

    모든 자연수 `n`과 반복 횟수 `r ≥ 0`에 대해

    `2^{A_r(n)} * F^[r](n) = 3^r * n + C_r(n)` 이 성립한다. -/

theorem GARCD_4_1_Affine_Iteration_Identity (n r : ℕ) :

    2 ^ A_orbit n r * x_seq n r = 3 ^ r * n + C_orbit n r := by

  induction r with

  | zero =>

    simp [A_orbit_zero, C_orbit_zero, x_seq]

  | succ r ih =>

    rw [A_orbit_succ, pow_add, mul_assoc, syracuse_step_eq]

    calc

      2 ^ A_orbit n r * (3 * x_seq n r + 1)

          = 3 * (2 ^ A_orbit n r * x_seq n r) + 2 ^ A_orbit n r := by ring

      _ = 3 * (3 ^ r * n + C_orbit n r) + 2 ^ A_orbit n r := by rw [ih]

      _ = 3 ^ (r + 1) * n + (3 * C_orbit n r + 2 ^ A_orbit n r) := by ring

      _ = 3 ^ (r + 1) * n + C_orbit n (r + 1) := by rw [C_orbit_succ]



/-- 정리 6.2의 유리수/실수 나눗셈 형태: `x_r(n) = (3^r * n + C_r(n)) / 2^{A_r(n)}` -/

theorem GARCD_4_1_Affine_Iteration_Real (n r : ℕ) :

    (x_seq n r : ℝ) = ((3 : ℝ) ^ r * (n : ℝ) + (C_orbit n r : ℝ)) / (2 : ℝ) ^ A_orbit n r := by

  have h := congrArg (Nat.cast : ℕ → ℝ) (GARCD_4_1_Affine_Iteration_Identity n r)

  push_cast at h

  have hpow : (2 : ℝ) ^ A_orbit n r ≠ 0 := by positivity

  exact eq_div_of_mul_eq hpow (by linarith)



/-! ## §6.3 로그 드리프트와 정확한 하강/절반 하강 판정 (GARCD-4.2; 원본 v0.3 p.21 정리 6.3) -/



/-- 로그 드리프트 `D_r(n) = log₂(n / x_r(n))` (원본 v0.3 식 (10)) -/

noncomputable def DriftLog (n r : ℕ) : ℝ :=

  Real.logb 2 ((n : ℝ) / (x_seq n r : ℝ))



/-- **정리 6.3.1 (GARCD-4.2 로그 드리프트 공식; 원본 v0.3 p.21 식 (10))**:

    양의 정수 `n ≥ 1`과 `r ≥ 0`에 대해

    `D_r(n) = log₂((2^{A_r(n)} * n) / (3^r * n + C_r(n)))` 이다. -/

theorem GARCD_4_2_Log_Drift_Formula {n : ℕ} (_hn : 1 ≤ n) (r : ℕ) :

    DriftLog n r = Real.logb 2 (((2 : ℝ) ^ A_orbit n r * (n : ℝ)) / ((3 : ℝ) ^ r * (n : ℝ) + (C_orbit n r : ℝ))) := by

  unfold DriftLog

  rw [GARCD_4_1_Affine_Iteration_Real n r, div_div_eq_mul_div, mul_comm (n : ℝ)]



/-- **정리 6.3.2 (GARCD-4.2 정확한 하강 판정 부등식; 원본 v0.3 p.21 식 (11))**:

    모든 `n, r`에 대해 `x_r(n) < n`일 필요충분조건은 정수 부등식

    `((2 : ℤ)^{A_r(n)} - 3^r) * n > C_r(n)` 이 성립하는 것이다. -/

theorem GARCD_4_2_Exact_Descent_Iff (n r : ℕ) :

    x_seq n r < n ↔ (C_orbit n r : ℤ) < ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) := by

  have hid := congrArg (Nat.cast : ℕ → ℤ) (GARCD_4_1_Affine_Iteration_Identity n r)

  push_cast at hid

  have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ A_orbit n r := by positivity

  constructor

  · intro hlt

    have hlt_z : (x_seq n r : ℤ) < (n : ℤ) := Int.ofNat_lt.mpr hlt

    have hmul : (2 : ℤ) ^ A_orbit n r * (x_seq n r : ℤ) < (2 : ℤ) ^ A_orbit n r * (n : ℤ) :=

      mul_lt_mul_of_pos_left hlt_z hpow_pos

    linarith

  · intro hgt

    have hmul : (2 : ℤ) ^ A_orbit n r * (x_seq n r : ℤ) < (2 : ℤ) ^ A_orbit n r * (n : ℤ) := by

      linarith

    have hlt_z : (x_seq n r : ℤ) < (n : ℤ) := lt_of_mul_lt_mul_left hmul (le_of_lt hpow_pos)

    exact Int.ofNat_lt.mp hlt_z



/-- **정리 6.3.3 (GARCD-4.2 정확한 절반 이하 하강 판정 부등식; 원본 v0.3 p.21 식 (12))**:

    모든 `n, r`에 대해 `2 * x_r(n) ≤ n` (실수 `x_r(n) ≤ n / 2`)일 필요충분조건은 정수 부등식

    `((2 : ℤ)^{A_r(n)} - 2 * 3^r) * n ≥ 2 * C_r(n)` 이 성립하는 것이다. -/

theorem GARCD_4_2_Half_Descent_Iff (n r : ℕ) :

    2 * x_seq n r ≤ n ↔ 2 * (C_orbit n r : ℤ) ≤ ((2 : ℤ) ^ A_orbit n r - 2 * (3 : ℤ) ^ r) * (n : ℤ) := by

  have hid := congrArg (Nat.cast : ℕ → ℤ) (GARCD_4_1_Affine_Iteration_Identity n r)

  push_cast at hid

  have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ A_orbit n r := by positivity

  constructor

  · intro hle

    have hle_z : 2 * (x_seq n r : ℤ) ≤ (n : ℤ) := by exact_mod_cast hle

    have hmul : (2 : ℤ) ^ A_orbit n r * (2 * (x_seq n r : ℤ)) ≤ (2 : ℤ) ^ A_orbit n r * (n : ℤ) :=

      mul_le_mul_of_nonneg_left hle_z (le_of_lt hpow_pos)

    linarith

  · intro hge

    have hmul : (2 : ℤ) ^ A_orbit n r * (2 * (x_seq n r : ℤ)) ≤ (2 : ℤ) ^ A_orbit n r * (n : ℤ) := by

      linarith

    have hle_z : 2 * (x_seq n r : ℤ) ≤ (n : ℤ) := le_of_mul_le_mul_left hmul hpow_pos

    exact_mod_cast hle_z



/-! ## §7.1 & 부록 A.2 유한 valuation word의 유일한 합동류 (GARCD-4.3; 원본 v0.3 p.22 정리 7.1 및 p.38 부록 A.2) -/



/-- 양의 홀수 `n`이 길이 `r`인 양의 지수열 `w`를 최초 `r`번 정확히 실현한다는 조건 -/

def RealizesWord (w : List ℕ) (n : ℕ) : Prop :=

  n % 2 = 1 ∧ (∀ a ∈ w, 1 ≤ a) ∧ ∀ j : ℕ, j < w.length → a_seq n j = w.getD j 0



/-- 보조정리 7.1.1: 양의 정수 `m`과 `a ≥ 1`에 대해 `v₂(m) = a`일 필요충분조건은 `m ≡ 2^a (mod 2^{a+1})` (즉 `∃ q, m = 2^a * q ∧ q % 2 = 1`)이다. -/

lemma v2_eq_iff_mod_two_pow_succ {m a : ℕ} (hm : m ≠ 0) :

    v2 m = a ↔ m % (2 ^ (a + 1)) = 2 ^ a := by

  unfold v2

  constructor

  · intro h

    have hdvd : 2 ^ a ∣ m := by

      rw [← h]

      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).2 (le_refl _)

    have hndvd : ¬ (2 ^ (a + 1) ∣ m) := by

      rw [← h]

      intro hc

      have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mp hc

      omega

    obtain ⟨q, hq⟩ := hdvd

    have hq_odd : q % 2 = 1 := by

      by_contra hq_even

      have hq2 : 2 ∣ q := by omega

      obtain ⟨k, hk⟩ := hq2

      apply hndvd

      refine ⟨k, ?_⟩

      rw [hq, hk, pow_succ]

      ring

    have hq_decomp : q = 2 * (q / 2) + 1 := by omega

    calc

      m % (2 ^ (a + 1)) = (2 ^ a * (2 * (q / 2) + 1)) % (2 ^ (a + 1)) := by rw [hq, ← hq_decomp]

      _ = (2 ^ a + 2 ^ (a + 1) * (q / 2)) % (2 ^ (a + 1)) := by ring_nf

      _ = 2 ^ a % (2 ^ (a + 1)) := Nat.add_mul_mod_self_left _ _ _

      _ = 2 ^ a := by
        have ha : 0 < 2 ^ a := by positivity
        have hpow : 2 ^ (a + 1) = 2 ^ a * 2 := by rw [pow_succ]
        apply Nat.mod_eq_of_lt
        omega

  · intro hmod

    have hdiv_eq : m = 2 ^ (a + 1) * (m / 2 ^ (a + 1)) + 2 ^ a := by

      have := Nat.div_add_mod m (2 ^ (a + 1))

      omega

    have hdvd : 2 ^ a ∣ m := by

      refine ⟨2 * (m / 2 ^ (a + 1)) + 1, ?_⟩

      calc
        m = 2 ^ (a + 1) * (m / 2 ^ (a + 1)) + 2 ^ a := hdiv_eq
        _ = 2 ^ a * (2 * (m / 2 ^ (a + 1)) + 1) := by
          rw [pow_succ]
          ring

    have hndvd : ¬ (2 ^ (a + 1) ∣ m) := by

      intro hc

      have hzero : m % (2 ^ (a + 1)) = 0 := Nat.mod_eq_zero_of_dvd hc

      have hpos : 0 < 2 ^ a := by positivity

      omega

    have hge : a ≤ m.factorization 2 :=

      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mp hdvd

    have hlt : ¬ (a + 1 ≤ m.factorization 2) :=

      fun hle => hndvd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr hle)

    omega



/-- 보조정리 7.1.2: `n`이 `w`를 실현하면 모든 `j ≤ w.length`에서 `A_orbit n j = A_part w j` 및 `C_orbit n j = C_sum w j`이다. -/

lemma A_orbit_eq_A_part_of_RealizesWord {w : List ℕ} {n : ℕ} (h : RealizesWord w n) :

    ∀ j : ℕ, j ≤ w.length → A_orbit n j = A_part w j := by

  intro j hj

  induction j with

  | zero =>

    simp [A_orbit, A_part]

  | succ j ih =>

    have hj_lt : j < w.length := by omega

    rw [A_orbit_succ, ih (by omega)]

    simp only [A_part]

    rw [List.take_succ_eq_append_getElem hj_lt, List.sum_append, List.sum_singleton]

    have hget : w.getD j 0 = w[j] := List.getD_eq_getElem w 0 hj_lt

    rw [h.2.2 j hj_lt, hget]




lemma C_orbit_eq_C_sum_of_RealizesWord {w : List ℕ} {n : ℕ} (h : RealizesWord w n) :

    ∀ j : ℕ, j ≤ w.length → C_orbit n j = C_sum w j := by

  intro j hj

  unfold C_orbit C_sum

  refine sum_congr rfl ?_

  intro i hi

  have hi_lt : i < j := mem_range.mp hi

  rw [A_orbit_eq_A_part_of_RealizesWord h i (by omega)]



/-- 보조정리 7.1.3 (부록 A.2의 부분 보정항 분할 항등식; 원본 v0.3 p.38):

    모든 `j ≤ r`에 대해

    `C_sum w r = 3^{r - j} * C_sum w j + ∑ t ∈ Ico j r, 3^{r - 1 - t} * 2^{A_part w t}` 이다. -/

lemma C_sum_split (w : List ℕ) {j r : ℕ} (hjr : j ≤ r) :

    C_sum w r = 3 ^ (r - j) * C_sum w j + ∑ t ∈ Ico j r, 3 ^ (r - 1 - t) * 2 ^ A_part w t := by

  unfold C_sum

  rw [← sum_range_add_sum_Ico _ hjr, mul_sum]

  congr 1

  refine sum_congr rfl ?_

  intro i hi

  have hi_lt : i < j := mem_range.mp hi

  have hexp : r - 1 - i = (r - j) + (j - 1 - i) := by omega

  rw [hexp, pow_add]

  ring



/-- 보조정리 7.1.4: 양의 지수 word `w` (`∀ a ∈ w, 1 ≤ a`)에서 `i ≤ t ≤ w.length`이면 `A_part w i + (t - i) ≤ A_part w t`이다. -/

lemma A_part_mono_add {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {i t : ℕ} (hit : i ≤ t) (ht : t ≤ w.length) :

    A_part w i + (t - i) ≤ A_part w t := by

  induction t with

  | zero =>

    have hi0 : i = 0 := by omega

    subst hi0

    simp [A_part]

  | succ t ih =>

    by_cases h_eq : i = t + 1

    · subst h_eq

      simp

    · have hit' : i ≤ t := by omega

      have ht_lt : t < w.length := by omega

      have h_step : A_part w (t + 1) = A_part w t + w[t] := by

        unfold A_part

        rw [List.take_succ_eq_append_getElem ht_lt, List.sum_append, List.sum_singleton]

      have hw_t : 1 ≤ w[t] := hw w[t] (List.getElem_mem ht_lt)

      have h_ih := ih hit' (by omega)

      omega



/-- 보조정리 7.1.5 (부록 A.2 가분성): `t ≥ j`이면 `2^{A_part w j} ∣ 2^{A_part w t}`이므로

    `2^{A_part w j} ∣ ∑ t ∈ Ico j r, 3^{r - 1 - t} * 2^{A_part w t}` 이다. -/

lemma two_pow_A_part_dvd_tail (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) {j r : ℕ} (hjr : j ≤ r) (hr : r ≤ w.length) :

    2 ^ A_part w j ∣ ∑ t ∈ Ico j r, 3 ^ (r - 1 - t) * 2 ^ A_part w t := by

  refine dvd_sum ?_

  intro t ht

  rw [mem_Ico] at ht

  have hle : A_part w j ≤ A_part w t := by

    have := A_part_mono_add hw ht.1 (by omega)

    omega

  exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hle) _



/-- 보조정리 7.1.6: 홀수 `M`과 임의의 `K`에 대해 `gcd(M, 2^K) = 1`이다. -/

lemma coprime_odd_two_pow {M : ℕ} (hM : M % 2 = 1) (K : ℕ) :

    Nat.Coprime M (2 ^ K) := by

  refine Nat.Coprime.pow_right K ?_

  rw [Nat.coprime_two_right, Nat.odd_iff]

  exact hM



lemma coprime_three_pow_two_pow (r K : ℕ) :

    Nat.Coprime (3 ^ r) (2 ^ K) := by

  refine Nat.Coprime.pow r K ?_

  decide



/-- **정리 7.1 정방향 (GARCD-4.3 필요조건; 원본 v0.3 p.22 식 (13))**:

    양의 홀수 `n`이 길이 `r = w.length`인 양의 지수열 `w`를 실현하면

    `3^r * n + C_p(w) ≡ 2^{A(w)} (mod 2^{A(w) + 1})` 이 성립한다. -/

theorem GARCD_4_3_Forward {w : List ℕ} {n : ℕ} (h : RealizesWord w n) :

    (3 ^ w.length * n + C_p w) % (2 ^ (A_total w + 1)) = 2 ^ A_total w := by

  have hid := GARCD_4_1_Affine_Iteration_Identity n w.length

  have hA : A_orbit n w.length = A_total w := by

    unfold A_total

    rw [A_orbit_eq_A_part_of_RealizesWord h w.length (le_refl _), A_part, List.take_length]

  have hC : C_orbit n w.length = C_p w := by

    unfold C_p

    exact C_orbit_eq_C_sum_of_RealizesWord h w.length (le_refl _)

  rw [hA, hC] at hid

  rw [← hid]

  have hx_odd : x_seq n w.length % 2 = 1 := x_seq_odd h.1 w.length

  have hx_decomp : x_seq n w.length = 2 * (x_seq n w.length / 2) + 1 := by omega

  calc

    (2 ^ A_total w * x_seq n w.length) % (2 ^ (A_total w + 1))

        = (2 ^ A_total w * (2 * (x_seq n w.length / 2) + 1)) % (2 ^ (A_total w + 1)) := by

          rw [← hx_decomp]

    _ = (2 ^ A_total w + 2 ^ (A_total w + 1) * (x_seq n w.length / 2)) % (2 ^ (A_total w + 1)) := by

          ring_nf

    _ = (2 ^ A_total w) % (2 ^ (A_total w + 1)) := Nat.add_mul_mod_self_left _ _ _

    _ = 2 ^ A_total w := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))



/-- **정리 7.1 역방향 및 부록 A.2 완전 증명 (GARCD-4.3 충분조건; 원본 v0.3 p.22 & p.38)**:

    길이 `r = w.length`인 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)에 대해, 양의 정수 `n`이 합동식

    `(3^r * n + C_p(w)) % 2^{A(w) + 1} = 2^{A(w)}` 를 만족하면,

    `n`은 홀수이고 모든 `0 ≤ j < r`에서 `a_seq n j = w[j]`로 `w`를 정확히 실현한다. -/

theorem GARCD_4_3_Reverse_Appendix_A2 {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {n : ℕ}

    (hcong : (3 ^ w.length * n + C_p w) % (2 ^ (A_total w + 1)) = 2 ^ A_total w) :

    RealizesWord w n := by

  let r := w.length

  let A := A_total w

  -- Step 1: 2^A ∣ (3^r * n + C_p w) 및 몫 y = (3^r * n + C_p w) / 2^A 가 홀수임을 확인

  have hdiv_eq : 3 ^ r * n + C_p w = 2 ^ (A + 1) * ((3 ^ r * n + C_p w) / 2 ^ (A + 1)) + 2 ^ A := by

    have hmod : (3 ^ r * n + C_p w) % (2 ^ (A + 1)) = 2 ^ A := hcong
    have hq := Nat.div_add_mod (3 ^ r * n + C_p w) (2 ^ (A + 1))
    calc
      3 ^ r * n + C_p w =
        (2 ^ (A + 1)) * ((3 ^ r * n + C_p w) / (2 ^ (A + 1))) +
          (3 ^ r * n + C_p w) % (2 ^ (A + 1)) := hq.symm
      _ = 2 ^ (A + 1) * ((3 ^ r * n + C_p w) / 2 ^ (A + 1)) + 2 ^ A := by
        rw [hmod]

  let q := (3 ^ r * n + C_p w) / 2 ^ (A + 1)

  let y := 2 * q + 1

  have hy_eq : 3 ^ r * n + C_p w = 2 ^ A * y := by

    change 3 ^ r * n + C_p w = 2 ^ A * (2 * q + 1)

    calc
      3 ^ r * n + C_p w = 2 ^ (A + 1) * q + 2 ^ A := hdiv_eq
      _ = 2 ^ A * (2 * q + 1) := by
        rw [pow_succ]
        ring

  have hy_odd : y % 2 = 1 := by omega



  -- Step 2: 부록 A.2의 부분 합동식에 의해 모든 j ≤ r 에서 2^{A_part w j} ∣ (3^j * n + C_sum w j)

  -- 그리고 몫 y_j = (3^j * n + C_sum w j) / 2^{A_part w j} 가 홀수이며 2^{w[j]} * y_{j+1} = 3 * y_j + 1 을 만족함

  have h_step_div : ∀ j : ℕ, j ≤ r →

      ∃ y_j : ℕ, 3 ^ j * n + C_sum w j = 2 ^ A_part w j * y_j ∧ y_j % 2 = 1 := by

    intro j hj

    -- r - j 에 대한 하향 귀납법 (부록 A.2 역귀납)

    obtain ⟨d, hd⟩ : ∃ d, r - j = d := ⟨r - j, rfl⟩

    induction d generalizing j with

    | zero =>

      have hjr : j = r := by omega

      subst hjr

      refine ⟨y, ?_, hy_odd⟩

      have hAp : A_part w r = A := by

        unfold A_part A A_total r

        rw [List.take_length]

      rw [hAp]

      exact hy_eq

    | succ d ih =>

      have hj_lt : j < r := by omega

      have hd' : r - (j + 1) = d := by omega

      obtain ⟨y_next, hy_next_eq, hy_next_odd⟩ := ih (j + 1) (by omega) hd'

      have hC_succ : C_sum w (j + 1) = 3 * C_sum w j + 2 ^ A_part w j := by

        rw [← C_rec_eq_C_sum, C_rec, C_rec_eq_C_sum]

      have hA_succ : A_part w (j + 1) = A_part w j + w[j] := by

        unfold A_part

        rw [List.take_succ_eq_append_getElem hj_lt, List.sum_append, List.sum_singleton]

      have h_rel : 3 * (3 ^ j * n + C_sum w j) + 2 ^ A_part w j = 2 ^ A_part w j * (2 ^ w[j] * y_next) := by

        calc

          3 * (3 ^ j * n + C_sum w j) + 2 ^ A_part w j

              = 3 ^ (j + 1) * n + (3 * C_sum w j + 2 ^ A_part w j) := by ring

          _ = 3 ^ (j + 1) * n + C_sum w (j + 1) := by rw [← hC_succ]

          _ = 2 ^ A_part w (j + 1) * y_next := hy_next_eq

          _ = 2 ^ A_part w j * (2 ^ w[j] * y_next) := by rw [hA_succ, pow_add, mul_assoc]

      have hdvd_3 : 2 ^ A_part w j ∣ 3 * (3 ^ j * n + C_sum w j) := by

        refine ⟨2 ^ w[j] * y_next - 1, ?_⟩

        have hpos : 1 ≤ 2 ^ w[j] * y_next := by

          have : 1 ≤ 2 ^ w[j] := Nat.one_le_pow _ 2 (by omega)

          have : 1 ≤ y_next := by omega

          exact Nat.mul_le_mul ‹1 ≤ 2 ^ w[j]› ‹1 ≤ y_next›

        rw [Nat.mul_sub_left_distrib, mul_one]

        omega

      have hcop : Nat.Coprime (2 ^ A_part w j) 3 := (coprime_three_pow_two_pow 1 (A_part w j)).symm

      have hdvd_base : 2 ^ A_part w j ∣ (3 ^ j * n + C_sum w j) :=

        hcop.dvd_of_dvd_mul_left hdvd_3

      obtain ⟨y_j, hy_j_eq⟩ := hdvd_base

      refine ⟨y_j, hy_j_eq, ?_⟩

      have h_cancel : 2 ^ A_part w j * (3 * y_j + 1) = 2 ^ A_part w j * (2 ^ w[j] * y_next) := by

        calc

          2 ^ A_part w j * (3 * y_j + 1)

              = 3 * (2 ^ A_part w j * y_j) + 2 ^ A_part w j := by ring

          _ = 3 * (3 ^ j * n + C_sum w j) + 2 ^ A_part w j := by rw [← hy_j_eq]

          _ = 2 ^ A_part w j * (2 ^ w[j] * y_next) := h_rel

      have hpow_pos : 0 < 2 ^ A_part w j := by positivity

      have hy_step : 3 * y_j + 1 = 2 ^ w[j] * y_next := Nat.eq_of_mul_eq_mul_left hpow_pos h_cancel

      have hw_j : 1 ≤ w[j] := hw w[j] (List.getElem_mem hj_lt)

      have heven : (2 ^ w[j] * y_next) % 2 = 0 := by

        obtain ⟨k, hk⟩ : ∃ k, w[j] = k + 1 := ⟨w[j] - 1, by omega⟩

        rw [hk, pow_succ]

        omega

      omega



  -- Step 3: j = 0 에서 n 이 홀수임을 도출

  have hn_odd : n % 2 = 1 := by

    obtain ⟨y_0, hy_0_eq, hy_0_odd⟩ := h_step_div 0 (Nat.zero_le r)

    simp [A_part, C_sum] at hy_0_eq

    omega



  -- Step 4: j 에 대한 전방향 귀납법으로 x_seq n j = y_j 및 a_seq n j = w[j] 증명

  have h_forward : ∀ j : ℕ, j < r →

      (A_orbit n j = A_part w j ∧ C_orbit n j = C_sum w j ∧ a_seq n j = w.getD j 0) := by

    intro j hj

    induction j with

    | zero =>

      have hA0 : A_orbit n 0 = A_part w 0 := by simp [A_orbit, A_part]

      have hC0 : C_orbit n 0 = C_sum w 0 := by simp [C_orbit, C_sum]

      refine ⟨hA0, hC0, ?_⟩

      obtain ⟨y_1, hy_1_eq, hy_1_odd⟩ := h_step_div 1 (by omega)

      have hA1 : A_part w 1 = w[0] := by

        have : A_part w 1 = A_part w 0 + w[0] := by

          unfold A_part

          rw [List.take_succ_eq_append_getElem hj, List.sum_append, List.sum_singleton]

        simpa [A_part] using this

      have hC1 : C_sum w 1 = 1 := by simp [C_sum, A_part]

      rw [hA1, hC1, pow_one] at hy_1_eq

      have ha0 : a_seq n 0 = w[0] := by

        unfold a_seq x_seq

        simp only [Function.iterate_zero_apply]

        rw [v2_eq_iff_mod_two_pow_succ (by omega)]

        rw [hy_1_eq]

        have hy1_decomp : y_1 = 2 * (y_1 / 2) + 1 := by omega

        calc

          (2 ^ w[0] * y_1) % (2 ^ (w[0] + 1))

              = (2 ^ w[0] + 2 ^ (w[0] + 1) * (y_1 / 2)) % (2 ^ (w[0] + 1)) := by

                conv_lhs => rw [hy1_decomp]
                ring_nf

          _ = (2 ^ w[0]) % (2 ^ (w[0] + 1)) := Nat.add_mul_mod_self_left _ _ _

          _ = 2 ^ w[0] := by
            have hpos : 0 < 2 ^ w[0] := by positivity
            have hpow : 2 ^ (w[0] + 1) = 2 ^ w[0] * 2 := by rw [pow_succ]
            apply Nat.mod_eq_of_lt
            omega

      rw [ha0, List.getD_eq_getElem w 0 hj]

    | succ j ih =>

      have hj_lt : j < r := by omega

      obtain ⟨hAj, hCj, haj⟩ := ih hj_lt

      have hget_j : w.getD j 0 = w[j] := List.getD_eq_getElem w 0 hj_lt

      have hA_succ : A_orbit n (j + 1) = A_part w (j + 1) := by

        rw [A_orbit_succ, hAj, haj, hget_j]

        unfold A_part

        rw [List.take_succ_eq_append_getElem hj_lt, List.sum_append, List.sum_singleton]

      have hC_succ : C_orbit n (j + 1) = C_sum w (j + 1) := by

        rw [C_orbit_succ, hCj, hAj]
        calc
          3 * C_sum w j + 2 ^ A_part w j = C_rec w (j + 1) := by
            rw [C_rec, C_rec_eq_C_sum]
          _ = C_sum w (j + 1) := C_rec_eq_C_sum w (j + 1)

      refine ⟨hA_succ, hC_succ, ?_⟩

      obtain ⟨y_j1, hy_j1_eq, _⟩ := h_step_div (j + 1) (by omega)

      obtain ⟨y_j2, hy_j2_eq, hy_j2_odd⟩ := h_step_div (j + 2) (by omega)

      have hx_eq : x_seq n (j + 1) = y_j1 := by

        have hid := GARCD_4_1_Affine_Iteration_Identity n (j + 1)

        rw [hA_succ, hC_succ, hy_j1_eq] at hid

        exact Nat.eq_of_mul_eq_mul_left (by positivity) hid

      have hC_j2 : C_sum w (j + 2) = 3 * C_sum w (j + 1) + 2 ^ A_part w (j + 1) := by

        rw [← C_rec_eq_C_sum, C_rec, C_rec_eq_C_sum]

      have hA_j2 : A_part w (j + 2) = A_part w (j + 1) + w[j + 1] := by

        unfold A_part

        rw [List.take_succ_eq_append_getElem hj, List.sum_append, List.sum_singleton]

      have h_rel : 2 ^ A_part w (j + 1) * (3 * x_seq n (j + 1) + 1) =

          2 ^ A_part w (j + 1) * (2 ^ w[j + 1] * y_j2) := by

        calc

          2 ^ A_part w (j + 1) * (3 * x_seq n (j + 1) + 1)

              = 3 * (2 ^ A_part w (j + 1) * y_j1) + 2 ^ A_part w (j + 1) := by rw [hx_eq]; ring

          _ = 3 * (3 ^ (j + 1) * n + C_sum w (j + 1)) + 2 ^ A_part w (j + 1) := by rw [← hy_j1_eq]

          _ = 3 ^ (j + 2) * n + C_sum w (j + 2) := by rw [hC_j2]; ring

          _ = 2 ^ A_part w (j + 2) * y_j2 := hy_j2_eq

          _ = 2 ^ A_part w (j + 1) * (2 ^ w[j + 1] * y_j2) := by rw [hA_j2, pow_add, mul_assoc]

      have h_step : 3 * x_seq n (j + 1) + 1 = 2 ^ w[j + 1] * y_j2 :=

        Nat.eq_of_mul_eq_mul_left (by positivity) h_rel

      have ha_j1 : a_seq n (j + 1) = w[j + 1] := by

        unfold a_seq

        rw [v2_eq_iff_mod_two_pow_succ (by omega), h_step]

        have hy_decomp : y_j2 = 2 * (y_j2 / 2) + 1 := by omega

        calc

          (2 ^ w[j + 1] * y_j2) % (2 ^ (w[j + 1] + 1))

              = (2 ^ w[j + 1] + 2 ^ (w[j + 1] + 1) * (y_j2 / 2)) % (2 ^ (w[j + 1] + 1)) := by

                conv_lhs => rw [hy_decomp]
                ring_nf

          _ = (2 ^ w[j + 1]) % (2 ^ (w[j + 1] + 1)) := Nat.add_mul_mod_self_left _ _ _

          _ = 2 ^ w[j + 1] := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))

      rw [ha_j1, List.getD_eq_getElem w 0 hj]



  refine ⟨hn_odd, hw, fun j hj => (h_forward j hj).2.2⟩



/-- **정리 7.1 통합본 (GARCD-4.3 유한 valuation word의 유일한 합동류 필요충분조건 및 유일성; 원본 v0.3 p.22 정리 7.1)**:

    고정된 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)와 양의 정수 `n`에 대해:

    (1) `n`이 `w`를 실현할 필요충분조건은 `(3^r * n + C_p(w)) % 2^{A(w) + 1} = 2^{A(w)}` 이다.

    (2) `n₁, n₂`가 모두 `w`를 실현하면 `n₁ ≡ n₂ (mod 2^{A(w) + 1})` 로 법 `2^{A(w) + 1}`에서 유일한 합동류를 이룬다. -/

theorem GARCD_4_3_Unique_Congruence_Class {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (n : ℕ) :

    RealizesWord w n ↔ (3 ^ w.length * n + C_p w) % (2 ^ (A_total w + 1)) = 2 ^ A_total w :=

  ⟨GARCD_4_3_Forward, GARCD_4_3_Reverse_Appendix_A2 hw⟩



theorem GARCD_4_3_Uniqueness_Mod_Two_Pow_Succ {w : List ℕ} {n₁ n₂ : ℕ}

    (h₁ : RealizesWord w n₁) (h₂ : RealizesWord w n₂) :

    n₁ % (2 ^ (A_total w + 1)) = n₂ % (2 ^ (A_total w + 1)) := by

  have hc₁ := GARCD_4_3_Forward h₁

  have hc₂ := GARCD_4_3_Forward h₂

  have hmod : (3 ^ w.length * n₁ + C_p w) ≡ (3 ^ w.length * n₂ + C_p w) [MOD 2 ^ (A_total w + 1)] := by

    change (3 ^ w.length * n₁ + C_p w) % _ = (3 ^ w.length * n₂ + C_p w) % _

    rw [hc₁, hc₂]

  have hmul : 3 ^ w.length * n₁ ≡ 3 ^ w.length * n₂ [MOD 2 ^ (A_total w + 1)] :=

    Nat.ModEq.add_right_cancel' (C_p w) hmod

  exact Nat.ModEq.cancel_left_of_coprime (coprime_three_pow_two_pow w.length (A_total w + 1)).symm hmul



/-! ## §7.3 & §7.4 보정항 상계 및 고정 길이에 대한 유한 해상도 하강 판정 (GARCD-4.4; 원본 v0.3 p.22) -/



/-- 보조정리 7.3.1: 양의 지수열 `w`에서 모든 `j ≤ r`에 대해 `r - j ≤ A_part w r - A_part w j`이다. -/

lemma sub_le_A_part_sub {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {j r : ℕ} (hjr : j ≤ r) (hr : r ≤ w.length) :

    r - j ≤ A_part w r - A_part w j := by

  have h := A_part_mono_add hw hjr hr

  omega



/-- 보조정리 7.3.2: 기본 등비합 항등식 `∑_{j=0}^{r-1} 3^{r-1-j} * 2^j + 2^r = 3^r`. -/

lemma sum_three_pow_mul_two_pow (r : ℕ) :

    (∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ j) + 2 ^ r = 3 ^ r := by

  induction r with

  | zero => simp

  | succ r ih =>

    rw [sum_range_succ]

    have hmul : ∑ x ∈ range r, 3 ^ (r - x) * 2 ^ x = 3 * ∑ x ∈ range r, 3 ^ (r - 1 - x) * 2 ^ x := by

      rw [mul_sum]

      refine sum_congr rfl ?_

      intro x hx

      have hx_lt : x < r := mem_range.mp hx

      have hexp : r - x = (r - 1 - x) + 1 := by omega

      rw [hexp, pow_succ']

      ring

    have hsum_shift :
        (∑ x ∈ range r, 3 ^ (r + 1 - 1 - x) * 2 ^ x) =
          ∑ x ∈ range r, 3 ^ (r - x) * 2 ^ x := by
      apply sum_congr rfl
      intro x hx
      have hshift : r + 1 - 1 - x = r - x := by omega
      rw [hshift]
    rw [hsum_shift, hmul]

    have hexp0 : r + 1 - 1 - r = 0 := by omega

    rw [hexp0, pow_zero, one_mul]

    have hpow2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring

    have hpow3 : 3 ^ (r + 1) = 3 * 3 ^ r := by ring

    linarith



/-- **보조정리 7.3 (보정항의 상계; 원본 v0.3 p.22 식 (14))**:

    양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)와 `r ≥ 1` (`r ≤ w.length`)에 대해:

    (1) 정수 부등식: `0 < C_r(w)` 이고 `2^r * C_r(w) ≤ 2^{A_r(w)} * (3^r - 2^r)` 이다.

    (2) 실수 부등식: `0 < (C_r(w) : ℝ) ≤ 2^{A_r(w)} * ((3/2)^r - 1)` 이다. -/

theorem Lemma_7_3_Correction_Upper_Bound_Nat

    {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {r : ℕ} (hr_pos : 1 ≤ r) (hr_le : r ≤ w.length) :

    0 < C_sum w r ∧ 2 ^ r * C_sum w r ≤ 2 ^ A_part w r * (3 ^ r - 2 ^ r) := by

  constructor

  · unfold C_sum

    have h0 : 0 ∈ range r := mem_range.mpr hr_pos

    have hterm : 0 < 3 ^ (r - 1 - 0) * 2 ^ A_part w 0 := by positivity

    have hsingle : 3 ^ (r - 1 - 0) * 2 ^ A_part w 0 ≤
        ∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ A_part w j := by
      have hnonneg : ∀ j ∈ range r, (0 : ℕ) ≤
          3 ^ (r - 1 - j) * 2 ^ A_part w j := by
        intro j hj
        exact Nat.zero_le _
      exact Finset.single_le_sum hnonneg h0
    exact lt_of_lt_of_le hterm hsingle

  · unfold C_sum

    rw [mul_sum]

    have hbound : ∑ j ∈ range r, 2 ^ r * (3 ^ (r - 1 - j) * 2 ^ A_part w j) ≤

        ∑ j ∈ range r, 2 ^ A_part w r * (3 ^ (r - 1 - j) * 2 ^ j) := by

      refine sum_le_sum ?_

      intro j hj

      have hj_lt : j < r := mem_range.mp hj

      have h_ineq := A_part_mono_add hw (le_of_lt hj_lt) hr_le

      have h_exp : r + A_part w j ≤ A_part w r + j := by omega

      have h_pow : 2 ^ (r + A_part w j) ≤ 2 ^ (A_part w r + j) := Nat.pow_le_pow_right (by omega) h_exp

      calc

        2 ^ r * (3 ^ (r - 1 - j) * 2 ^ A_part w j)

            = 3 ^ (r - 1 - j) * 2 ^ (r + A_part w j) := by rw [pow_add]; ring

        _ ≤ 3 ^ (r - 1 - j) * 2 ^ (A_part w r + j) := Nat.mul_le_mul_left _ h_pow

        _ = 2 ^ A_part w r * (3 ^ (r - 1 - j) * 2 ^ j) := by rw [pow_add]; ring


    have hsum := sum_three_pow_mul_two_pow r

    have hsub : (∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ j) = 3 ^ r - 2 ^ r := by omega

    simpa only [← mul_sum, hsub] using hbound



theorem Lemma_7_3_Correction_Upper_Bound_Real

    {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {r : ℕ} (hr_pos : 1 ≤ r) (hr_le : r ≤ w.length) :

    0 < (C_sum w r : ℝ) ∧ (C_sum w r : ℝ) ≤ (2 : ℝ) ^ A_part w r * (((3 : ℝ) / 2) ^ r - 1) := by

  obtain ⟨hpos, hle⟩ := Lemma_7_3_Correction_Upper_Bound_Nat hw hr_pos hr_le

  constructor

  · exact Nat.cast_pos.mpr hpos

  · have h2le3 : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by omega) r

    have hle_real : (2 : ℝ) ^ r * (C_sum w r : ℝ) ≤ (2 : ℝ) ^ A_part w r * ((3 : ℝ) ^ r - (2 : ℝ) ^ r) := by

      have h1 : ((2 ^ r * C_sum w r : ℕ) : ℝ) ≤ ((2 ^ A_part w r * (3 ^ r - 2 ^ r) : ℕ) : ℝ) :=

        Nat.cast_le.mpr hle

      push_cast [Nat.cast_sub h2le3] at h1

      exact h1

    have h2pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity

    rw [← le_div_iff₀' h2pos] at hle_real

    calc

      (C_sum w r : ℝ) ≤ (2 : ℝ) ^ A_part w r * ((3 : ℝ) ^ r - (2 : ℝ) ^ r) / (2 : ℝ) ^ r := hle_real

      _ = (2 : ℝ) ^ A_part w r * (((3 : ℝ) / 2) ^ r - 1) := by

        rw [mul_div_assoc, sub_div, div_self (ne_of_gt h2pos), div_pow]



/-- 시작값 `n`의 궤적 보정항 `C_orbit n r`에 대한 상계 (보조정리 7.3의 궤적 버전) -/

lemma C_orbit_upper_bound {n : ℕ} (hn : n % 2 = 1) {r : ℕ} (hr_pos : 1 ≤ r) :

    0 < C_orbit n r ∧ 2 ^ r * C_orbit n r ≤ 2 ^ A_orbit n r * (3 ^ r - 2 ^ r) := by

  let w := orbit_word n r

  have hw_len : w.length = r := by simp [w, orbit_word]

  have hw_pos : ∀ a ∈ w, 1 ≤ a := by

    intro a ha

    simp [w, orbit_word] at ha

    rcases ha with ⟨j, _, rfl⟩

    exact a_seq_ge_one hn j

  have hreal : RealizesWord w n := by

    refine ⟨hn, hw_pos, ?_⟩

    intro j hj

    rw [hw_len] at hj

    simp [w, orbit_word, List.getD_eq_getElem _ 0 (by simp [orbit_word, hj])]

  have hA : A_orbit n r = A_part w r :=

    A_orbit_eq_A_part_of_RealizesWord hreal r (by omega)

  have hC : C_orbit n r = C_sum w r :=

    C_orbit_eq_C_sum_of_RealizesWord hreal r (by omega)

  rw [hA, hC]

  exact Lemma_7_3_Correction_Upper_Bound_Nat hw_pos hr_pos (by omega)



/-- 정리 7.4의 임계치 `B_r(L_r) = ((3/2)^r - 1) / (1 - 3^r / 2^{L_r})` (원본 v0.3 p.22) -/

noncomputable def B_threshold (r L_r : ℕ) : ℝ :=

  (((3 : ℝ) / 2) ^ r - 1) / (1 - (3 : ℝ) ^ r / (2 : ℝ) ^ L_r)



/-- **정리 7.4 (GARCD-4.4: 고정된 길이에 대한 유한 해상도 하강 판정; 원본 v0.3 p.22 식 (15))**:

    `r ≥ 1`이고 `L_r : ℕ`가 `2^{L_r - 1} < 3^r < 2^{L_r}` (즉 `L_r = ⌊r log₂ 3⌋ + 1`)를 만족할 때,

    `B_r < n`인 모든 양의 홀수 `n`에 대해

    `F^[r](n) < n ↔ A_r(n) ≥ L_r` 이 성립한다. -/

theorem GARCD_4_4_Finite_Resolution_Descent_Criterion

    {r L_r : ℕ} (hr : 1 ≤ r) (hL_low : 2 ^ (L_r - 1) < 3 ^ r) (hL_high : 3 ^ r < 2 ^ L_r)

    {n : ℕ} (hn_odd : n % 2 = 1) (hn_gt : B_threshold r L_r < (n : ℝ)) :

    x_seq n r < n ↔ L_r ≤ A_orbit n r := by

  rw [GARCD_4_2_Exact_Descent_Iff]

  obtain ⟨hC_pos, hC_bound⟩ := C_orbit_upper_bound hn_odd hr

  constructor

  · intro hdesc

    by_contra hlt

    push_neg at hlt

    have hle : A_orbit n r ≤ L_r - 1 := by omega

    have hpow_le : 2 ^ A_orbit n r ≤ 2 ^ (L_r - 1) := Nat.pow_le_pow_right (by omega) hle

    have hpow_lt : 2 ^ A_orbit n r < 3 ^ r := lt_of_le_of_lt hpow_le hL_low

    have hpow_lt_z : (2 : ℤ) ^ A_orbit n r < (3 : ℤ) ^ r := by exact_mod_cast hpow_lt

    have hn_nonneg : (0 : ℤ) ≤ (n : ℤ) := by positivity

    have hprod_nonpos : ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ) ≤ 0 :=

      mul_nonpos_of_nonpos_of_nonneg (by linarith) hn_nonneg

    have hC_pos_z : (0 : ℤ) < (C_orbit n r : ℤ) := by exact_mod_cast hC_pos

    linarith

  · intro hge

    have hpow_ge : 2 ^ L_r ≤ 2 ^ A_orbit n r := Nat.pow_le_pow_right (by omega) hge

    have hA_gt : 3 ^ r < 2 ^ A_orbit n r := lt_of_lt_of_le hL_high hpow_ge

    have h2le3 : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by omega) r

    have hC_real : (2 : ℝ) ^ r * (C_orbit n r : ℝ) ≤ (2 : ℝ) ^ A_orbit n r * ((3 : ℝ) ^ r - (2 : ℝ) ^ r) := by

      have h1 : ((2 ^ r * C_orbit n r : ℕ) : ℝ) ≤ ((2 ^ A_orbit n r * (3 ^ r - 2 ^ r) : ℕ) : ℝ) :=

        Nat.cast_le.mpr hC_bound

      push_cast [Nat.cast_sub h2le3] at h1

      exact h1

    have h_denom_L : (0 : ℝ) < 1 - (3 : ℝ) ^ r / (2 : ℝ) ^ L_r := by

      rw [sub_pos, div_lt_one (by positivity)]

      exact_mod_cast hL_high

    have h_denom_A : (0 : ℝ) < (2 : ℝ) ^ A_orbit n r - (3 : ℝ) ^ r := by

      rw [sub_pos]

      exact_mod_cast hA_gt

    have h_ratio_le : (3 : ℝ) ^ r / (2 : ℝ) ^ A_orbit n r ≤ (3 : ℝ) ^ r / (2 : ℝ) ^ L_r := by

      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_

      exact_mod_cast hpow_ge

    have hB_ge : (((3 : ℝ) / 2) ^ r - 1) / (1 - (3 : ℝ) ^ r / (2 : ℝ) ^ A_orbit n r) ≤ B_threshold r L_r := by

      unfold B_threshold

      have hnum_nonneg : (0 : ℝ) ≤ ((3 : ℝ) / 2) ^ r - 1 := by

        have : (1 : ℝ) ≤ ((3 : ℝ) / 2) ^ r := one_le_pow₀ (by norm_num)

        linarith

      refine div_le_div_of_nonneg_left hnum_nonneg h_denom_L ?_

      linarith

    have hC_div : (C_orbit n r : ℝ) / ((2 : ℝ) ^ A_orbit n r - (3 : ℝ) ^ r) ≤

        (((3 : ℝ) / 2) ^ r - 1) / (1 - (3 : ℝ) ^ r / (2 : ℝ) ^ A_orbit n r) := by

      have h2pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity

      have hC_le : (C_orbit n r : ℝ) ≤ (2 : ℝ) ^ A_orbit n r * (((3 : ℝ) / 2) ^ r - 1) := by

        rw [← le_div_iff₀' h2pos] at hC_real

        calc

          (C_orbit n r : ℝ) ≤ (2 : ℝ) ^ A_orbit n r * ((3 : ℝ) ^ r - (2 : ℝ) ^ r) / (2 : ℝ) ^ r := hC_real

          _ = (2 : ℝ) ^ A_orbit n r * (((3 : ℝ) / 2) ^ r - 1) := by

            rw [mul_div_assoc, sub_div, div_self (ne_of_gt h2pos), div_pow]

      have h_eq : ((2 : ℝ) ^ A_orbit n r * (((3 : ℝ) / 2) ^ r - 1)) / ((2 : ℝ) ^ A_orbit n r - (3 : ℝ) ^ r) =

          (((3 : ℝ) / 2) ^ r - 1) / (1 - (3 : ℝ) ^ r / (2 : ℝ) ^ A_orbit n r) := by

        have h2A_ne : (2 : ℝ) ^ A_orbit n r ≠ 0 := by positivity

        rw [← div_div_div_cancel_right₀ h2A_ne, mul_div_cancel_left₀ _ h2A_ne, sub_div, div_self h2A_ne]

      rw [← h_eq]

      exact div_le_div_of_nonneg_right hC_le (le_of_lt h_denom_A)

    have h_lt_n : (C_orbit n r : ℝ) / ((2 : ℝ) ^ A_orbit n r - (3 : ℝ) ^ r) < (n : ℝ) :=

      lt_of_le_of_lt (le_trans hC_div hB_ge) hn_gt

    rw [div_lt_iff₀ h_denom_A] at h_lt_n

    conv_rhs => rw [mul_comm]
    exact_mod_cast h_lt_n



/-! ## §7.4 부록 A.1: `r = 3`의 작은 예외, `B_3 = 76 / 5`, 그리고 `r = 2` 절반 하강 판정 (원본 v0.3 p.23 & p.38) -/



/-- **부록 A.1 정리 1 (`r = 3`의 `L_3 = 5`, `B_3 = 76 / 5 = 15.2` 및 작은 홀수 `3..15` 직접 산술 검산; 원본 v0.3 p.38 표)**:

    `B_threshold 3 5 = 76 / 5` 이며, `n ∈ {3, 5, 7, 9, 11, 13, 15}`에 대한 `F^[3](n)` 값과 하강 여부가 표와 정확히 일치한다. -/

theorem Appendix_A1_B3_And_Small_Odd_Table :

    B_threshold 3 5 = 76 / 5 ∧

    x_seq 3 3 = 1 ∧ x_seq 5 3 = 1 ∧ x_seq 7 3 = 13 ∧

    x_seq 9 3 = 17 ∧ x_seq 11 3 = 5 ∧ x_seq 13 3 = 1 ∧ x_seq 15 3 = 53 := by

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · unfold B_threshold

    norm_num

  · change F (F (F 3)) = 1

    simp only [F_explicit_3, F_explicit_5, F_explicit_1]

  · change F (F (F 5)) = 1

    simp only [F_explicit_5, F_explicit_1]

  · change F (F (F 7)) = 13

    simp only [F_explicit_7, F_explicit_11, F_explicit_17]

  · change F (F (F 9)) = 17

    simp only [F_explicit_9, F_explicit_7, F_explicit_11]

  · change F (F (F 11)) = 5

    simp only [F_explicit_11, F_explicit_17, F_explicit_13]

  · change F (F (F 13)) = 1

    simp only [F_explicit_13, F_explicit_5, F_explicit_1]

  · change F (F (F 15)) = 53

    simp only [F_explicit_15, F_explicit_23, F_explicit_35]



/-- **부록 A.1 정리 2 (`r = 2`의 절반 이하 하강 판정; 원본 v0.3 p.23 식 (16) 및 p.38)**:

    홀수 `n ≥ 7`에서 `A_2(n) ≥ 5`이면 항상 `2 * F^[2](n) ≤ n` (즉 `F^[2](n) ≤ n / 2`)이 성립하며,

    작은 홀수 `n = 3, 5`에서도 `F^[2](3) = 1 ≤ 3/2`, `F^[2](5) = 1 ≤ 5/2`가 성립한다. -/

theorem Appendix_A1_Two_Step_Half_Descent

    {n : ℕ} (hn_odd : n % 2 = 1) (hn_ge : 7 ≤ n) (hA2 : 5 ≤ A_orbit n 2) :

    2 * x_seq n 2 ≤ n := by

  rw [GARCD_4_2_Half_Descent_Iff]

  obtain ⟨_, hC_bound⟩ := C_orbit_upper_bound hn_odd (by decide : 1 ≤ 2)

  have hC_le : 4 * C_orbit n 2 ≤ 5 * 2 ^ A_orbit n 2 := by

    norm_num at hC_bound
    omega

  have hpow_ge : 32 ≤ 2 ^ A_orbit n 2 := by

    calc

      32 = 2 ^ 5 := by norm_num

      _ ≤ 2 ^ A_orbit n 2 := Nat.pow_le_pow_right (by omega) hA2

  -- 2 * C_2 ≤ (5/2) * 2^{A_2} 이고, n ≥ 7 에서 (2^{A_2} - 18) * n ≥ (2^{A_2} - 18) * 7 ≥ (5/2) * 2^{A_2}

  have h_ineq_nat : 5 * 2 ^ A_orbit n 2 ≤ 2 * (2 ^ A_orbit n 2 - 18) * n := by

    have h1 : 5 * 2 ^ A_orbit n 2 ≤ 2 * (2 ^ A_orbit n 2 - 18) * 7 := by omega

    have h2 : 2 * (2 ^ A_orbit n 2 - 18) * 7 ≤ 2 * (2 ^ A_orbit n 2 - 18) * n :=

      Nat.mul_le_mul_left _ hn_ge

    exact le_trans h1 h2

  have h_total_nat : 4 * C_orbit n 2 ≤ 2 * (2 ^ A_orbit n 2 - 18) * n :=

    le_trans hC_le h_ineq_nat

  have h_z : 4 * (C_orbit n 2 : ℤ) ≤ 2 * ((2 : ℤ) ^ A_orbit n 2 - 18) * (n : ℤ) := by

    have h18 : 18 ≤ 2 ^ A_orbit n 2 := by omega

    have hcast := Nat.cast_le (α := ℤ).mpr h_total_nat

    push_cast [Nat.cast_sub h18] at hcast

    linarith

  linarith



/-! ## §8 하강 비율의 자연밀도: 유한 단계의 통계 (GARCD-4.5; 원본 v0.3 p.23 정리 8.1) -/



/-- 보완 유한 실패 밀도를 통한 감소 밀도 `δ_r = 1 - ∑_{s = r}^{L_r - 1} C(s-1, r-1) 2^{-s}` (원본 v0.3 p.23 식 (17)) -/

noncomputable def delta_r (r L_r : ℕ) : ℝ :=

  1 - ∑ s ∈ Ico r L_r, (Nat.choose (s - 1) (r - 1) : ℝ) * ((2 : ℝ)⁻¹) ^ s



/-- **정리 8.1 (GARCD-4.5: 고정 `r = 1, 2, 3, 4`의 정확한 감소 밀도 표 검증; 원본 v0.3 p.23 표)**:

    `r = 1 (L_1 = 2) ⟹ δ_1 = 1/2`,

    `r = 2 (L_2 = 4) ⟹ δ_2 = 1/2`,

    `r = 3 (L_3 = 5) ⟹ δ_3 = 11/16`,

    `r = 4 (L_4 = 7) ⟹ δ_4 = 21/32` 이다. -/

theorem GARCD_4_5_Density_Table_Values :

    delta_r 1 2 = 1 / 2 ∧

    delta_r 2 4 = 1 / 2 ∧

    delta_r 3 5 = 11 / 16 ∧

    delta_r 4 7 = 21 / 32 := by

  unfold delta_r

  refine ⟨?_, ?_, ?_, ?_⟩ <;>

  · simp [Finset.sum_Ico_succ_top, Nat.choose]

    norm_num



/-- 주의 8.2의 반례 수열 검증: 매 고정 `r`에 대해 `n = 2^{r+1} - 1`은 첫 `r`번 지수가 `1`이어서 `F^[r](n) > n`이다 (예: `r = 1, 2, 3, 4`). -/

theorem Remark_8_2_Exception_Examples :

    x_seq (2 ^ 2 - 1) 1 > 2 ^ 2 - 1 ∧

    x_seq (2 ^ 3 - 1) 2 > 2 ^ 3 - 1 ∧

    x_seq (2 ^ 4 - 1) 3 > 2 ^ 4 - 1 ∧

    x_seq (2 ^ 5 - 1) 4 > 2 ^ 5 - 1 := by

  decide



/-! ## §9 등비급수 및 가변비율 상계 (보조정리 9.1 및 보조정리 9.3; 원본 v0.3 p.23~24) -/



/-- 보조정리 9.1.1: `a_j(n) ≥ 2`인 한 단계에서 `(x_{j+1}(n) : ℝ) - 1 ≤ (3 / 4) * ((x_j(n) : ℝ) - 1)`이다. -/

lemma strong_valuation_step_bound {n j : ℕ} (ha : 2 ≤ a_seq n j) :

    (x_seq n (j + 1) : ℝ) - 1 ≤ (3 / 4 : ℝ) * ((x_seq n j : ℝ) - 1) := by

  have hstep := syracuse_step_eq n j

  have hpow : 4 ≤ 2 ^ a_seq n j := by

    calc

      4 = 2 ^ 2 := by norm_num

      _ ≤ 2 ^ a_seq n j := Nat.pow_le_pow_right (by omega) ha

  have hmul : 4 * x_seq n (j + 1) ≤ 3 * x_seq n j + 1 := by

    calc

      4 * x_seq n (j + 1) ≤ 2 ^ a_seq n j * x_seq n (j + 1) := Nat.mul_le_mul_right _ hpow

      _ = 3 * x_seq n j + 1 := hstep

  have hmul_real : (4 : ℝ) * (x_seq n (j + 1) : ℝ) ≤ 3 * (x_seq n j : ℝ) + 1 := by

    exact_mod_cast hmul

  linarith



/-- **보조정리 9.1 (강한 valuation 블록 상계; 원본 v0.3 p.23 식 (18))**:

    최초 `r`번의 시러큐스 반복에서 모든 `0 ≤ j < r`에 대해 `a_j(n) ≥ 2`이면:

    (1) 모든 `r ≥ 0`에 대해 `(F^[r](n) : ℝ) ≤ 1 + (3/4)^r * (n - 1)` 이다.

    (2) 특히 `r = 5`이고 `n ≥ 3`이면 `(F^[5](n) : ℝ) ≤ n / 2`이다. -/

theorem Lemma_9_1_Strong_Valuation_Block_Bound

    {n r : ℕ} (ha : ∀ j : ℕ, j < r → 2 ≤ a_seq n j) :

    (x_seq n r : ℝ) ≤ 1 + ((3 : ℝ) / 4) ^ r * ((n : ℝ) - 1) := by

  induction r with

  | zero =>

    simp [x_seq]

  | succ r ih =>

    have ih_r := ih (fun j hj => ha j (by omega))

    have hstep := strong_valuation_step_bound (ha r (by omega))

    calc

      (x_seq n (r + 1) : ℝ) ≤ 1 + (3 / 4 : ℝ) * ((x_seq n r : ℝ) - 1) := by linarith

      _ ≤ 1 + (3 / 4 : ℝ) * (((3 : ℝ) / 4) ^ r * ((n : ℝ) - 1)) := by linarith

      _ = 1 + ((3 : ℝ) / 4) ^ (r + 1) * ((n : ℝ) - 1) := by ring



theorem Lemma_9_1_Five_Steps_Half_Descent

    {n : ℕ} (hn : 3 ≤ n) (ha : ∀ j : ℕ, j < 5 → 2 ≤ a_seq n j) :

    (x_seq n 5 : ℝ) ≤ (n : ℝ) / 2 := by

  have h5 := Lemma_9_1_Strong_Valuation_Block_Bound ha

  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn

  linarith



/-- **보조정리 9.3 (고정 valuation word의 점근비 및 절반 이하 감소 필요충분조건; 원본 v0.3 p.24)**:

    길이 `r ≥ 1`인 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)를 실현하는 양의 정수 `n`에서:

    (1) 정확한 비율 등식: `(F^[r](n) : ℝ) / n - (3^r : ℝ) / 2^{A(w)} = C_p(w) / (2^{A(w)} * n)` 이다

        (따라서 합동류를 따라 `n → ∞`일 때 `F^[r](n) / n → 3^r / 2^{A(w)}`).

    (2) 충분히 큰 합동류 원소 `n`에서 절반 이하 하강 `2 * F^[r](n) ≤ n`이 성립할 필요충분조건은 `2 * 3^r < 2^{A(w)}` 이다. -/

theorem Lemma_9_3_Fixed_Word_Asymptotic_Ratio

    {w : List ℕ} {n : ℕ} (hn : 1 ≤ n) (hreal : RealizesWord w n) :

    (x_seq n w.length : ℝ) / (n : ℝ) - (3 : ℝ) ^ w.length / (2 : ℝ) ^ A_total w =

      (C_p w : ℝ) / ((2 : ℝ) ^ A_total w * (n : ℝ)) := by

  have hA : A_orbit n w.length = A_total w := by

    unfold A_total

    rw [A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _), A_part, List.take_length]

  have hC : C_orbit n w.length = C_p w :=

    C_orbit_eq_C_sum_of_RealizesWord hreal w.length (le_refl _)

  rw [GARCD_4_1_Affine_Iteration_Real n w.length, hA, hC]

  have hn_ne : (n : ℝ) ≠ 0 := by positivity

  have h2_ne : (2 : ℝ) ^ A_total w ≠ 0 := by positivity

  field_simp
  ring



theorem Lemma_9_3_Half_Descent_For_Large_N_Iff

    {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (hr : 1 ≤ w.length) :

    (2 * 3 ^ w.length < 2 ^ A_total w) ↔

      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → RealizesWord w n → 2 * x_seq n w.length ≤ n) := by

  constructor

  · intro hgt

    refine ⟨2 * C_p w + 1, ?_⟩

    intro n hn hreal

    rw [GARCD_4_2_Half_Descent_Iff]

    have hA : A_orbit n w.length = A_total w := by

      unfold A_total

      rw [A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _), A_part, List.take_length]

    have hC : C_orbit n w.length = C_p w :=

      C_orbit_eq_C_sum_of_RealizesWord hreal w.length (le_refl _)

    rw [hA, hC]

    have hdiff_ge_one : (1 : ℤ) ≤ (2 : ℤ) ^ A_total w - 2 * (3 : ℤ) ^ w.length := by

      have : (2 * 3 ^ w.length : ℤ) < (2 ^ A_total w : ℤ) := by exact_mod_cast hgt

      linarith

    have hn_z : 2 * (C_p w : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : 2 * C_p w ≤ n)

    calc

      2 * (C_p w : ℤ) ≤ 1 * (n : ℤ) := by linarith

      _ ≤ ((2 : ℤ) ^ A_total w - 2 * (3 : ℤ) ^ w.length) * (n : ℤ) :=

        mul_le_mul_of_nonneg_right hdiff_ge_one (by positivity)

  · rintro ⟨N₀, hN₀⟩

    by_contra hnot

    push_neg at hnot

    -- 2^A = 2 * 3^r 은 r ≥ 1 에서 불가능하므로 2^A < 2 * 3^r

    have hne : 2 ^ A_total w ≠ 2 * 3 ^ w.length := by

      intro heq

      have hdvd : 3 ∣ 2 ^ A_total w := by

        obtain ⟨k, hk⟩ : ∃ k, w.length = k + 1 := ⟨w.length - 1, by omega⟩

        refine ⟨2 * 3 ^ k, ?_⟩

        rw [heq, hk, pow_succ]

        ring

      have hcop : Nat.Coprime 3 (2 ^ A_total w) := coprime_odd_two_pow (by decide) (A_total w)

      have : 3 ∣ 1 := by

        rw [← hcop.gcd_eq_one]

        exact Nat.dvd_gcd (dvd_refl 3) hdvd

      omega

    have hlt : 2 ^ A_total w < 2 * 3 ^ w.length := lt_of_le_of_ne hnot hne

    -- 법 M = 2^{A+1} 에서 3^r 는 가역이므로 n ≥ N₀ 인 합동류 원소가 존재함

    let M := 2 ^ (A_total w + 1)

    have hcop : Nat.Coprime (3 ^ w.length) M := coprime_three_pow_two_pow w.length (A_total w + 1)

    have hexists : ∃ n : ℕ, N₀ ≤ n ∧ 1 ≤ n ∧ (3 ^ w.length * n + C_p w) % M = 2 ^ A_total w := by

      let u : ZMod M := (3 ^ w.length : ℕ)

      let target : ZMod M := (2 ^ A_total w : ℕ) - (C_p w : ℕ)

      let r0 : ℕ := (target * u⁻¹).val

      refine ⟨r0 + (N₀ + 1) * M, by omega, by omega, ?_⟩

      have hM_pos : 0 < M := by positivity

      haveI : NeZero M := ⟨ne_of_gt hM_pos⟩

      have hu_mul : u * (u⁻¹) = 1 := by

        change ((3 ^ w.length : ℕ) : ZMod M) *

          (((3 ^ w.length : ℕ) : ZMod M)⁻¹) = 1

        exact ZMod.coe_mul_inv_eq_one (3 ^ w.length) hcop

      have h_zmod : ((3 ^ w.length * (r0 + (N₀ + 1) * M) + C_p w : ℕ) : ZMod M) = ((2 ^ A_total w : ℕ) : ZMod M) := by

        push_cast

        have hM_zero : (M : ZMod M) = 0 := ZMod.natCast_self M

        have hr0_cast : (r0 : ZMod M) = target * u⁻¹ := ZMod.natCast_zmod_val (target * u⁻¹)

        rw [hM_zero, mul_zero, add_zero, hr0_cast]

        have hu_eq : u = (3 : ZMod M) ^ w.length := by

          dsimp [u]

          push_cast

          rfl

        rw [← hu_eq]

        calc

          u * (target * u⁻¹) + (C_p w : ZMod M)

              = target * (u * u⁻¹) + (C_p w : ZMod M) := by ring

          _ = target * 1 + (C_p w : ZMod M) := by rw [hu_mul]

          _ = (2 ^ A_total w : ZMod M) := by unfold target; ring

      have h_val := congrArg ZMod.val h_zmod

      simp only [ZMod.val_natCast] at h_val

      rw [h_val]

      exact Nat.mod_eq_of_lt (by unfold M; have : 0 < 2 ^ A_total w := by positivity; omega)

    obtain ⟨n, hn_ge, hn_pos, hn_cong⟩ := hexists

    have hreal : RealizesWord w n := GARCD_4_3_Reverse_Appendix_A2 hw hn_cong

    have hdesc := hN₀ n hn_ge hreal

    rw [GARCD_4_2_Half_Descent_Iff] at hdesc

    have hA : A_orbit n w.length = A_total w := by

      unfold A_total

      rw [A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _), A_part, List.take_length]

    have hC : C_orbit n w.length = C_p w :=

      C_orbit_eq_C_sum_of_RealizesWord hreal w.length (le_refl _)

    rw [hA, hC] at hdesc

    have hdiff_neg : (2 : ℤ) ^ A_total w - 2 * (3 : ℤ) ^ w.length ≤ -1 := by

      have : (2 ^ A_total w : ℤ) < 2 * (3 ^ w.length : ℤ) := by exact_mod_cast hlt

      linarith

    have hn_z : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn_pos

    have hrhs_neg : ((2 : ℤ) ^ A_total w - 2 * (3 : ℤ) ^ w.length) * (n : ℤ) ≤ -1 := by

      nlinarith

    have hlhs_nonneg : (0 : ℤ) ≤ 2 * (C_p w : ℤ) := by positivity

    linarith



end Module2

end GARCD

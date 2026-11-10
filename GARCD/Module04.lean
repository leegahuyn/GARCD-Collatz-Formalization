import GARCD.Module03

open scoped BigOperators
open Finset Real Filter

namespace GARCD




/-!

================================================================================

# MODULE 4: 주기 판정의 대수적 토대 및 순환회전 불변성

  (보충본 §1.1 및 원본 v0.3 §14~§15, GARCD-18 ~ GARCD-30)

================================================================================

-/



section Module4



/-! ## §14.0 원시 지수 블록, 허용 블록 집합 `\mathcal{W}_{adm}`, 그리고 `\gcd(D, 6) = 1` (보충본 §1.1 식 (2) 및 주의 1.2) -/



/-- 리스트 `v`를 `k`번 반복 연결한 word `v^k` -/

def repeatWord (v : List ℕ) : ℕ → List ℕ

  | 0 => []

  | k + 1 => v ++ repeatWord v k



/-- 원시 블록(primitive word)의 정의 (보충본 주의 1.2 및 원본 주의 15.2):

    더 짧은 블록 `v`의 `k ≥ 2`회 반복 `repeatWord v k`로 표현되지 않는 비어 있지 않은 word. -/

def IsPrimitiveWord (w : List ℕ) : Prop :=

  1 ≤ w.length ∧ ∀ v : List ℕ, ∀ k : ℕ, 2 ≤ k → w ≠ repeatWord v k



/-- 원고의 전역 주기 배제 허용 집합 `\mathcal{W}_{adm}` (보충본 §1.1 식 (2)):

    - 모든 지수 `a ∈ w`가 `a ≥ 1`,

    - `w`는 원시 블록 (`IsPrimitiveWord w`),

    - 자명한 `1`의 주기 `w ≠ [2]` (원시 블록 중 모든 원소가 `2`인 유일한 블록은 `[2]`),

    - 정확한 정수 부등식 `3^p < 2^{A(w)}` 및 `7^p * 2^{A(w)} ≤ 22^p`. -/

def IsAdmissibleWord (w : List ℕ) : Prop :=

  (∀ a ∈ w, 1 ≤ a) ∧

  IsPrimitiveWord w ∧

  (∃ a ∈ w, a ≠ 2) ∧

  3 ^ w.length < 2 ^ A_total w ∧

  7 ^ w.length * 2 ^ A_total w ≤ 22 ^ w.length



/-- **보충본 주의 1.2 (`D(w)`의 홀수성 및 `\gcd(D(w), 6) = 1` 증명; 보충본 p.3 & 원본 p.30)**:

    `1 ≤ A_total w`이고 `1 ≤ w.length`이며 `3^p ≤ 2^A`일 때, `D_nat w = 2^A - 3^p`는:

    (1) 홀수(`D_nat w % 2 = 1`)이고,

    (2) `3`으로 나누어떨어지지 않으며(`¬ (3 ∣ D_nat w)`),

    (3) `6`과 서로소(`Nat.Coprime (D_nat w) 6`)이다. -/

theorem Remark_1_2_D_nat_Odd_And_Coprime_Six

    {w : List ℕ} (hA : 1 ≤ A_total w) (hp : 1 ≤ w.length) (hle : 3 ^ w.length ≤ 2 ^ A_total w) :

    D_nat w % 2 = 1 ∧ ¬ (3 ∣ D_nat w) ∧ Nat.Coprime (D_nat w) 6 := by

  unfold D_nat

  have h2_even : 2 ^ A_total w % 2 = 0 := by

    obtain ⟨k, hk⟩ : ∃ k, A_total w = k + 1 := ⟨A_total w - 1, by omega⟩

    rw [hk, pow_succ]

    omega

  have h3_odd : 3 ^ w.length % 2 = 1 := by

    induction w.length with

    | zero => rfl

    | succ k ih => rw [pow_succ]; omega

  have hD_odd : (2 ^ A_total w - 3 ^ w.length) % 2 = 1 := by omega

  have hD_not_dvd_3 : ¬ (3 ∣ (2 ^ A_total w - 3 ^ w.length)) := by

    intro hdvd

    have h3_dvd_3p : 3 ∣ 3 ^ w.length := by

      obtain ⟨k, hk⟩ : ∃ k, w.length = k + 1 := ⟨w.length - 1, by omega⟩

      rw [hk, pow_succ]

      exact dvd_mul_left 3 (3 ^ k)

    have h3_dvd_2A : 3 ∣ 2 ^ A_total w := by

      have h_add := Nat.dvd_add hdvd h3_dvd_3p

      rwa [Nat.sub_add_cancel hle] at h_add

    have hcop32 : Nat.Coprime 3 (2 ^ A_total w) := coprime_odd_two_pow (by decide) (A_total w)

    have : 3 ∣ 1 := by

      rw [← hcop32.gcd_eq_one]

      exact Nat.dvd_gcd (dvd_refl 3) h3_dvd_2A

    omega

  refine ⟨hD_odd, hD_not_dvd_3, ?_⟩

  have hcop2 : Nat.Coprime (2 ^ A_total w - 3 ^ w.length) 2 := by

    rw [Nat.coprime_two_right, Nat.odd_iff]

    exact hD_odd

  have hcop3 : Nat.Coprime (2 ^ A_total w - 3 ^ w.length) 3 := by

    exact ((Nat.prime_three.coprime_iff_not_dvd).2 hD_not_dvd_3).symm

  exact hcop2.mul_right hcop3



/-- 보조정리 14.0.2: 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)이고 `1 ≤ w.length`이면 보정항 `C_p(w)`는 양의 홀수이다 (`C_p w % 2 = 1`). -/

lemma C_p_odd_of_pos_word {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (hp : 1 ≤ w.length) :

    C_p w % 2 = 1 := by

  unfold C_p C_sum

  obtain ⟨k, hk⟩ : ∃ k, w.length = k + 1 := ⟨w.length - 1, by omega⟩

  rw [hk, sum_range_succ']

  simp only [A_part, List.take_zero, List.sum_nil, pow_zero, mul_one, Nat.sub_zero, Nat.add_sub_cancel]

  have h3_odd : 3 ^ k % 2 = 1 := by

    induction k with

    | zero => rfl

    | succ m ih => simpa [pow_succ, Nat.mul_mod, ih]

  have h_sum_even : (∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ (w.take (i + 1)).sum) % 2 = 0 := by

    have hdvd : 2 ∣ ∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ (w.take (i + 1)).sum := by

      refine dvd_sum ?_

      intro i hi

      have hi_lt : i < k := mem_range.mp hi

      have h_ge1 : 1 ≤ (w.take (i + 1)).sum := by

        have hbound := A_part_mono_add hw (Nat.zero_le (i + 1))
          (by omega : i + 1 ≤ w.length)

        have h_lower : i + 1 ≤ (w.take (i + 1)).sum := by
          simpa [A_part] using hbound

        omega

      obtain ⟨m, hm⟩ : ∃ m, (w.take (i + 1)).sum = m + 1 := ⟨(w.take (i + 1)).sum - 1, by omega⟩

      rw [hm, pow_succ]

      exact dvd_mul_of_dvd_right (dvd_mul_left 2 (2 ^ m)) _

    exact Nat.mod_eq_zero_of_dvd hdvd

  have hsum_align :
      (∑ i ∈ range k, 3 ^ (k - (i + 1)) * 2 ^ (w.take (i + 1)).sum) =
      ∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ (w.take (i + 1)).sum := by
    apply Finset.sum_congr rfl
    intro i hi
    have hexp : k - (i + 1) = k - 1 - i := by omega
    rw [hexp]

  rw [hsum_align, Nat.add_mod, h_sum_even, h3_odd]
  norm_num



/-! ## §14.1 & §14.2 양의 홀수 주기의 정확한 방정식 및 필요충분조건 (원본 v0.3 p.30 정리 14.1, 정리 14.2) -/



/-- **정리 14.1 (양의 홀수 주기의 정확한 방정식; 원본 v0.3 p.30)**:

    양의 홀수 `n`이 어떤 `p ≥ 1`에 대해 `x_seq n p = n`이고 지수열 `w` (`w.length = p`)를 실현하면,

    `3^p < 2^{A(w)}`, `0 < C_p(w)`, 그리고 `D_nat w * n = C_p w` 가 성립한다. -/

theorem Theorem_14_1_Positive_Odd_Cycle_Equation

    {w : List ℕ} {n : ℕ} (hp : 1 ≤ w.length) (hreal : RealizesWord w n) (hper : x_seq n w.length = n) :

    3 ^ w.length < 2 ^ A_total w ∧ 0 < C_p w ∧ D_nat w * n = C_p w := by

  have hid := GARCD_4_1_Affine_Iteration_Identity n w.length

  have hA : A_orbit n w.length = A_total w := by

    unfold A_total

    rw [A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _), A_part, List.take_length]

  have hC : C_orbit n w.length = C_p w :=

    C_orbit_eq_C_sum_of_RealizesWord hreal w.length (le_refl _)

  rw [hA, hC, hper] at hid

  have hn_pos : 1 ≤ n := by have := hreal.1; omega

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hreal.2.1 hp (le_refl _)).1

  have hgt : 3 ^ w.length < 2 ^ A_total w := by

    have hmul : 3 ^ w.length * n < 2 ^ A_total w * n := by omega

    exact lt_of_mul_lt_mul_right hmul (Nat.zero_le n)

  refine ⟨hgt, hC_pos, ?_⟩

  unfold D_nat

  rw [Nat.sub_mul]

  omega



/-- **정리 14.2 (정확한 양의 정수 주기 실현 판정 필요충분조건; 보충본 보조정리 1.1 및 원본 v0.3 p.30 정리 14.2)**:

    임의의 양의 정수 지수 블록 `w` (`1 ≤ w.length`, `∀ a ∈ w, 1 ≤ a`)에 대해,

    이 지수 블록을 주기로 실현하는 양의 홀수 `n`이 존재할 필요충분조건은

    `3^p < 2^{A(w)}` (즉 `D(w) > 0`) 이고 `D_nat w ∣ C_p w` 인 것이다. -/

theorem Theorem_14_2_Cycle_Realization_Iff

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a) :

    (∃ n : ℕ, RealizesWord w n ∧ x_seq n w.length = n) ↔

      (3 ^ w.length < 2 ^ A_total w ∧ D_nat w ∣ C_p w) := by

  constructor

  · rintro ⟨n, hreal, hper⟩

    obtain ⟨hgt, _, heq⟩ := Theorem_14_1_Positive_Odd_Cycle_Equation hp hreal hper

    exact ⟨hgt, ⟨n, heq.symm⟩⟩

  · rintro ⟨hgt, ⟨n, hn_eq⟩⟩

    refine ⟨n, ?_, ?_⟩

    · -- C_p w 와 D_nat w 가 모두 홀수이므로 n 도 홀수이고,

      -- 3^p * n + C_p w = 2^A * n ≡ 2^A (mod 2^{A+1}) 이므로 정리 7.1 역방향에 의해 RealizesWord w n 성립!

      have hA_ge1 : 1 ≤ A_total w := by

        unfold A_total

        have := A_part_mono_add hw (Nat.zero_le w.length) (le_refl _)

        simp [A_part] at this

        omega

      have hD_odd : D_nat w % 2 = 1 :=

        (Remark_1_2_D_nat_Odd_And_Coprime_Six hA_ge1 hp (le_of_lt hgt)).1

      have hC_odd : C_p w % 2 = 1 := C_p_odd_of_pos_word hw hp

      have hn_odd : n % 2 = 1 := by

        have hprod_odd : (D_nat w * n) % 2 = 1 := by rw [← hn_eq]; exact hC_odd

        simpa [Nat.mul_mod, hD_odd] using hprod_odd

      have h_2An : 3 ^ w.length * n + C_p w = 2 ^ A_total w * n := by

        have hsub : D_nat w * n = 2 ^ A_total w * n - 3 ^ w.length * n := by

          unfold D_nat

          rw [Nat.sub_mul]

        have hle_mul : 3 ^ w.length * n ≤ 2 ^ A_total w * n :=

          Nat.mul_le_mul_right n (le_of_lt hgt)

        omega

      have hcong : (3 ^ w.length * n + C_p w) % (2 ^ (A_total w + 1)) = 2 ^ A_total w := by

        rw [h_2An]

        have hn_decomp : n = 2 * (n / 2) + 1 := by omega

        calc

          (2 ^ A_total w * n) % (2 ^ (A_total w + 1))

              = (2 ^ A_total w * (2 * (n / 2) + 1)) % (2 ^ (A_total w + 1)) := by rw [← hn_decomp]

          _ = (2 ^ A_total w + 2 ^ (A_total w + 1) * (n / 2)) % (2 ^ (A_total w + 1)) := by ring_nf

          _ = (2 ^ A_total w) % (2 ^ (A_total w + 1)) := Nat.add_mul_mod_self_left _ _ _

          _ = 2 ^ A_total w := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))

      exact GARCD_4_3_Reverse_Appendix_A2 hw hcong

    · -- x_seq n p = n 확인

      have hA_ge1 : 1 ≤ A_total w := by

        unfold A_total

        have := A_part_mono_add hw (Nat.zero_le w.length) (le_refl _)

        simp [A_part] at this

        omega

      have hD_odd : D_nat w % 2 = 1 :=

        (Remark_1_2_D_nat_Odd_And_Coprime_Six hA_ge1 hp (le_of_lt hgt)).1

      have hC_odd : C_p w % 2 = 1 := C_p_odd_of_pos_word hw hp

      have hn_odd : n % 2 = 1 := by

        have hprod_odd : (D_nat w * n) % 2 = 1 := by rw [← hn_eq]; exact hC_odd

        simpa [Nat.mul_mod, hD_odd] using hprod_odd

      have h_2An : 3 ^ w.length * n + C_p w = 2 ^ A_total w * n := by

        have hsub : D_nat w * n = 2 ^ A_total w * n - 3 ^ w.length * n := by

          unfold D_nat

          rw [Nat.sub_mul]

        have hle_mul : 3 ^ w.length * n ≤ 2 ^ A_total w * n :=

          Nat.mul_le_mul_right n (le_of_lt hgt)

        omega

      have hcong : (3 ^ w.length * n + C_p w) % (2 ^ (A_total w + 1)) = 2 ^ A_total w := by

        rw [h_2An]

        have hn_decomp : n = 2 * (n / 2) + 1 := by omega

        calc

          (2 ^ A_total w * n) % (2 ^ (A_total w + 1))

              = (2 ^ A_total w * (2 * (n / 2) + 1)) % (2 ^ (A_total w + 1)) := by rw [← hn_decomp]

          _ = (2 ^ A_total w + 2 ^ (A_total w + 1) * (n / 2)) % (2 ^ (A_total w + 1)) := by ring_nf

          _ = (2 ^ A_total w) % (2 ^ (A_total w + 1)) := Nat.add_mul_mod_self_left _ _ _

          _ = 2 ^ A_total w := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))

      have hreal : RealizesWord w n := GARCD_4_3_Reverse_Appendix_A2 hw hcong

      have hid := GARCD_4_1_Affine_Iteration_Identity n w.length

      have hA : A_orbit n w.length = A_total w := by

        unfold A_total

        rw [A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _), A_part, List.take_length]

      have hC : C_orbit n w.length = C_p w :=

        C_orbit_eq_C_sum_of_RealizesWord hreal w.length (le_refl _)

      rw [hA, hC, h_2An] at hid

      exact Nat.eq_of_mul_eq_mul_left (by positivity) hid



/-- **따름정리 14.3 (소수 거듭제곱별 가분성의 정확한 판정; 원본 v0.3 p.30)**:

    `D_nat w > 0`이고 `C_p w > 0`일 때, `D_nat w ∣ C_p w`일 필요충분조건은

    모든 소수 `q`에 대해 `(D_nat w).factorization q ≤ (C_p w).factorization q` 인 것이다. -/

theorem Corollary_14_3_Prime_Power_Divisibility_Iff

    {w : List ℕ} (hD_pos : 0 < D_nat w) (hC_pos : 0 < C_p w) :

    D_nat w ∣ C_p w ↔ ∀ q : ℕ, (D_nat w).factorization q ≤ (C_p w).factorization q := by

  rw [← Nat.factorization_le_iff_dvd (ne_of_gt hD_pos) (ne_of_gt hC_pos), Finsupp.le_def]



/-! ## §14.4 & §14.5 가중 드리프트 항등식 및 가중 우세 주기 배제 (원본 v0.3 p.30~31 보조정리 14.4, 따름정리 14.5; GARCD-20) -/



/-- 가중치 `W_j(w) = 3^{p - 1 - j} * 2^{A_j(w)}` (원본 v0.3 보조정리 14.4) -/

def W_weight (w : List ℕ) (r j : ℕ) : ℤ :=

  (3 : ℤ) ^ (r - 1 - j) * (2 : ℤ) ^ A_part w j



/-- **보조정리 14.4 (GARCD-20: 가중 드리프트 항등식; 원본 v0.3 p.30 식 (24), (25))**:

    임의의 지수열 `w`에 대해:

    (1) `D_int w = ∑_{j=0}^{p-1} W_j(w) * (2^{w[j]} - 3)` (식 (24))

    (2) `D_int w - C_p(w) = ∑_{j=0}^{p-1} W_j(w) * (2^{w[j]} - 4)` (식 (25)) -/

lemma weighted_drift_partial (w : List ℕ) {r : ℕ} (hr : r ≤ w.length) :

    (∑ j ∈ range r, W_weight w r j * ((2 : ℤ) ^ (w.getD j 0) - 3)) =

      (2 : ℤ) ^ A_part w r - (3 : ℤ) ^ r := by

  induction r with

  | zero =>

    simp [A_part]

  | succ r ih =>

    have hr_lt : r < w.length := by omega

    have ih_r := ih (by omega)

    rw [sum_range_succ]

    have h_scale : (∑ x ∈ range r, W_weight w (r + 1) x * ((2 : ℤ) ^ w.getD x 0 - 3)) =

        3 * ∑ x ∈ range r, W_weight w r x * ((2 : ℤ) ^ w.getD x 0 - 3) := by

      rw [mul_sum]

      refine sum_congr rfl ?_

      intro x hx

      have hx_lt : x < r := mem_range.mp hx

      unfold W_weight

      have hexp : r - x = (r - 1 - x) + 1 := by omega

      rw [hexp, pow_succ']

      ring

    rw [h_scale, ih_r]

    unfold W_weight

    have hexp0 : r - r = 0 := by omega

    rw [hexp0, pow_zero, one_mul]

    have hA_succ : A_part w (r + 1) = A_part w r + w.getD r 0 := by

      unfold A_part

      rw [List.take_succ_eq_append_getElem hr_lt, List.sum_append, List.sum_singleton,

          List.getD_eq_getElem w 0 hr_lt]

    rw [hA_succ, pow_add, pow_succ' (3 : ℤ) r]

    ring



theorem GARCD_20_Weighted_Drift_Identities (w : List ℕ) :

    D_int w = (∑ j ∈ range w.length, W_weight w w.length j * ((2 : ℤ) ^ (w.getD j 0) - 3)) ∧

    D_int w - (C_p w : ℤ) = (∑ j ∈ range w.length, W_weight w w.length j * ((2 : ℤ) ^ (w.getD j 0) - 4)) := by

  have h1 := weighted_drift_partial w (le_refl w.length)

  have hAp : A_part w w.length = A_total w := by

    unfold A_part A_total

    rw [List.take_length]

  rw [hAp] at h1

  constructor

  · unfold D_int

    exact h1.symm

  · have hC : (C_p w : ℤ) = ∑ j ∈ range w.length, W_weight w w.length j := by

      unfold C_p C_sum W_weight

      push_cast

      rfl

    unfold D_int

    rw [← h1, hC, ← sum_sub_distrib]

    refine sum_congr rfl ?_

    intro j _

    ring



/-- **따름정리 14.5 (가중 우세에 의한 주기 배제; 원본 v0.3 p.31)**:

    양의 지수열 `w` (`1 ≤ w.length`, `∀ a ∈ w, 1 ≤ a`)에서

    `0 < ∑_{j=0}^{p-1} W_j(w) * (2^{w[j]} - 4)` 이면 `0 < C_p(w) < D_nat w` 이며 따라서 `¬ (D_nat w ∣ C_p w)` 이다. -/

theorem Corollary_14_5_Weighted_Dominance_Exclusion

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a)

    (hdom : 0 < ∑ j ∈ range w.length, W_weight w w.length j * ((2 : ℤ) ^ (w.getD j 0) - 4)) :

    0 < C_p w ∧ C_p w < D_nat w ∧ ¬ (D_nat w ∣ C_p w) := by

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).1

  have hid := (GARCD_20_Weighted_Drift_Identities w).2

  have hdiff_pos : (C_p w : ℤ) < D_int w := by linarith

  have hD_pos_z : (0 : ℤ) < D_int w := by

    have : (0 : ℤ) < (C_p w : ℤ) := by exact_mod_cast hC_pos

    linarith

  have hle_pow : 3 ^ w.length ≤ 2 ^ A_total w := by

    unfold D_int at hD_pos_z

    have : (3 ^ w.length : ℤ) < (2 ^ A_total w : ℤ) := by linarith

    exact le_of_lt (by exact_mod_cast this)

  have hD_cast : (D_nat w : ℤ) = D_int w := by

    unfold D_nat D_int

    exact Int.ofNat_sub hle_pow

  have hC_lt_D : C_p w < D_nat w := by

    rw [← hD_cast] at hdiff_pos

    exact Int.ofNat_lt.mp hdiff_pos

  refine ⟨hC_pos, hC_lt_D, ?_⟩

  intro hdvd

  have hle := Nat.le_of_dvd hC_pos hdvd

  omega



/-! ## §14.6 유한환 `\mathbb{Z}/m\mathbb{Z}` 지수합 및 소거 동치 (보충본 §3.1 식 (3) 및 원본 v0.3 p.31 정리 14.6) -/



/-- 유한환 `ZMod m` 위의 지수항 `u_j(w, m) = 2^{A_j(w)} * (3^j)⁻¹ ∈ ZMod m` (보충본 식 (3) 및 원본 정리 14.6) -/

def u_mod (w : List ℕ) (m : ℕ) (j : ℕ) : ZMod m :=

  ((2 : ZMod m) ^ A_part w j) * (((3 : ZMod m) ^ j)⁻¹)



/-- 유한환 `ZMod m` 위의 지수합 `S_m(w) = ∑_{j=0}^{p-1} u_j(w, m)` -/

def S_mod (w : List ℕ) (m : ℕ) : ZMod m :=

  ∑ j ∈ range w.length, u_mod w m j



/-- **정리 14.6 (소수 거듭제곱 및 약수 `m`의 유한환 지수합 항등식과 소거 동치; 원본 v0.3 p.31 식 (26))**:

    `m`이 `3`과 서로소인 자연수(`Nat.Coprime 3 m`)일 때:

    (1) `(C_p w : ZMod m) = (3 : ZMod m)^{p - 1} * S_mod w m` 이다.

    (2) `m ∣ C_p w ↔ S_mod w m = 0` 이다. -/

theorem Theorem_14_6_Finite_Ring_Exponential_Sum

    (w : List ℕ) {m : ℕ} (hp : 1 ≤ w.length) (hcop3 : Nat.Coprime 3 m) :

    (C_p w : ZMod m) = (3 : ZMod m) ^ (w.length - 1) * S_mod w m ∧

    (m ∣ C_p w ↔ S_mod w m = 0) := by

  have h1 : (C_p w : ZMod m) = (3 : ZMod m) ^ (w.length - 1) * S_mod w m := by

    unfold C_p C_sum S_mod u_mod

    push_cast

    rw [mul_sum]

    refine sum_congr rfl ?_

    intro j hj

    have hj_lt : j < w.length := mem_range.mp hj

    have hexp : w.length - 1 = (w.length - 1 - j) + j := by omega

    have hcop3j : Nat.Coprime (3 ^ j) m := hcop3.pow_left j

    have h_inv_mul : ((3 : ZMod m) ^ j) * (((3 : ZMod m) ^ j)⁻¹) = 1 := by

      have hcast : ((3 : ZMod m) ^ j) = ((3 ^ j : ℕ) : ZMod m) := by push_cast; rfl

      rw [hcast]

      exact ZMod.coe_mul_inv_eq_one (3 ^ j) hcop3j

    calc

      (3 : ZMod m) ^ (w.length - 1 - j) * (2 : ZMod m) ^ A_part w j

          = (3 : ZMod m) ^ (w.length - 1 - j) * (((3 : ZMod m) ^ j) * (((3 : ZMod m) ^ j)⁻¹)) *

              (2 : ZMod m) ^ A_part w j := by rw [h_inv_mul, mul_one]

      _ = ((3 : ZMod m) ^ (w.length - 1 - j) * (3 : ZMod m) ^ j) *

              ((2 : ZMod m) ^ A_part w j * ((3 : ZMod m) ^ j)⁻¹) := by ring

      _ = (3 : ZMod m) ^ (w.length - 1) *

              ((2 : ZMod m) ^ A_part w j * ((3 : ZMod m) ^ j)⁻¹) := by

            rw [← pow_add, ← hexp]

  refine ⟨h1, ?_⟩

  rw [← ZMod.natCast_eq_zero_iff (C_p w) m, h1]

  have hcop_p1 : Nat.Coprime (3 ^ (w.length - 1)) m := hcop3.pow_left (w.length - 1)

  have h_inv_p1 : (((3 : ZMod m) ^ (w.length - 1))⁻¹) * ((3 : ZMod m) ^ (w.length - 1)) = 1 := by

    rw [mul_comm]

    have hcast : ((3 : ZMod m) ^ (w.length - 1)) = ((3 ^ (w.length - 1) : ℕ) : ZMod m) := by push_cast; rfl

    rw [hcast]

    exact ZMod.coe_mul_inv_eq_one (3 ^ (w.length - 1)) hcop_p1

  constructor

  · intro hzero

    calc

      S_mod w m = 1 * S_mod w m := (one_mul _).symm

      _ = (((3 : ZMod m) ^ (w.length - 1))⁻¹ * (3 : ZMod m) ^ (w.length - 1)) * S_mod w m := by rw [h_inv_p1]

      _ = ((3 : ZMod m) ^ (w.length - 1))⁻¹ * ((3 : ZMod m) ^ (w.length - 1) * S_mod w m) := by ring

      _ = ((3 : ZMod m) ^ (w.length - 1))⁻¹ * 0 := by rw [hzero]

      _ = 0 := mul_zero _

  · intro hS

    rw [hS, mul_zero]



/-! ## §14.8 반복 블록의 공통인수 분해 (GARCD-23; 원본 v0.3 p.31 보조정리 14.8) -/



/-- 반복 블록 공통인수 `S_k(w) = ∑_{t=0}^{k-1} 2^{A(w) * (k - 1 - t)} * 3^{p * t}` (원본 v0.3 보조정리 14.8) -/

def S_repeat_factor (w : List ℕ) (k : ℕ) : ℕ :=

  ∑ t ∈ range k, 2 ^ (A_total w * (k - 1 - t)) * 3 ^ (w.length * t)



/-- 보조정리 14.8.1: `repeatWord w k`의 길이는 `k * w.length`이고 총 지수합은 `k * A_total w`이다. -/

lemma repeatWord_length_and_sum (w : List ℕ) (k : ℕ) :

    (repeatWord w k).length = w.length * k ∧ A_total (repeatWord w k) = A_total w * k := by

  induction k with

  | zero =>

    simp [repeatWord, A_total]

  | succ k ih =>

    unfold repeatWord A_total at ih ⊢

    rw [List.length_append, List.sum_append, ih.1, ih.2]

    constructor <;> ring



/-- **보조정리 14.8 차분 분해 (GARCD-23: `D(w^k) = D(w) * S_k(w)`; 원본 v0.3 p.31)**:

    모든 word `w`와 반복 횟수 `k ≥ 0`에 대해

    `D_int (repeatWord w k) = D_int w * (S_repeat_factor w k : ℤ)` 가 성립한다. -/

theorem GARCD_23_Repeated_Block_D_Decomposition (w : List ℕ) (k : ℕ) :

    D_int (repeatWord w k) = D_int w * (S_repeat_factor w k : ℤ) := by

  obtain ⟨hlen, hsum⟩ := repeatWord_length_and_sum w k

  unfold D_int S_repeat_factor

  rw [hlen, hsum]

  push_cast

  induction k with

  | zero =>

    simp

  | succ k ih =>

    rw [sum_range_succ, mul_add]

    have h_scale : ((2 : ℤ) ^ A_total w - (3 : ℤ) ^ w.length) *

        (∑ x ∈ range k, (2 : ℤ) ^ (A_total w * (k - x)) * (3 : ℤ) ^ (w.length * x)) =

        (2 : ℤ) ^ A_total w * (((2 : ℤ) ^ A_total w - (3 : ℤ) ^ w.length) *

          ∑ x ∈ range k, (2 : ℤ) ^ (A_total w * (k - 1 - x)) * (3 : ℤ) ^ (w.length * x)) := by

      rw [mul_left_comm, mul_sum, mul_sum]

      congr 1

      refine sum_congr rfl ?_

      intro x hx

      have hx_lt : x < k := mem_range.mp hx

      have hexp : A_total w * (k - x) = A_total w + A_total w * (k - 1 - x) := by

        have : k - x = 1 + (k - 1 - x) := by omega

        rw [this, Nat.mul_add, Nat.mul_one]

      rw [hexp, pow_add]

      ring

    rw [h_scale, ← ih]

    have hexp0 : k - k = 0 := by omega

    rw [hexp0, Nat.mul_zero, pow_zero, one_mul]

    rw [Nat.mul_succ, pow_add (2 : ℤ), Nat.mul_succ w.length k, pow_add (3 : ℤ)]

    ring



/-! ## §14.9 & §14.10 모든 시작값에 대한 산술 변위 및 7 이상 홀수 조건 (원본 v0.3 p.31~32 보조정리 14.9, 14.10; GARCD-25~26) -/



/-- **보조정리 14.9 (GARCD-25~26: 모든 시작값에 대한 산술 변위 항등식; 원본 v0.3 p.31)**:

    모든 양의 홀수 `n`과 `p ≥ 1`에 대해

    `((2 : ℤ)^{A_orbit n p} - 3^p) * n - C_orbit n p = 2^{A_orbit n p} * (n - x_seq n p)` 이다. -/

theorem GARCD_25_26_Arithmetic_Displacement_Identity (n p : ℕ) :

    ((2 : ℤ) ^ A_orbit n p - (3 : ℤ) ^ p) * (n : ℤ) - (C_orbit n p : ℤ) =

      (2 : ℤ) ^ A_orbit n p * ((n : ℤ) - (x_seq n p : ℤ)) := by

  have hid := congrArg (Nat.cast : ℕ → ℤ) (GARCD_4_1_Affine_Iteration_Identity n p)

  push_cast at hid

  linarith



/-- **보조정리 14.10 (7 이상의 홀수 및 가상 주기의 공통 조건; 원본 v0.3 p.32)**:

    (1) 모든 자연수 `x`에 대해 `F(x)`는 `3`으로 나누어떨어지지 않는다 (`¬ (3 ∣ F x)`).

    (2) 홀수 `n > 1`에 대해 `n < F(n)`이면 반드시 `a_seq n 0 = 1` 이고 `n % 4 = 3` 이다. -/

theorem Lemma_14_10_Syracuse_Mod_Three_And_Ascent :

    (∀ x : ℕ, ¬ (3 ∣ F x)) ∧

    (∀ n : ℕ, n % 2 = 1 → 1 < n → n < F n → a_seq n 0 = 1 ∧ n % 4 = 3) := by

  constructor

  · intro x hdvd

    have hstep := two_pow_v2_mul_F x

    have h3_dvd : 3 ∣ 2 ^ v2 (3 * x + 1) * F x := dvd_mul_of_dvd_right hdvd _

    rw [hstep] at h3_dvd

    omega

  · intro n hn_odd hn_gt1 h_asc

    have ha_ge1 : 1 ≤ a_seq n 0 := a_seq_ge_one hn_odd 0

    have ha_eq1 : a_seq n 0 = 1 := by

      by_contra hne

      have ha_ge2 : 2 ≤ a_seq n 0 := by omega

      have hpow : 4 ≤ 2 ^ a_seq n 0 := by

        calc

          4 = 2 ^ 2 := by norm_num

          _ ≤ 2 ^ a_seq n 0 := Nat.pow_le_pow_right (by omega) ha_ge2

      have hstep : 2 ^ a_seq n 0 * F n = 3 * n + 1 := two_pow_v2_mul_F n

      have h4 : 4 * F n ≤ 3 * n + 1 := by

        calc

          4 * F n ≤ 2 ^ a_seq n 0 * F n := Nat.mul_le_mul_right (F n) hpow

          _ = 3 * n + 1 := hstep

      omega

    refine ⟨ha_eq1, ?_⟩

    -- a_seq n 0 = 1 이므로 (3 * n + 1) % 4 = 2, 따라서 홀수 n 에 대해 n % 4 = 3

    have hmod4 : (3 * n + 1) % 4 = 2 := by

      have hv2 : v2 (3 * n + 1) = 1 := ha_eq1

      rw [v2_eq_iff_mod_two_pow_succ (by omega)] at hv2

      simpa using hv2

    omega



/-! ## §15 순환회전과 소수별 비소거의 불변성 (GARCD-30; 보충본 보조정리 6.2 및 원본 v0.3 p.32 정리 15.1) -/



/-- 유한 지수열 `w`의 1단계 왼쪽 순환회전(cyclic shift) `σ(w) = w.tail ++ [w.head]` -/

def rotateLeftOne (w : List ℕ) : List ℕ :=

  match w with

  | [] => []

  | a₀ :: tl => tl ++ [a₀]



/-- `j`단계 순환회전 `σ^[j](w)` -/

def rotateLeft (w : List ℕ) (j : ℕ) : List ℕ :=

  (rotateLeftOne^[j]) w



/-- 보조정리 15.1.1: 순환회전 `rotateLeftOne w`는 길이 `w.length`와 총 지수합 `A_total w` (따라서 `D_nat w`, `D_int w`)를 보존한다. -/

lemma rotateLeftOne_length_and_A_total (w : List ℕ) :

    (rotateLeftOne w).length = w.length ∧

    A_total (rotateLeftOne w) = A_total w ∧

    D_nat (rotateLeftOne w) = D_nat w ∧

    D_int (rotateLeftOne w) = D_int w := by

  cases w with

  | nil =>

    simp [rotateLeftOne, A_total, D_nat, D_int]

  | cons a₀ tl =>

    have hlen : (rotateLeftOne (a₀ :: tl)).length = (a₀ :: tl).length := by

      simp [rotateLeftOne]

    have hA : A_total (rotateLeftOne (a₀ :: tl)) = A_total (a₀ :: tl) := by

      simp [rotateLeftOne, A_total, Nat.add_comm]

    refine ⟨hlen, hA, ?_, ?_⟩

    · unfold D_nat

      rw [hlen, hA]

    · unfold D_int

      rw [hlen, hA]



/-- 보조정리 15.1.2: `w = a₀ :: tl`에서 모든 `j ≤ tl.length`에 대해

    `A_part (a₀ :: tl) (j + 1) = a₀ + A_part (tl ++ [a₀]) j` 이다. -/

lemma A_part_cons_succ_eq (a₀ : ℕ) (tl : List ℕ) {j : ℕ} (hj : j ≤ tl.length) :

    A_part (a₀ :: tl) (j + 1) = a₀ + A_part (tl ++ [a₀]) j := by

  unfold A_part

  rw [List.take_succ_cons, List.sum_cons, List.take_append_of_le_length hj]



/-- **정리 15.1 핵심 대수 항등식 (GARCD-30: 순환회전 보정항 항등식 `2^{a_0} C_p(σ w) = 3 C_p(w) + D(w)`; 원본 v0.3 p.32 식 (28) 및 보충본 보조정리 6.2)**:

    비어 있지 않은 모든 지수열 `w = a₀ :: tl`에 대해:

    (1) 자연수 등식: `2^{a₀} * C_p (rotateLeftOne (a₀ :: tl)) + 3^{w.length} = 3 * C_p (a₀ :: tl) + 2^{A_total (a₀ :: tl)}`,

    (2) 정수 등식: `(2 : ℤ)^{a₀} * (C_p (rotateLeftOne (a₀ :: tl)) : ℤ) = 3 * (C_p (a₀ :: tl) : ℤ) + D_int (a₀ :: tl)` 이 성립한다. -/

theorem GARCD_30_Cyclic_Rotation_Identity_Nat (a₀ : ℕ) (tl : List ℕ) :

    2 ^ a₀ * C_p (rotateLeftOne (a₀ :: tl)) + 3 ^ (a₀ :: tl).length =

      3 * C_p (a₀ :: tl) + 2 ^ A_total (a₀ :: tl) := by

  let m := tl.length

  have hlen_w : (a₀ :: tl).length = m + 1 := rfl

  have hlen_rot : (rotateLeftOne (a₀ :: tl)).length = m + 1 := by

    simp [rotateLeftOne, m]

  -- C_p (a₀ :: tl) 를 첫 항 j = 0 과 나머지 j = 1..m 으로 분리

  have hC_w : C_p (a₀ :: tl) = 3 ^ m + ∑ j ∈ range m, 3 ^ (m - 1 - j) * 2 ^ A_part (a₀ :: tl) (j + 1) := by

    unfold C_p C_sum

    rw [hlen_w, sum_range_succ']

    simp only [A_part, List.take_zero, List.sum_nil, pow_zero, mul_one, Nat.sub_zero, Nat.add_sub_cancel]

    rw [Nat.add_comm]

  -- C_p (rotateLeftOne (a₀ :: tl)) 를 앞쪽 j = 0..m-1 과 마지막 항 j = m 으로 분리

  have hC_rot : C_p (rotateLeftOne (a₀ :: tl)) =

      (∑ j ∈ range m, 3 ^ (m - 1 - j) * 2 ^ A_part (tl ++ [a₀]) j) + 2 ^ A_part (tl ++ [a₀]) m := by

    unfold C_p C_sum

    rw [hlen_rot, sum_range_succ]

    congr 1

    · refine sum_congr rfl ?_

      intro j hj

      have hj_lt : j < m := mem_range.mp hj

      have hexp : m - j = m - 1 - j + 1 := by omega

      rfl

    · have hexp0 : m - m = 0 := by omega

      simp [rotateLeftOne, hexp0]

  -- 2^{a₀} * C_p (rotateLeftOne (a₀ :: tl)) 전개

  have h_2a0_rot : 2 ^ a₀ * C_p (rotateLeftOne (a₀ :: tl)) =

      (∑ j ∈ range m, 3 ^ (m - 1 - j) * 2 ^ A_part (a₀ :: tl) (j + 1)) + 2 ^ A_total (a₀ :: tl) := by

    rw [hC_rot, mul_add, mul_sum]

    congr 1

    · refine sum_congr rfl ?_

      intro j hj

      have hj_lt : j < m := mem_range.mp hj

      rw [A_part_cons_succ_eq a₀ tl (le_of_lt hj_lt), pow_add]

      ring

    · have hAm : a₀ + A_part (tl ++ [a₀]) m = A_total (a₀ :: tl) := by

        rw [← A_part_cons_succ_eq a₀ tl (le_refl m)]

        unfold A_part A_total

        have : m + 1 = (a₀ :: tl).length := rfl

        rw [this, List.take_length]

      rw [← pow_add, hAm]

  -- 3 * C_p (a₀ :: tl) 와 비교

  have h_3Cw : 3 * C_p (a₀ :: tl) =

      3 ^ (m + 1) + 3 * ∑ j ∈ range m, 3 ^ (m - 1 - j) * 2 ^ A_part (a₀ :: tl) (j + 1) := by

    rw [hC_w, mul_add, pow_succ']

  -- 실제로 rotateLeftOne 의 각 항 계수는 3^{(m+1) - 1 - j} = 3^{m - j} = 3 * 3^{m - 1 - j} 이다!

  -- 위 hC_rot 에서 (m + 1) - 1 - j = m - j 이므로 이를 정확히 반영하여 다시 정리:

  clear hC_rot h_2a0_rot h_3Cw

  have hC_rot_exact : C_p (rotateLeftOne (a₀ :: tl)) =

      (∑ j ∈ range m, 3 ^ (m - j) * 2 ^ A_part (tl ++ [a₀]) j) + 2 ^ A_part (tl ++ [a₀]) m := by

    unfold C_p C_sum

    rw [hlen_rot, sum_range_succ]

    simp [rotateLeftOne]

  have h_2a0_exact : 2 ^ a₀ * C_p (rotateLeftOne (a₀ :: tl)) =

      3 * (∑ j ∈ range m, 3 ^ (m - 1 - j) * 2 ^ A_part (a₀ :: tl) (j + 1)) + 2 ^ A_total (a₀ :: tl) := by

    rw [hC_rot_exact, mul_add, mul_sum, mul_sum]

    congr 1

    · refine sum_congr rfl ?_

      intro j hj

      have hj_lt : j < m := mem_range.mp hj

      have hexp : m - j = (m - 1 - j) + 1 := by omega

      rw [hexp, pow_succ', A_part_cons_succ_eq a₀ tl (le_of_lt hj_lt), pow_add]

      ring

    · have hAm : a₀ + A_part (tl ++ [a₀]) m = A_total (a₀ :: tl) := by

        rw [← A_part_cons_succ_eq a₀ tl (le_refl m)]

        unfold A_part A_total

        have : m + 1 = (a₀ :: tl).length := rfl

        rw [this, List.take_length]

      rw [← pow_add, hAm]

  rw [h_2a0_exact, hC_w, hlen_w, pow_succ']

  ring



theorem GARCD_30_Cyclic_Rotation_Identity_Int (a₀ : ℕ) (tl : List ℕ) :

    (2 : ℤ) ^ a₀ * (C_p (rotateLeftOne (a₀ :: tl)) : ℤ) =

      3 * (C_p (a₀ :: tl) : ℤ) + D_int (a₀ :: tl) := by

  have hnat := congrArg (Nat.cast : ℕ → ℤ) (GARCD_30_Cyclic_Rotation_Identity_Nat a₀ tl)

  push_cast at hnat

  unfold D_int

  linarith



/-- **정리 15.1 최대공약수 및 가분성 불변성 (GARCD-30: `\gcd(D, C_p(\sigma^j w)) = \gcd(D, C_p(w))` 및 `D ∣ C_p(\sigma^j w) ↔ D ∣ C_p(w)`; 원본 v0.3 p.32)**:

    `1 ≤ A_total w`, `1 ≤ w.length`, `3^{w.length} ≤ 2^{A_total w}`를 만족하는 지수열 `w`에 대해:

    (1) 1단계 회전에서 `Nat.gcd (D_nat w) (C_p (rotateLeftOne w)) = Nat.gcd (D_nat w) (C_p w)` 이다.

    (2) 임의의 `j ≥ 0`단계 회전 `rotateLeft w j`에서

        `Nat.gcd (D_nat w) (C_p (rotateLeft w j)) = Nat.gcd (D_nat w) (C_p w)` 및

        `(D_nat w ∣ C_p (rotateLeft w j) ↔ D_nat w ∣ C_p w)` 가 성립한다. -/

theorem GARCD_30_Cyclic_Rotation_GCD_Invariance_One

    {w : List ℕ} (hA : 1 ≤ A_total w) (hp : 1 ≤ w.length) (hle : 3 ^ w.length ≤ 2 ^ A_total w) :

    Nat.gcd (D_nat w) (C_p (rotateLeftOne w)) = Nat.gcd (D_nat w) (C_p w) := by

  cases w with

  | nil => simp at hp

  | cons a₀ tl =>

    obtain ⟨hD_odd, hD_not3, _⟩ := Remark_1_2_D_nat_Odd_And_Coprime_Six hA hp hle

    have hcop2 : Nat.Coprime (D_nat (a₀ :: tl)) (2 ^ a₀) :=

      coprime_odd_two_pow hD_odd a₀

    have hcop3 : Nat.Coprime (D_nat (a₀ :: tl)) 3 := by

      exact ((Nat.prime_three.coprime_iff_not_dvd).2 hD_not3).symm

    have hid_nat := GARCD_30_Cyclic_Rotation_Identity_Nat a₀ tl

    have h_rel_D : 2 ^ a₀ * C_p (rotateLeftOne (a₀ :: tl)) =

        3 * C_p (a₀ :: tl) + D_nat (a₀ :: tl) := by

      unfold D_nat

      omega

    calc

      Nat.gcd (D_nat (a₀ :: tl)) (C_p (rotateLeftOne (a₀ :: tl)))

          = Nat.gcd (D_nat (a₀ :: tl)) (2 ^ a₀ * C_p (rotateLeftOne (a₀ :: tl))) :=

            (hcop2.symm.gcd_mul_left_cancel_right (C_p (rotateLeftOne (a₀ :: tl)))).symm

      _ = Nat.gcd (D_nat (a₀ :: tl)) (3 * C_p (a₀ :: tl) + D_nat (a₀ :: tl)) := by

            rw [h_rel_D]

      _ = Nat.gcd (D_nat (a₀ :: tl)) (3 * C_p (a₀ :: tl)) := by

            rw [Nat.gcd_add_self_right]

      _ = Nat.gcd (D_nat (a₀ :: tl)) (C_p (a₀ :: tl)) :=

            hcop3.symm.gcd_mul_left_cancel_right (C_p (a₀ :: tl))



theorem GARCD_30_Cyclic_Rotation_Invariance_All

    {w : List ℕ} (hA : 1 ≤ A_total w) (hp : 1 ≤ w.length) (hle : 3 ^ w.length ≤ 2 ^ A_total w) (j : ℕ) :

    Nat.gcd (D_nat w) (C_p (rotateLeft w j)) = Nat.gcd (D_nat w) (C_p w) ∧

    (D_nat w ∣ C_p (rotateLeft w j) ↔ D_nat w ∣ C_p w) := by

  have h_all : ∀ k : ℕ,

      (rotateLeft w k).length = w.length ∧

      A_total (rotateLeft w k) = A_total w ∧

      D_nat (rotateLeft w k) = D_nat w ∧

      Nat.gcd (D_nat w) (C_p (rotateLeft w k)) = Nat.gcd (D_nat w) (C_p w) := by

    intro k

    induction k with

    | zero =>

      simp [rotateLeft]

    | succ k ih =>

      obtain ⟨hlen_k, hA_k, hD_k, hgcd_k⟩ := ih

      have h_step := rotateLeftOne_length_and_A_total (rotateLeft w k)

      have h_rot_succ : rotateLeft w (k + 1) = rotateLeftOne (rotateLeft w k) :=

        Function.iterate_succ_apply' rotateLeftOne k w

      rw [h_rot_succ]

      refine ⟨by rw [h_step.1, hlen_k], by rw [h_step.2.1, hA_k], by rw [h_step.2.2.1, hD_k], ?_⟩

      have hA_k_ge1 : 1 ≤ A_total (rotateLeft w k) := by rw [hA_k]; exact hA

      have hp_k_ge1 : 1 ≤ (rotateLeft w k).length := by rw [hlen_k]; exact hp

      have hle_k : 3 ^ (rotateLeft w k).length ≤ 2 ^ A_total (rotateLeft w k) := by

        rw [hlen_k, hA_k]; exact hle

      have hgcd_step := GARCD_30_Cyclic_Rotation_GCD_Invariance_One hA_k_ge1 hp_k_ge1 hle_k

      rw [hD_k] at hgcd_step

      rw [hgcd_step, hgcd_k]

  have hgcd := (h_all j).2.2.2

  refine ⟨hgcd, ?_⟩

  rw [← Nat.gcd_eq_left_iff_dvd, ← Nat.gcd_eq_left_iff_dvd, hgcd]



end Module4

end GARCD

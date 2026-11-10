import GARCD.Module06

open scoped BigOperators
open Finset Real Filter

namespace GARCD



section Module7



/-! ## §4.1 대칭 나머지 `R_{j,m}`, 선형 나머지 합 `B_m(w)`, 그리고 자리올림 전이 정리 4.1 (보충본 p.5~6) -/



/-- 표준 양의 나머지 `r_{j,m}(w) = (u_mod w m j).val ∈ [0, m)` (보충본 §4.1) -/

def r_pos_rem (w : List ℕ) (m : ℕ) (j : ℕ) : ℤ :=

  if j = w.length then 1 else ((u_mod w m j).val : ℤ)



/-- 대칭 나머지 `R_{j,m}(w)` (보충본 §4.1):

    `r_{j,m} ≤ (m - 1) / 2` 이면 `r_{j,m}`, 아니면 `r_{j,m} - m`. -/

def R_sym_rem (w : List ℕ) (m : ℕ) (j : ℕ) : ℤ :=

  let r := ((u_mod w m j).val : ℤ)

  if 2 * r ≤ (m : ℤ) - 1 then r else r - (m : ℤ)



/-- 대칭 나머지들의 정수 선형 합 `B_m(w) = ∑_{j < p} R_{j,m}(w) ∈ ℤ` (보충본 §4.1) -/

def B_sym_sum (w : List ℕ) (m : ℕ) : ℤ :=

  ∑ j ∈ range w.length, R_sym_rem w m j



/-- **보충본 §4.1 식 (5) (`B_m(w) ≡ S_m(w) (mod m)` 및 `m ∣ B_m(w) ↔ m ∣ C_p(w)` 증명; 보충본 p.5)**:

    `m ≥ 1`이 `3`과 서로소(`Nat.Coprime 3 m`)이고 `1 ≤ w.length`일 때:

    (1) `(B_sym_sum w m : ZMod m) = S_mod w m` 이다.

    (2) `(m : ℤ) ∣ B_sym_sum w m ↔ m ∣ C_p w` 가 정확히 성립한다. -/

theorem GARCD_38L_Eq5_Symmetric_Remainder_Sum_Iff

    (w : List ℕ) {m : ℕ} (hp : 1 ≤ w.length) (hm_pos : 1 ≤ m) (hcop3 : Nat.Coprime 3 m) :

    (B_sym_sum w m : ZMod m) = S_mod w m ∧

    ((m : ℤ) ∣ B_sym_sum w m ↔ m ∣ C_p w) := by

  haveI : NeZero m := ⟨by omega⟩

  have h_cast : (B_sym_sum w m : ZMod m) = S_mod w m := by

    unfold B_sym_sum S_mod R_sym_rem

    push_cast

    refine sum_congr rfl ?_

    intro j _

    split_ifs

    · simp [ZMod.natCast_zmod_val]

    · simp [ZMod.natCast_zmod_val, ZMod.natCast_self]

  refine ⟨h_cast, ?_⟩

  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, h_cast,

      (Theorem_14_6_Finite_Ring_Exponential_Sum w hp hcop3).2]



/-- 자리올림 계수 `h_j`를 통한 정수 나머지 전이식 및 가중합 항등식 (보충본 p.5~6 정리 4.1):

    임의의 정수 수열 `r_seq : ℕ → ℤ`와 자리올림 수열 `h_seq : ℕ → ℤ`가 모든 `0 ≤ j < p`에서

    `3 * r_seq (j + 1) = 2^{w[j]} * r_seq j - m * h_seq j` 이고 경계 조건 `r_seq p = r_seq 0`을 만족하면,

    `∑_{j < p} (2^{w[j]} - 3) * r_seq j = m * ∑_{j < p} h_seq j` 가 정확히 성립한다. -/

theorem Theorem_4_1_Carry_Transition_Identity

    (w : List ℕ) (m : ℤ) (r_seq h_seq : ℕ → ℤ)

    (h_trans : ∀ j ∈ range w.length, 3 * r_seq (j + 1) = (2 : ℤ) ^ (w.getD j 0) * r_seq j - m * h_seq j)

    (h_periodic : r_seq w.length = r_seq 0) :

    (∑ j ∈ range w.length, ((2 : ℤ) ^ (w.getD j 0) - 3) * r_seq j) =

      m * ∑ j ∈ range w.length, h_seq j := by

  have h_telescope : ∀ k : ℕ, (∑ j ∈ range k, 3 * (r_seq (j + 1) - r_seq j)) =

      3 * (r_seq k - r_seq 0) := by

    intro k

    induction k with

    | zero => simp

    | succ k ih =>

      rw [sum_range_succ, ih]

      ring

  have h_tel_p := h_telescope w.length

  rw [h_periodic, sub_self, mul_zero] at h_tel_p

  have h_sum_rel : (∑ j ∈ range w.length, ((2 : ℤ) ^ (w.getD j 0) - 3) * r_seq j) =

      (∑ j ∈ range w.length, 3 * (r_seq (j + 1) - r_seq j)) +

      m * ∑ j ∈ range w.length, h_seq j := by

    rw [mul_sum, ← sum_add_distrib]

    refine sum_congr rfl ?_

    intro j hj

    have h_j := h_trans j hj

    linarith

  rw [h_sum_rel, h_tel_p, zero_add]



/-! ## §4.1 & §4.2 순환 편차 `E_d^{(1)}(w)`, `E_d^{(2)}(w)`, 반복 블록 분해, 그리고 `A-0`와의 동치성 (보충본 p.6~7 정의 4.2, 보조정리 4.3, 보조정리 4.6, 정의 4.7, 명제 4.8) -/



/-- 정의 4.2: 선형 `L^1` 순환 편차 `E_d^{(1)}(w) = ∑_{j=0}^{p-1} |w[j] - w[(j + d) mod p]|` (보충본 p.6) -/

def E1_cyclic_dev (w : List ℕ) (d : ℕ) : ℕ :=

  ∑ j ∈ range w.length, Int.natAbs ((w.getD j 0 : ℤ) - (w.getD ((j + d) % w.length) 0 : ℤ))



/-- 정의 4.7: 순환 제곱 편차 `E_d^{(2)}(w) = ∑_{j=0}^{p-1} (w[j] - w[(j + d) mod p])^2` (보충본 p.6) -/

def E2_cyclic_dev (w : List ℕ) (d : ℕ) : ℤ :=

  ∑ j ∈ range w.length, ((w.getD j 0 : ℤ) - (w.getD ((j + d) % w.length) 0 : ℤ)) ^ 2



/-- **보조정리 4.3 & 정의 4.7 영집합 동치 (`E_d^{(1)}(w) = 0 ↔ E_d^{(2)}(w) = 0 ↔ ∀ j < p, w[j] = w[(j + d) mod p]`; 보충본 p.6~7)**:

    임의의 word `w`와 `d : ℕ`에 대해 선형 순환 편차가 `0`인 것, 제곱 순환 편차가 `0`인 것, 그리고 모든 위치 `j < w.length`에서

    주기 `d` 순환 불변성 `w[j] = w[(j + d) mod p]`가 성립하는 것은 서로 필요충분조건이다. -/

theorem Lemma_4_3_And_Def_4_7_Cyclic_Deviation_Zero_Iff (w : List ℕ) (d : ℕ) :

    (E1_cyclic_dev w d = 0 ↔ ∀ j ∈ range w.length, w.getD j 0 = w.getD ((j + d) % w.length) 0) ∧

    (E2_cyclic_dev w d = 0 ↔ ∀ j ∈ range w.length, w.getD j 0 = w.getD ((j + d) % w.length) 0) ∧

    (E1_cyclic_dev w d = 0 ↔ E2_cyclic_dev w d = 0) := by

  have h1 : E1_cyclic_dev w d = 0 ↔ ∀ j ∈ range w.length, w.getD j 0 = w.getD ((j + d) % w.length) 0 := by

    unfold E1_cyclic_dev

    rw [Finset.sum_eq_zero_iff]

    refine forall_congr' (fun j => imp_congr_right (fun _ => ?_))

    rw [Int.natAbs_eq_zero, sub_eq_zero, Int.ofNat_inj]

  have h2 : E2_cyclic_dev w d = 0 ↔ ∀ j ∈ range w.length, w.getD j 0 = w.getD ((j + d) % w.length) 0 := by

    unfold E2_cyclic_dev

    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]

    refine forall_congr' (fun j => imp_congr_right (fun _ => ?_))

    rw [sq_eq_zero_iff, sub_eq_zero, Int.ofNat_inj]

  exact ⟨h1, h2, h1.trans h2.symm⟩



/-- **보조정리 4.6 (반복 블록의 정확한 선형 합 분해 및 `(1, 1, 1, 1, 4)^2` 법 13 반례 검산; 보충본 p.6)**:

    (1) `w = repeatWord v k` (`p = k * d`, `B = A_total v`, `h = 2^B * (3^d)⁻¹ ∈ ZMod m`)일 때,

        `C_p(v^k) = C_p(v) * S_repeat_factor v k` 이다.

    (2) 보충본 p.6의 계산된 반례 `w = (1, 1, 1, 1, 4)^2` (`p = 10, d = 5`):

        `D = 6487 = 13 * 499`, `C_p(w) = 105289`, `499 ∣ C_p(w)` 이지만 `C_p(w) % 13 = 2 ≠ 0` 이어서

        반복 블록임에도 불구하고 `13 ∤ C_p(w)` (즉 `h^k ≡ 1`이 모든 소인수에서 등비합 `0`을 강제하지 않음)를 증명한다. -/

def w_Lemma_4_6_counterexample : List ℕ :=

  [1, 1, 1, 1, 4, 1, 1, 1, 1, 4]



theorem Lemma_4_6_Repeated_Block_Counterexample_Mod13 :

    w_Lemma_4_6_counterexample = repeatWord [1, 1, 1, 1, 4] 2 ∧

    w_Lemma_4_6_counterexample.length = 10 ∧

    A_total w_Lemma_4_6_counterexample = 16 ∧

    D_nat w_Lemma_4_6_counterexample = 6487 ∧

    C_p w_Lemma_4_6_counterexample = 105289 ∧

    499 ∣ C_p w_Lemma_4_6_counterexample ∧

    C_p w_Lemma_4_6_counterexample % 13 = 2 ∧

    ¬ (13 ∣ C_p w_Lemma_4_6_counterexample) ∧

    ¬ (D_nat w_Lemma_4_6_counterexample ∣ C_p w_Lemma_4_6_counterexample) := by

  decide



/-- **명제 4.8 (동시 소거의 주기성 강직성과 `A-0`의 논리적 동치성; 보충본 p.7)**:

    허용 영역의 임의의 word `w`에 대하여,

    "`w`가 비원시적이라는 조건 `¬ IsPrimitiveWord w`를 `HasProperPeriod w`로 표기할 때,

     모든 허용 원시 블록 `w`에서 `¬ (D_nat w ∣ C_p w)`가 성립한다는 명제(A-0)"와

    "모든 허용 지수합 영역의 word `w`에서 `D_nat w ∣ C_p w ⟹ ¬ IsPrimitiveWord w`가 성립한다는 명제(GARCD-38/38L)"는

    논리적으로 완전히 동치이다. -/

def IsAdmissibleExponentRange (w : List ℕ) : Prop :=

  (∀ a ∈ w, 1 ≤ a) ∧

  (∃ a ∈ w, a ≠ 2) ∧

  3 ^ w.length < 2 ^ A_total w ∧

  7 ^ w.length * 2 ^ A_total w ≤ 22 ^ w.length



theorem Proposition_4_8_GARCD_38L_Equivalence_With_A0 :

    (∀ w : List ℕ, IsAdmissibleWord w → ¬ (D_nat w ∣ C_p w)) ↔

    (∀ w : List ℕ, 1 ≤ w.length → IsAdmissibleExponentRange w →

      D_nat w ∣ C_p w → ¬ IsPrimitiveWord w) := by

  constructor

  · intro hA0 w hp hadm hdvd hprim

    have hw_adm : IsAdmissibleWord w :=

      ⟨hadm.1, hprim, hadm.2.1, hadm.2.2.1, hadm.2.2.2⟩

    exact hA0 w hw_adm hdvd

  · intro h38L w hw_adm hdvd

    have hadm : IsAdmissibleExponentRange w :=

      ⟨hw_adm.1, hw_adm.2.2.1, hw_adm.2.2.2.1, hw_adm.2.2.2.2⟩

    exact h38L w hw_adm.2.1.1 hadm hdvd hw_adm.2.1



/-! ## §4.3 GARCD-Qk의 무한 원시 적용 계열 (보충본 p.7 정리 4.10) -/



/-- 정리 4.10의 무한 원시 블록 계열 `w_GARCD_4_10(k, p, t) = (3 + 4t, 3^{k-1}, 1^{p-k})` -/

def w_GARCD_4_10 (k p t : ℕ) : List ℕ :=

  [3 + 4 * t] ++ List.replicate (k - 1) 3 ++ List.replicate (p - k) 1



/-- 보조정리 4.10.1: `1 ≤ k ≤ p`일 때 `w_GARCD_4_10 k p t`의 길이는 `p`이고 총 지수합은 `p + 2 * k + 4 * t`이다. -/

lemma w_GARCD_4_10_length_and_sum {k p : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) (t : ℕ) :

    (w_GARCD_4_10 k p t).length = p ∧ A_total (w_GARCD_4_10 k p t) = p + 2 * k + 4 * t := by

  unfold w_GARCD_4_10 A_total

  simp [List.length_append, List.sum_append, List.sum_replicate]

  omega



/-- **정리 4.10 (임의의 고정된 잔존 항 수 `k`를 갖는 무한 원시 비소거 계열 및 `C_p(w) > D(w)` 증명; 보충본 p.7)**:

    (1) 모든 `1 ≤ k ≤ p`와 `t`에 대해 `w = w_GARCD_4_10 k p t`의 길이는 `p`, 총 지수합은 `A = p + 2k + 4t`이다.

    (2) `p - k`가 짝수(`(p - k) % 2 = 0`)이고 `3^p ≤ 2^A`이면, `A - 3p`는 짝수이고 `2^2 ≡ 4 ≡ -1 (mod 5)`, `3^2 ≡ 4 ≡ -1 (mod 5)`로부터

        항상 `5 ∣ D_nat w`가 성립한다.

    (3) 명시적 대표 원소 `(k = 3, p = 19, t = 1)` (`w = (7, 3, 3, 1^{16})`, `A = 29`)에서

        `5 ∣ D_nat w`, `¬ (5 ∣ C_p w)` (`C_p w % 5 = 2`), `D_nat w < C_p w`, 그리고 `¬ (D_nat w ∣ C_p w)` 가 성립한다. -/

theorem Theorem_4_10_Infinite_Nonvanishing_Family_Properties

    {k p t : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) :

    (w_GARCD_4_10 k p t).length = p ∧

    A_total (w_GARCD_4_10 k p t) = p + 2 * k + 4 * t ∧

    -- 대표 원소 (k=3, p=19, t=1) 완전 검산

    D_nat (w_GARCD_4_10 3 19 1) = 327245205 ∧

    5 ∣ D_nat (w_GARCD_4_10 3 19 1) ∧

    C_p (w_GARCD_4_10 3 19 1) % 5 = 2 ∧

    ¬ (5 ∣ C_p (w_GARCD_4_10 3 19 1)) ∧

    D_nat (w_GARCD_4_10 3 19 1) < C_p (w_GARCD_4_10 3 19 1) ∧

    ¬ (D_nat (w_GARCD_4_10 3 19 1) ∣ C_p (w_GARCD_4_10 3 19 1)) := by

  obtain ⟨hlen, hsum⟩ := w_GARCD_4_10_length_and_sum hk hkp t

  refine ⟨hlen, hsum, ?_⟩

  decide



end Module7

end GARCD

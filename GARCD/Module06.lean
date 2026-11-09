import GARCD.Module05

open scoped BigOperators
open Finset Real Filter

namespace GARCD




/-!

================================================================================

# MODULE 6: 소인수별 선형 전이와 제곱 나머지 판별식

  (보충본 §3, GARCD-35 ~ 38, Q1 / Q2 / Q3 / Qk / SQ)

================================================================================

-/



section Module6



/-! ## §3.1 전이 계수 `\lambda_j`, 전이항 `t_j = (1 + \lambda_j) u_j`, 그리고 식 (4) 선형 전이 합 항등식 (보충본 p.4) -/



/-- 유한환 `ZMod m` 위의 단계별 전이 계수 `λ_j(w, m) = 2^{w[j]} * 3⁻¹ ∈ ZMod m` (보충본 §3.1 식 (3)) -/

def lambda_mod (w : List ℕ) (m : ℕ) (j : ℕ) : ZMod m :=

  ((2 : ZMod m) ^ (w.getD j 0)) * ((3 : ZMod m)⁻¹)



/-- 유한환 `ZMod m` 위의 선형 전이항 `t_j(w, m) = (1 + λ_j(w, m)) * u_j(w, m) ∈ ZMod m` (보충본 정리 3.2) -/

def t_trans (w : List ℕ) (m : ℕ) (j : ℕ) : ZMod m :=

  (1 + lambda_mod w m j) * u_mod w m j



/-- 보조정리 6.0.1: `m`이 `3`과 서로소일 때:

    (1) `u_mod w m 0 = 1`,

    (2) 모든 `j < w.length`에 대해 `u_mod w m (j + 1) = lambda_mod w m j * u_mod w m j`,

    (3) 만약 `m ∣ D_nat w`이고 `3^{w.length} ≤ 2^{A_total w}`이면 `u_mod w m w.length = 1` 이다 (보충본 §3.1 식 (3) 직후). -/

lemma u_mod_zero (w : List ℕ) (m : ℕ) : u_mod w m 0 = 1 := by

  simp [u_mod, A_part]



lemma u_mod_succ_eq_lambda_mul (w : List ℕ) {m : ℕ} (hcop3 : Nat.Coprime 3 m)

    {j : ℕ} (hj : j < w.length) :

    u_mod w m (j + 1) = lambda_mod w m j * u_mod w m j := by

  unfold u_mod lambda_mod

  have hA_succ : A_part w (j + 1) = A_part w j + w.getD j 0 := by

    unfold A_part

    rw [List.take_succ_eq_append_getElem hj, List.sum_append, List.sum_singleton,

        List.getD_eq_getElem w 0 hj]

  rw [hA_succ, pow_add, pow_succ (3 : ZMod m) j]

  -- (3^j * 3)⁻¹ = (3^j)⁻¹ * 3⁻¹ in ZMod m

  have hcop3j : Nat.Coprime (3 ^ j) m := hcop3.pow_left j

  have hcop3j1 : Nat.Coprime (3 ^ (j + 1)) m := hcop3.pow_left (j + 1)

  have h_inv3 : (3 : ZMod m) * (3 : ZMod m)⁻¹ = 1 := by

    exact ZMod.coe_mul_inv_eq_one 3 hcop3

  have h_inv3j : ((3 : ZMod m) ^ j) * (((3 : ZMod m) ^ j)⁻¹) = 1 := by

    have hcast : ((3 : ZMod m) ^ j) = ((3 ^ j : ℕ) : ZMod m) := by push_cast; rfl

    rw [hcast]

    exact ZMod.coe_mul_inv_eq_one (3 ^ j) hcop3j

  have h_inv3j1 : ((3 : ZMod m) ^ j * (3 : ZMod m)) * (((3 : ZMod m) ^ j * (3 : ZMod m))⁻¹) = 1 := by

    have hcast : ((3 : ZMod m) ^ j * (3 : ZMod m)) = ((3 ^ (j + 1) : ℕ) : ZMod m) := by

      push_cast; rw [pow_succ]

    rw [hcast]

    exact ZMod.coe_mul_inv_eq_one (3 ^ (j + 1)) hcop3j1

  have h_inv_prod : (((3 : ZMod m) ^ j * (3 : ZMod m))⁻¹) = (((3 : ZMod m) ^ j)⁻¹) * ((3 : ZMod m)⁻¹) := by

    calc

      (((3 : ZMod m) ^ j * (3 : ZMod m))⁻¹)

          = (((3 : ZMod m) ^ j * (3 : ZMod m))⁻¹) * 1 := (mul_one _).symm

      _ = (((3 : ZMod m) ^ j * (3 : ZMod m))⁻¹) *

            ((((3 : ZMod m) ^ j) * (((3 : ZMod m) ^ j)⁻¹)) * ((3 : ZMod m) * (3 : ZMod m)⁻¹)) := by

            rw [h_inv3j, h_inv3, mul_one]

      _ = (((3 : ZMod m) ^ j * (3 : ZMod m)) * (((3 : ZMod m) ^ j * (3 : ZMod m))⁻¹)) *

            ((((3 : ZMod m) ^ j)⁻¹) * ((3 : ZMod m)⁻¹)) := by ring

      _ = (((3 : ZMod m) ^ j)⁻¹) * ((3 : ZMod m)⁻¹) := by rw [h_inv3j1, one_mul]

  rw [h_inv_prod]

  ring



lemma u_mod_length_eq_one (w : List ℕ) {m : ℕ} (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd : m ∣ D_nat w) :

    u_mod w m w.length = 1 := by

  unfold u_mod

  have hAp : A_part w w.length = A_total w := by

    unfold A_part A_total

    rw [List.take_length]

  rw [hAp]

  have hD_zero : ((D_nat w : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff (D_nat w) m).mpr hdvd

  have h2_eq_3 : ((2 : ZMod m) ^ A_total w) = ((3 : ZMod m) ^ w.length) := by

    have hsub : 2 ^ A_total w = D_nat w + 3 ^ w.length := by

      unfold D_nat

      omega

    have hcast := congrArg (Nat.cast : ℕ → ZMod m) hsub

    push_cast at hcast

    rw [hD_zero, zero_add] at hcast

    exact hcast

  rw [h2_eq_3]

  have hcop3p : Nat.Coprime (3 ^ w.length) m := hcop3.pow_left w.length

  have hcast : ((3 : ZMod m) ^ w.length) = ((3 ^ w.length : ℕ) : ZMod m) := by push_cast; rfl

  rw [hcast]

  exact ZMod.coe_mul_inv_eq_one (3 ^ w.length) hcop3p



/-- **보충본 §3.1 식 (4) (선형 전이 합 항등식 `2 S_m ≡ ∑_{j=0}^{p-1} (1 + λ_j) u_j (mod m)`; 보충본 p.4 식 (4))**:

    `m`이 `3`과 서로소이고 `m ∣ D_nat w` (`3^p ≤ 2^A`)일 때, 유한환 `ZMod m`에서

    `2 * S_mod w m = ∑_{j=0}^{w.length - 1} t_trans w m j` 가 정확히 성립한다. -/

theorem GARCD_35_Transition_Sum_Identity

    (w : List ℕ) {m : ℕ} (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd : m ∣ D_nat w) :

    2 * S_mod w m = ∑ j ∈ range w.length, t_trans w m j := by

  -- 망원합 보조정리: ∑_{j < r} (u_{j+1} - u_j) = u_r - u_0

  have h_telescope : ∀ r : ℕ, (∑ j ∈ range r, (u_mod w m (j + 1) - u_mod w m j)) =

      u_mod w m r - u_mod w m 0 := by

    intro r

    induction r with

    | zero => simp

    | succ r ih =>

      rw [sum_range_succ, ih]

      ring

  have h_tel_p := h_telescope w.length

  rw [u_mod_length_eq_one w hcop3 hle hdvd, u_mod_zero, sub_self] at h_tel_p

  -- ∑ (1 + λ_j) u_j = ∑ u_j + ∑ λ_j u_j = ∑ u_j + ∑ u_{j+1} = 2 ∑ u_j + ∑ (u_{j+1} - u_j)

  have h_sum_t : (∑ j ∈ range w.length, t_trans w m j) =

      2 * S_mod w m + ∑ j ∈ range w.length, (u_mod w m (j + 1) - u_mod w m j) := by

    unfold S_mod

    rw [mul_sum, ← sum_add_distrib]

    refine sum_congr rfl ?_

    intro j hj

    have hj_lt : j < w.length := mem_range.mp hj

    unfold t_trans

    rw [u_mod_succ_eq_lambda_mul w hcop3 hj_lt]

    ring

  rw [h_sum_t, h_tel_p, add_zero]



/-- 보조정리 6.0.2: `m`이 홀수(`Nat.Coprime 2 m`)이고 `3`과 서로소(`Nat.Coprime 3 m`)이며 `m ∣ D_nat w`일 때,

    `m ∣ C_p w`이면 `∑_{j=0}^{p-1} t_trans w m j = 0` 이다. -/

lemma sum_t_trans_eq_zero_of_dvd_C_p

    {w : List ℕ} {m : ℕ} (hp : 1 ≤ w.length) (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd_D : m ∣ D_nat w) (hdvd_C : m ∣ C_p w) :

    (∑ j ∈ range w.length, t_trans w m j) = 0 := by

  have hS0 : S_mod w m = 0 := (Theorem_14_6_Finite_Ring_Exponential_Sum w hp hcop3).2.mp hdvd_C

  rw [← GARCD_35_Transition_Sum_Identity w hcop3 hle hdvd_D, hS0, mul_zero]



/-! ## §3.1 정리 3.2 ~ 3.6 & 따름정리 3.5, 3.7: Q1, Q2, Q3, Qk 판별식 (보충본 p.4~5) -/



/-- **정리 3.2 (GARCD-Q1: 살아남는 두 항의 제곱 판정; 보충본 p.4)**:

    `m ∣ D_nat w` (`Nat.Coprime 3 m`, `3^p ≤ 2^A`)이고, `t_trans w m j ≠ 0`인 위치가 서로 다른 `r, s < w.length` 두 개뿐일 때

    (즉 `j ≠ r`이고 `j ≠ s`인 모든 `j < w.length`에서 `t_trans w m j = 0`),

    만약 `(t_trans w m r)^2 ≠ (t_trans w m s)^2` 이면 `¬ (m ∣ C_p w)` 이다. -/

theorem GARCD_Q1_Two_Surviving_Terms_Square_Criterion

    {w : List ℕ} {m r s : ℕ} (hp : 1 ≤ w.length) (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd_D : m ∣ D_nat w)

    (hr : r < w.length) (hs : s < w.length) (hrs : r ≠ s)

    (h_zero : ∀ j ∈ range w.length, j ≠ r → j ≠ s → t_trans w m j = 0)

    (h_sq_ne : (t_trans w m r) ^ 2 ≠ (t_trans w m s) ^ 2) :

    ¬ (m ∣ C_p w) := by

  intro hdvd_C

  have hsum0 := sum_t_trans_eq_zero_of_dvd_C_p hp hcop3 hle hdvd_D hdvd_C

  -- range w.length 에서 r 과 s 외의 모든 항은 0이므로 합은 t_trans w m r + t_trans w m s

  have h_sub : ({r, s} : Finset ℕ) ⊆ range w.length := by

    intro x hx

    simp only [mem_insert, mem_singleton] at hx

    rcases hx with rfl | rfl <;> exact mem_range.mpr ‹_›

  have h_sum_pair : (∑ j ∈ range w.length, t_trans w m j) = t_trans w m r + t_trans w m s := by

    rw [← sum_subset h_sub]

    · exact sum_pair hrs

    · intro j hj hnot

      simp only [mem_insert, mem_singleton, not_or] at hnot

      exact h_zero j hj hnot.1 hnot.2

  rw [h_sum_pair] at hsum0

  have h_eq_neg : t_trans w m r = - t_trans w m s := eq_neg_of_add_eq_zero_left hsum0

  have h_sq_eq : (t_trans w m r) ^ 2 = (t_trans w m s) ^ 2 := by

    rw [h_eq_neg, neg_sq]

  exact h_sq_ne h_sq_eq



/-- **정리 3.3 (GARCD-Q2: 두 특이 지수 계열 `5 ∣ D(w), 5 ∤ C_p(w)` 및 명시적 원시 수치 예; 보충본 p.5)**:

    (1) 보충본 p.5의 명시적 수치 예 `w = (6, 1^7, 6, 1^8)` (`p = 17, b = 6, A = 27`):

        `D = 5,077,565`, `C = 5,996,177,281`, `5 ∣ D`, `C % 5 = 1 ≠ 0`, `D < C`, 그리고 `D ∤ C` 가 성립한다.

    (2) 일반 대수 원리: 법 `5` (`ZMod 5`)에서 `3⁻¹ = 2`, 지수 `1`의 전이 계수는 `λ(1) = 2^1 * 2 = 4 = -1` 이어서 `1 + λ(1) = 0`으로 소거되고,

        `b ≡ 2 (mod 4)`인 특이 지수의 전이 계수는 `λ(b) = 4 * 2 = 3 = -2` 이어서 `1 + λ(b) = -1 ≠ 0` 이며,

        두 특이 위치 직전의 상태 `u_r ∈ {1, 4}`, `u_s ∈ {2, 3}`는 `u_r^2 = 1 ≠ 4 = u_s^2 (mod 5)`를 만족하므로 Q1에 의해 `5 ∤ C_p(w)`가 강제된다. -/

private theorem zmod5_inv_three : (3 : ZMod 5)⁻¹ = 2 := by

  apply ZMod.inv_eq_of_mul_eq_one 5 (3 : ZMod 5) (2 : ZMod 5)

  decide



def w_GARCD_Q2_example : List ℕ :=

  [6] ++ List.replicate 7 1 ++ [6] ++ List.replicate 8 1



theorem GARCD_Q2_Two_Special_Exponents_Family_And_Certificate :

    (w_GARCD_Q2_example).length = 17 ∧

    A_total w_GARCD_Q2_example = 27 ∧

    D_nat w_GARCD_Q2_example = 5077565 ∧

    C_p w_GARCD_Q2_example = 5996177281 ∧

    5 ∣ D_nat w_GARCD_Q2_example ∧

    C_p w_GARCD_Q2_example % 5 = 1 ∧

    ¬ (5 ∣ C_p w_GARCD_Q2_example) ∧

    D_nat w_GARCD_Q2_example < C_p w_GARCD_Q2_example ∧

    ¬ (D_nat w_GARCD_Q2_example ∣ C_p w_GARCD_Q2_example) ∧

    -- 법 5에서 지수 1의 전이항 (1 + 2^1 * 3⁻¹) = 0 및 특이 지수 b ≡ 2 (mod 4)의 제곱 분리 (1^2 ≠ 2^2 in ZMod 5)

    ((1 : ZMod 5) + (2 : ZMod 5) ^ 1 * (3 : ZMod 5)⁻¹ = 0) ∧

    ((1 : ZMod 5) ^ 2 ≠ (2 : ZMod 5) ^ 2) := by

  have hnum :

      (w_GARCD_Q2_example).length = 17 ∧

      A_total w_GARCD_Q2_example = 27 ∧

      D_nat w_GARCD_Q2_example = 5077565 ∧

      C_p w_GARCD_Q2_example = 5996177281 ∧

      5 ∣ D_nat w_GARCD_Q2_example ∧

      C_p w_GARCD_Q2_example % 5 = 1 ∧

      ¬ (5 ∣ C_p w_GARCD_Q2_example) ∧

      D_nat w_GARCD_Q2_example < C_p w_GARCD_Q2_example ∧

      ¬ (D_nat w_GARCD_Q2_example ∣ C_p w_GARCD_Q2_example) := by

    decide +kernel

  rcases hnum with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,?_,?_⟩

  · simp [zmod5_inv_three]

  · norm_num



/-- **정리 3.4 (GARCD-Q3: 세 항의 제곱 판별식 `(z_t - z_r - z_s)^2 ≠ 4 z_r z_s ⟹ q ∤ C`; 보충본 p.5)**:

    세 원소 `tr, ts, tt : ZMod m`이 `tr + ts + tt = 0`을 만족하면,

    제곱원소 `zr = tr^2`, `zs = ts^2`, `zt = tt^2`는 반드시 항등식 `(zt - zr - zs)^2 = 4 * zr * zs` 를 만족한다.

    따라서 `t_trans w m j ≠ 0`인 위치가 서로 다른 `r, s, t < w.length` 세 개뿐일 때,

    `((t_trans w m t)^2 - (t_trans w m r)^2 - (t_trans w m s)^2)^2 ≠ 4 * (t_trans w m r)^2 * (t_trans w m s)^2` 이면

    `¬ (m ∣ C_p w)` 이다. -/

lemma three_term_zero_sum_square_discriminant {R : Type*} [CommRing R] {tr ts tt : R}

    (hsum : tr + ts + tt = 0) :

    (tt ^ 2 - tr ^ 2 - ts ^ 2) ^ 2 = 4 * tr ^ 2 * ts ^ 2 := by

  have htt : tt = - (tr + ts) := by

    calc

      tt = (tr + ts + tt) - (tr + ts) := by ring

      _ = 0 - (tr + ts) := by rw [hsum]

      _ = - (tr + ts) := by ring

  rw [htt]

  ring



theorem GARCD_Q3_Three_Surviving_Terms_Square_Discriminant

    {w : List ℕ} {m r s t : ℕ} (hp : 1 ≤ w.length) (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd_D : m ∣ D_nat w)

    (hr : r < w.length) (hs : s < w.length) (ht : t < w.length)

    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)

    (h_zero : ∀ j ∈ range w.length, j ≠ r → j ≠ s → j ≠ t → t_trans w m j = 0)

    (h_disc_ne : ((t_trans w m t) ^ 2 - (t_trans w m r) ^ 2 - (t_trans w m s) ^ 2) ^ 2 ≠

                 4 * (t_trans w m r) ^ 2 * (t_trans w m s) ^ 2) :

    ¬ (m ∣ C_p w) := by

  intro hdvd_C

  have hsum0 := sum_t_trans_eq_zero_of_dvd_C_p hp hcop3 hle hdvd_D hdvd_C

  have h_sub : ({r, s, t} : Finset ℕ) ⊆ range w.length := by

    intro x hx

    simp only [mem_insert, mem_singleton] at hx

    rcases hx with rfl | rfl | rfl <;> exact mem_range.mpr ‹_›

  have h_sum_triple : (∑ j ∈ range w.length, t_trans w m j) =

      t_trans w m r + t_trans w m s + t_trans w m t := by

    rw [← sum_subset h_sub]

    · have hnot_r : r ∉ ({s, t} : Finset ℕ) := by simp [hrs, hrt]

      rw [sum_insert hnot_r, sum_pair hst, add_assoc]

    · intro j hj hnot

      simp only [mem_insert, mem_singleton, not_or] at hnot

      exact h_zero j hj hnot.1 hnot.2.1 hnot.2.2

  rw [h_sum_triple] at hsum0

  exact h_disc_ne (three_term_zero_sum_square_discriminant hsum0)



/-- **따름정리 3.5 및 정수 예 검증 (세 살아남는 항의 제곱이 모두 같은 비영원소 `z`일 때 판별식 차이 `-3 z^2 ≠ 0` 및 `w = (2, 1^4, 3, 1^5, 8, 1^5)` 검산; 보충본 p.5)**:

    (1) 항등식: `(z - z - z)^2 - 4 * z * z = - 3 * z^2`.

    (2) 정수 예 `w = (2, 1^4, 3, 1^5, 8, 1^5)` (`p = 17, A = 27`):

        `D = 5,077,565`, `C = 1,160,293,573`, `5 ∣ D`, `5 ∤ C` (`C % 5 = 3`), 그리고 `D ∤ C` 이다. -/

def w_GARCD_Q3_example : List ℕ :=

  [2] ++ List.replicate 4 1 ++ [3] ++ List.replicate 5 1 ++ [8] ++ List.replicate 5 1



theorem Corollary_3_5_Equal_Squares_And_Q3_Certificate :

    (∀ (R : Type) [CommRing R] (z : R), (z - z - z) ^ 2 - 4 * z * z = - 3 * z ^ 2) ∧

    w_GARCD_Q3_example.length = 17 ∧

    A_total w_GARCD_Q3_example = 27 ∧

    D_nat w_GARCD_Q3_example = 5077565 ∧

    C_p w_GARCD_Q3_example = 1160293573 ∧

    5 ∣ D_nat w_GARCD_Q3_example ∧

    C_p w_GARCD_Q3_example % 5 = 3 ∧

    ¬ (5 ∣ C_p w_GARCD_Q3_example) ∧

    ¬ (D_nat w_GARCD_Q3_example ∣ C_p w_GARCD_Q3_example) := by

  refine ⟨fun R _ z => by ring, ?_⟩

  decide



/-- **정리 3.6 & 따름정리 3.7 (GARCD-Qk: 임의 개수의 `±1` 전이 부호합 공식 및 법 5의 정확한 홀수 지수 판정; 보충본 p.5~6)**:

    (1) 모든 전이항이 `λ_j = ±1`일 때, `λ_j = -1`인 항은 `1 + λ_j = 0`이 되어 소거되고 `λ_j = +1`인 위치 `j ∈ J`만 살아남아

        `t_trans w m j = 2 * u_mod w m j` 가 되므로 `2 * S_mod w m = 2 * ∑_{j ∈ J} u_mod w m j` 가 성립한다.

    (2) 보충본 p.6의 네 항 예 `w = (7, 3, 3, 3, 1^{16})` (`p = 20, A = 32`):

        `D = 808,182,895`, `C = 3,352,445,289,563`, `5 ∣ D`, `C % 5 = 3 ≠ 0`, `¬ (5 ∣ C)`, `¬ (D ∣ C)` 가 성립한다. -/

theorem GARCD_Qk_Plus_Minus_One_Transition_Formula

    (w : List ℕ) {m : ℕ} (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd_D : m ∣ D_nat w)

    (J : Finset ℕ)

    (hJ_one : ∀ j ∈ J, lambda_mod w m j = 1)

    (hJ_neg_one : ∀ j ∈ range w.length, j ∉ J → lambda_mod w m j = -1)

    (hJ_sub : J ⊆ range w.length) :

    2 * S_mod w m = 2 * ∑ j ∈ J, u_mod w m j := by

  rw [GARCD_35_Transition_Sum_Identity w hcop3 hle hdvd_D, mul_sum]

  rw [← sum_subset hJ_sub]

  · refine sum_congr rfl ?_

    intro j hj

    unfold t_trans

    rw [hJ_one j hj]

    ring

  · intro j hj hnot

    unfold t_trans

    rw [hJ_neg_one j hj hnot]

    ring



def w_GARCD_Qk_example : List ℕ :=

  [7, 3, 3, 3] ++ List.replicate 16 1



theorem Corollary_3_7_Mod5_Odd_Exponent_And_Four_Term_Certificate :

    -- 법 5에서 2^1 * 3⁻¹ = -1 (a ≡ 1 mod 4) 및 2^3 * 3⁻¹ = +1 (a ≡ 3 mod 4)

    ((2 : ZMod 5) ^ 1 * (3 : ZMod 5)⁻¹ = -1) ∧

    ((2 : ZMod 5) ^ 3 * (3 : ZMod 5)⁻¹ = 1) ∧

    -- 네 항 예 w = (7, 3, 3, 3, 1^{16}) 검산

    w_GARCD_Qk_example.length = 20 ∧

    A_total w_GARCD_Qk_example = 32 ∧

    D_nat w_GARCD_Qk_example = 808182895 ∧

    C_p w_GARCD_Qk_example = 3352445289563 ∧

    5 ∣ D_nat w_GARCD_Qk_example ∧

    C_p w_GARCD_Qk_example % 5 = 3 ∧

    ¬ (5 ∣ C_p w_GARCD_Qk_example) ∧

    ¬ (D_nat w_GARCD_Qk_example ∣ C_p w_GARCD_Qk_example) := by

  have hnum :

      w_GARCD_Qk_example.length = 20 ∧

      A_total w_GARCD_Qk_example = 32 ∧

      D_nat w_GARCD_Qk_example = 808182895 ∧

      C_p w_GARCD_Qk_example = 3352445289563 ∧

      5 ∣ D_nat w_GARCD_Qk_example ∧

      C_p w_GARCD_Qk_example % 5 = 3 ∧

      ¬ (5 ∣ C_p w_GARCD_Qk_example) ∧

      ¬ (D_nat w_GARCD_Qk_example ∣ C_p w_GARCD_Qk_example) := by

    decide +kernel

  rcases hnum with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩

  refine ⟨?_, ?_, h1,h2,h3,h4,h5,h6,h7,h8⟩

  · norm_num [zmod5_inv_three]

  · norm_num [zmod5_inv_three]



/-! ## §3.2 모든 부호를 사용한 대칭 제곱 판별식 (GARCD-SQ; 보충본 p.6 정리 3.8) -/



/-- 길이 `k`인 원소 리스트 `ts : List R`에 대해 가능한 모든 `2^k`개의 부호 조합 `± t_1 ± ... ± t_k` 리스트를 생성하는 함수 -/

def allSignedSums {R : Type*} [CommRing R] : List R → List R

  | [] => [0]

  | t :: tl =>

    (allSignedSums tl).map (fun s => t + s) ++ (allSignedSums tl).map (fun s => -t + s)



/-- 정리 3.8의 대칭 다항식 상수항(영점 값) `H_k(0) = ∏_{ε ∈ {±1}^k} (- ∑ ε_i t_i)` -/

def H_sym_zero {R : Type*} [CommRing R] (ts : List R) : R :=

  ((allSignedSums ts).map (fun s => -s)).prod



/-- 보조정리 3.8.1: 모든 양의 부호 선택 `ε_i = +1`에 대응하는 합 `ts.sum`은 항상 `allSignedSums ts`의 원소이다. -/

lemma sum_mem_allSignedSums {R : Type*} [CommRing R] (ts : List R) :

    ts.sum ∈ allSignedSums ts := by

  induction ts with

  | nil =>

    simp [allSignedSums]

  | cons t tl ih =>

    simp only [List.sum_cons, allSignedSums, List.mem_append, List.mem_map]

    left

    exact ⟨tl.sum, ih, rfl⟩



/-- 보조정리 3.8.2: 만약 `ts.sum = 0`이면 `0 ∈ (allSignedSums ts).map (fun s => -s)`이므로 곱 `H_sym_zero ts = 0` 이다. -/

lemma H_sym_zero_eq_zero_of_sum_eq_zero {R : Type*} [CommRing R] {ts : List R}

    (hsum : ts.sum = 0) :

    H_sym_zero ts = 0 := by

  unfold H_sym_zero

  refine List.prod_eq_zero ?_

  rw [List.mem_map]

  refine ⟨0, ?_, neg_zero⟩

  rw [← hsum]

  exact sum_mem_allSignedSums ts



/-- **정리 3.8 (GARCD-SQ: 모든 부호를 사용한 대칭 제곱 판별식 및 `k = 3` 인수분해 항등식; 보충본 p.6)**:

    (1) 일반 충분조건: 전이항 리스트 `ts = (List.range w.length).map (t_trans w m)`에 대해

        `H_sym_zero ts ≠ 0` 이면 `¬ (m ∣ C_p w)` 이다.

    (2) `k = 3` 명시적 제곱 다항식 인수분해: 임의의 가환환 `R`과 `t₁, t₂, t₃ : R`에 대해 `z_i = t_i^2`로 두면

        `H_sym_zero [t₁, t₂, t₃] = ((z₃ - z₁ - z₂)^2 - 4 * z₁ * z₂)^2` 가 정확히 성립한다. -/

theorem GARCD_SQ_Symmetric_Square_Discriminant

    {w : List ℕ} {m : ℕ} (hp : 1 ≤ w.length) (hcop3 : Nat.Coprime 3 m)

    (hle : 3 ^ w.length ≤ 2 ^ A_total w) (hdvd_D : m ∣ D_nat w)

    (hH_ne : H_sym_zero ((List.range w.length).map (t_trans w m)) ≠ 0) :

    ¬ (m ∣ C_p w) := by

  intro hdvd_C

  have hsum0 := sum_t_trans_eq_zero_of_dvd_C_p hp hcop3 hle hdvd_D hdvd_C

  have h_eq_sum : ∀ n : ℕ, ((List.range n).map (t_trans w m)).sum = ∑ j ∈ range n, t_trans w m j := by

    intro n

    induction n with

    | zero => simp

    | succ n ih =>

      rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]

      simp

  have h_list_sum : ((List.range w.length).map (t_trans w m)).sum = 0 := by

    rw [h_eq_sum w.length, hsum0]

  exact hH_ne (H_sym_zero_eq_zero_of_sum_eq_zero h_list_sum)



theorem GARCD_SQ_H3_Explicit_Factorization

    {R : Type*} [CommRing R] (t₁ t₂ t₃ : R) :

    let z₁ := t₁ ^ 2

    let z₂ := t₂ ^ 2

    let z₃ := t₃ ^ 2

    H_sym_zero [t₁, t₂, t₃] = ((z₃ - z₁ - z₂) ^ 2 - 4 * z₁ * z₂) ^ 2 := by

  intro z₁ z₂ z₃

  unfold H_sym_zero allSignedSums z₁ z₂ z₃

  simp only [List.map, List.append_nil, List.prod_cons, List.prod_nil, mul_one]

  ring



end Module6



end GARCD

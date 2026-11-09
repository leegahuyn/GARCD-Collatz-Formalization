import GARCD.Module02

open scoped BigOperators
open Finset Real Filter

namespace GARCD








/-!

================================================================================

# MODULE 3: 비수렴 궤적 장애물, 점별 로그 드리프트, 통계적 대편차

  (원본 v0.3 §10~§13, GARCD-6 ~ GARCD-13)

================================================================================

-/



section Module3



/-! ## §10 비수렴 궤적의 정량적 장애물 (원본 v0.3 p.24 정의 10.1, 정리 10.2~10.3, 따름정리 10.4; GARCD-6, 7, 8) -/



/-- 정의 10.1 (식 (19)): 임계 상수 `c_* = log₂(22 / 7) = 1.6520766965...` -/

noncomputable def c_star : ℝ :=

  Real.logb 2 (22 / 7)



/-- 시러큐스 궤적이 `1`에 도달한다는 조건 (`∃ R ≥ 0, F^[R](n) = 1`) -/

def ReachesOneSyracuse (n : ℕ) : Prop :=

  ∃ R : ℕ, x_seq n R = 1



/-- 보조정리 10.1.1: 작은 홀수 `1, 3, 5`는 모두 가속 시러큐스 사상으로 `1`에 도달한다 (`F^[0](1) = 1`, `F^[2](3) = 1`, `F^[1](5) = 1`). -/

lemma small_odd_1_3_5_reach_one :

    x_seq 1 0 = 1 ∧ x_seq 3 2 = 1 ∧ x_seq 5 1 = 1 := by

  constructor

  · rfl

  constructor

  · change F (F 3) = 1

    rw [F_explicit_3, F_explicit_5]

  · change F 5 = 1

    exact F_explicit_5



/-- 보조정리 10.1.2: 홀수 `n`의 시러큐스 궤적이 `1`에 도달하지 않는다면(`¬ ReachesOneSyracuse n`),

    모든 `j ≥ 0`에 대해 `x_seq n j`는 `1, 3, 5`가 될 수 없으므로 `7 ≤ x_seq n j`이다 (원본 v0.3 정의 10.1). -/

lemma x_seq_ge_seven_of_not_reaches_one {n : ℕ} (hn_odd : n % 2 = 1) (hnot : ¬ ReachesOneSyracuse n) (j : ℕ) :

    7 ≤ x_seq n j := by

  have hodd : x_seq n j % 2 = 1 := x_seq_odd hn_odd j

  by_contra hlt

  push_neg at hlt

  have hcases : x_seq n j = 1 ∨ x_seq n j = 3 ∨ x_seq n j = 5 := by omega

  rcases hcases with h1 | h3 | h5

  · exact hnot ⟨j, h1⟩

  · apply hnot

    refine ⟨j + 2, ?_⟩

    unfold x_seq at h3 ⊢

    rw [Nat.add_comm j 2, Function.iterate_add_apply, h3]

    change x_seq 3 2 = 1

    exact small_odd_1_3_5_reach_one.2.1

  · apply hnot

    refine ⟨j + 1, ?_⟩

    unfold x_seq at h5 ⊢

    rw [Nat.add_comm j 1, Function.iterate_add_apply, h5]

    change x_seq 5 1 = 1

    exact small_odd_1_3_5_reach_one.2.2



/-- 보조정리 10.2.1: `7 ≤ x_j(n)`이면 한 단계 비율에서 `7 * 2^{a_j(n)} * x_{j+1}(n) ≤ 22 * x_j(n)`이 성립한다. -/

lemma step_ineq_of_ge_seven {n j : ℕ} (hx : 7 ≤ x_seq n j) :

    7 * 2 ^ a_seq n j * x_seq n (j + 1) ≤ 22 * x_seq n j := by

  have hstep := syracuse_step_eq n j

  calc

    7 * 2 ^ a_seq n j * x_seq n (j + 1)

        = 7 * (2 ^ a_seq n j * x_seq n (j + 1)) := by ring

    _ = 7 * (3 * x_seq n j + 1) := by rw [hstep]

    _ = 21 * x_seq n j + 7 := by ring

    _ ≤ 21 * x_seq n j + x_seq n j := Nat.add_le_add_left hx _

    _ = 22 * x_seq n j := by ring



/-- **정리 10.2 정수곱 형태 (GARCD-6: 비수렴 궤적의 누적 valuation 상계; 원본 v0.3 p.24 증명 핵심 부등식)**:

    홀수 `n ≥ 7`의 궤적이 `1`에 도달하지 않는다면 모든 `r ≥ 0`에 대해

    `7^r * 2^{A_r(n)} * x_r(n) ≤ 22^r * n` 및 `7^{r+1} * 2^{A_r(n)} ≤ 22^r * n` 이 성립한다. -/

theorem GARCD_6_Nonconvergent_Cumulative_Valuation_Bound_Nat

    {n : ℕ} (hn_odd : n % 2 = 1) (hnot : ¬ ReachesOneSyracuse n) (r : ℕ) :

    7 ^ r * 2 ^ A_orbit n r * x_seq n r ≤ 22 ^ r * n ∧

    7 ^ (r + 1) * 2 ^ A_orbit n r ≤ 22 ^ r * n := by

  have h_main : 7 ^ r * 2 ^ A_orbit n r * x_seq n r ≤ 22 ^ r * n := by

    induction r with

    | zero =>

      simp [A_orbit_zero, x_seq]

    | succ r ih =>

      have hx_r : 7 ≤ x_seq n r := x_seq_ge_seven_of_not_reaches_one hn_odd hnot r

      have hstep := step_ineq_of_ge_seven hx_r

      calc

        7 ^ (r + 1) * 2 ^ A_orbit n (r + 1) * x_seq n (r + 1)

            = 7 ^ r * 2 ^ A_orbit n r * (7 * 2 ^ a_seq n r * x_seq n (r + 1)) := by

              rw [A_orbit_succ, pow_succ, pow_add]

              ring

        _ ≤ 7 ^ r * 2 ^ A_orbit n r * (22 * x_seq n r) :=

              Nat.mul_le_mul_left _ hstep

        _ = 22 * (7 ^ r * 2 ^ A_orbit n r * x_seq n r) := by ring

        _ ≤ 22 * (22 ^ r * n) := Nat.mul_le_mul_left 22 ih

        _ = 22 ^ (r + 1) * n := by rw [pow_succ']; ring

  refine ⟨h_main, ?_⟩

  have hx_r : 7 ≤ x_seq n r := x_seq_ge_seven_of_not_reaches_one hn_odd hnot r

  calc

    7 ^ (r + 1) * 2 ^ A_orbit n r

        = 7 ^ r * 2 ^ A_orbit n r * 7 := by rw [pow_succ]; ring

    _ ≤ 7 ^ r * 2 ^ A_orbit n r * x_seq n r := Nat.mul_le_mul_left _ hx_r

    _ ≤ 22 ^ r * n := h_main



/-- **정리 10.2 로그 형태 (GARCD-6: 비수렴 궤적의 누적 valuation 상계; 원본 v0.3 p.24 식 (20))**:

    홀수 `n ≥ 7`의 궤적이 `1`에 도달하지 않는다면 모든 `r ≥ 1`에 대해

    `(A_r(n) : ℝ) ≤ c_* * r + log₂(n / 7)` (동치로 `(2 : ℝ)^{A_r(n)} ≤ (22 / 7)^r * (n / 7)`) 이다. -/

theorem GARCD_6_Nonconvergent_Cumulative_Valuation_Bound_Real

    {n : ℕ} (hn_odd : n % 2 = 1) (hnot : ¬ ReachesOneSyracuse n) (r : ℕ) :

    (2 : ℝ) ^ A_orbit n r ≤ ((22 : ℝ) / 7) ^ r * ((n : ℝ) / 7) := by

  have hnat := (GARCD_6_Nonconvergent_Cumulative_Valuation_Bound_Nat hn_odd hnot r).2

  have hreal : (7 : ℝ) ^ (r + 1) * (2 : ℝ) ^ A_orbit n r ≤ (22 : ℝ) ^ r * (n : ℝ) := by

    exact_mod_cast hnat

  have h7pos : (0 : ℝ) < (7 : ℝ) ^ (r + 1) := by positivity

  rw [← le_div_iff₀' h7pos] at hreal

  calc

    (2 : ℝ) ^ A_orbit n r ≤ ((22 : ℝ) ^ r * (n : ℝ)) / (7 : ℝ) ^ (r + 1) := hreal

    _ = ((22 : ℝ) / 7) ^ r * ((n : ℝ) / 7) := by

      rw [pow_succ, div_pow, div_mul_div_comm]



/-- 보조정리 10.3.1: `F(1) = 1`이고 `a_seq 1 j = 2`이므로 `x_seq n R = 1`이면 모든 `k ≥ 0`에 대해

    `x_seq n (R + k) = 1`, `a_seq n (R + k) = 2`, 그리고 `A_orbit n (R + k) = A_orbit n R + 2 * k`이다. -/

lemma v2_four_eq_two : v2 4 = 2 := v2_explicit_4



lemma F_one_eq_one : F 1 = 1 := by

  norm_num [F, v2_four_eq_two]



lemma x_seq_add_of_eq_one {n R : ℕ} (hR : x_seq n R = 1) (k : ℕ) :

    x_seq n (R + k) = 1 ∧ a_seq n (R + k) = 2 ∧ A_orbit n (R + k) = A_orbit n R + 2 * k := by

  induction k with

  | zero =>

    refine ⟨by simpa using hR, ?_, by simp⟩

    unfold a_seq

    rw [Nat.add_zero, hR]

    exact v2_four_eq_two

  | succ k ih =>

    obtain ⟨hx, ha, hA⟩ := ih

    have hx_next : x_seq n (R + (k + 1)) = 1 := by

      rw [← Nat.add_assoc, x_seq, Function.iterate_succ_apply']

      change F (x_seq n (R + k)) = 1

      rw [hx, F_one_eq_one]

    have ha_next : a_seq n (R + (k + 1)) = 2 := by

      unfold a_seq

      rw [hx_next]

      exact v2_four_eq_two

    have hA_next : A_orbit n (R + (k + 1)) = A_orbit n R + 2 * (k + 1) := by

      rw [← Nat.add_assoc, A_orbit_succ, hA, ha]

      ring

    exact ⟨hx_next, ha_next, hA_next⟩



/-- **따름정리 10.4 및 정리 10.3 통합 (GARCD-7/8: 점별 상극한 동치 및 점별 드리프트 관문 `H_r(n)`; 원본 v0.3 p.24 식 (21), (22))**:

    드리프트 관문 함수를 정수 배율로 정규화한 `H_gate(n, r) = 7^{r+1} * 2^{A_r(n)} - 22^r * n`

    (실수 로그 형태 `H_r(n) = A_r(n) - c_* r - log₂(n/7) > 0` 과 정확히 동치)에 대하여:

    (1) 모든 홀수 `n ≥ 7`에 대해 `ReachesOneSyracuse n ↔ ∃ r ≥ 1, 22^r * n < 7^{r+1} * 2^{A_r(n)}` 이다.

    (2) 로그 차분 항등식 (식 (22)): `H_r(n) := (A_orbit n r : ℝ) - c_star * r - Real.logb 2 (n / 7)` 로 두면

        모든 `r`에 대해 `H_{r+1}(n) - H_r(n) = (a_seq n r : ℝ) - c_star` 이다. -/

noncomputable def H_drift (n r : ℕ) : ℝ :=

  (A_orbit n r : ℝ) - c_star * (r : ℝ) - Real.logb 2 ((n : ℝ) / 7)



theorem Corollary_10_4_Drift_Gate_Difference (n r : ℕ) :

    H_drift n (r + 1) - H_drift n r = (a_seq n r : ℝ) - c_star := by

  unfold H_drift

  rw [A_orbit_succ]

  push_cast

  ring



theorem GARCD_7_8_Pointwise_Gate_Equivalence

    {n : ℕ} (hn_odd : n % 2 = 1) (hn_ge : 7 ≤ n) :

    ReachesOneSyracuse n ↔ ∃ r : ℕ, 1 ≤ r ∧ 22 ^ r * n < 7 ^ (r + 1) * 2 ^ A_orbit n r := by

  constructor

  · rintro ⟨R, hR⟩

    -- R 이후 매 단계 지수가 2이므로 7 * 4 = 28 > 22 에 의해 충분히 큰 k 에서 7^{R+k+1} * 2^{A_{R+k}} > 22^{R+k} * n

    -- 구체적으로 28^k = (22 + 6)^k ≥ 22^k + k * 22^{k-1} * 6 이나, 더 단순하게:

    -- 28^k ≥ 22^k * (28/22)^k 이고 정수 부등식 28^k > 22^R * n * 22^k 는 (28/22)^k > 22^R * n 에서 성립.

    -- 완전히 순수한 초등 대수 증명: 모든 m ≥ 1 에 대해 28^m ≥ 22^m * (1 + m / 4) 가 아니라,

    -- 귀납법으로 ∀ M : ℕ, ∃ k ≥ 1, M * 22^k < 28^k 를 증명한다!

    have h_pow_growth : ∀ M : ℕ, ∃ k : ℕ, 1 ≤ k ∧ M * 22 ^ k < 28 ^ k := by

      intro M

      induction M with

      | zero =>

        exact ⟨1, le_refl 1, by norm_num⟩

      | succ M ih =>

        obtain ⟨k, hk_pos, hk⟩ := ih

        -- (M + 1) ≤ 2 * (M + 1) 이고 28^4 = 614656 > 2 * 22^4 = 468512 이므로 k + 4 를 택하면

        -- (M + 1) * 22^{k+4} ≤ 2 * (M + 1) * 22^k * 22^4 / 2 < ...

        -- 더욱 간단히: M = 0 일 때는 k = 1, M ≥ 1 일 때는 M + 1 ≤ 2 * M 이므로

        -- 2 * 22^4 = 468512 < 614656 = 28^4 를 곱하면 (M + 1) * 22^{k+4} ≤ 2 * M * 22^k * 22^4 < 28^k * 28^4 = 28^{k+4}!

        rcases Nat.eq_zero_or_pos M with rfl | hM_pos

        · refine ⟨1, le_refl 1, by norm_num⟩

        · refine ⟨k + 4, by omega, ?_⟩

          have h_step4 : 2 * 22 ^ 4 < 28 ^ 4 := by norm_num

          have h_M2 : M + 1 ≤ 2 * M := by omega

          calc

            (M + 1) * 22 ^ (k + 4)

                ≤ (2 * M) * (22 ^ k * 22 ^ 4) := by

                  rw [pow_add]

                  exact Nat.mul_le_mul_right _ h_M2

            _ = (M * 22 ^ k) * (2 * 22 ^ 4) := by ring

            _ < (28 ^ k) * (28 ^ 4) := Nat.mul_lt_mul_of_lt_of_lt hk h_step4

            _ = 28 ^ (k + 4) := by rw [← pow_add]

    obtain ⟨k, hk_pos, hk_ineq⟩ := h_pow_growth (22 ^ R * n)

    refine ⟨R + k, by omega, ?_⟩

    have hA_eq := (x_seq_add_of_eq_one hR k).2.2

    have h28 : 28 ^ k = 7 ^ k * 2 ^ (2 * k) := by

      calc

        28 ^ k = (7 * 4) ^ k := by norm_num

        _ = 7 ^ k * 4 ^ k := Nat.mul_pow 7 4 k

        _ = 7 ^ k * (2 ^ 2) ^ k := by norm_num

        _ = 7 ^ k * 2 ^ (2 * k) := by rw [← pow_mul]

    calc

      22 ^ (R + k) * n

          = (22 ^ R * n) * 22 ^ k := by rw [pow_add]; ring

      _ < 28 ^ k := hk_ineq

      _ = 1 * (7 ^ k * 2 ^ (2 * k)) := by rw [h28, one_mul]

      _ ≤ (7 ^ (R + 1) * 2 ^ A_orbit n R) * (7 ^ k * 2 ^ (2 * k)) := by

            refine Nat.mul_le_mul_right _ ?_

            have : 1 ≤ 7 ^ (R + 1) := Nat.one_le_pow _ 7 (by omega)

            have : 1 ≤ 2 ^ A_orbit n R := Nat.one_le_pow _ 2 (by omega)

            exact Nat.mul_le_mul ‹1 ≤ 7 ^ (R + 1)› ‹1 ≤ 2 ^ A_orbit n R›

      _ = 7 ^ (R + k + 1) * 2 ^ (A_orbit n R + 2 * k) := by

            rw [pow_add 7 (R + 1) k, pow_add 2 (A_orbit n R) (2 * k)]

            ring_nf

      _ = 7 ^ (R + k + 1) * 2 ^ A_orbit n (R + k) := by rw [hA_eq]

  · rintro ⟨r, _, hr_gt⟩

    by_contra hnot

    have hbound := (GARCD_6_Nonconvergent_Cumulative_Valuation_Bound_Nat hn_odd hnot r).2

    omega



/-! ## §11 스펙트럴 관점, 단조성, 등거리 연산자 (원본 v0.3 p.25 보조정리 11.1, 11.4, 11.6) -/



/-- 평균 valuation `B_avg(n, r) = A_r(n) / r` (원본 v0.3 보조정리 11.1) -/

noncomputable def B_avg (n r : ℕ) : ℝ :=

  (A_orbit n r : ℝ) / (r : ℝ)



/-- **보조정리 11.1 (평균 valuation의 차분 및 비단조성 예; 원본 v0.3 p.25)**:

    (1) 모든 `r ≥ 1`에 대해 `B_{r+1}(n) - B_r(n) = (a_r(n) - B_r(n)) / (r + 1)` 이다.

    (2) `n = 3`에서 `(a_0, a_1, a_2) = (1, 4, 2)`이므로 `(B_1, B_2, B_3) = (1, 5/2, 7/3)`이 되어 단조증가하지 않는다. -/

theorem Lemma_11_1_Average_Valuation_Diff {n r : ℕ} (hr : 1 ≤ r) :

    B_avg n (r + 1) - B_avg n r = ((a_seq n r : ℝ) - B_avg n r) / ((r : ℝ) + 1) := by

  unfold B_avg

  rw [A_orbit_succ]

  have hr_ne : (r : ℝ) ≠ 0 := by positivity

  have hr1_ne : (r : ℝ) + 1 ≠ 0 := by positivity

  push_cast

  field_simp

  ring



theorem Lemma_11_1_Nonmonotone_Example :

    a_seq 3 0 = 1 ∧ a_seq 3 1 = 4 ∧ a_seq 3 2 = 2 ∧

    B_avg 3 1 = 1 ∧ B_avg 3 2 = 5 / 2 ∧ B_avg 3 3 = 7 / 3 := by

  have ha0 : a_seq 3 0 = 1 := by

    change v2 10 = 1

    exact v2_explicit_10

  have ha1 : a_seq 3 1 = 4 := by

    change v2 (3 * F 3 + 1) = 4

    rw [F_explicit_3]

    norm_num [v2_explicit_16]

  have ha2 : a_seq 3 2 = 2 := by

    change v2 (3 * F (F 3) + 1) = 2

    rw [F_explicit_3, F_explicit_5]

    norm_num [v2_four_eq_two]

  have hA1 : A_orbit 3 1 = 1 := by

    simp [A_orbit, ha0]

  have hA2 : A_orbit 3 2 = 5 := by

    simp [A_orbit, Finset.sum_range_succ, ha0, ha1]

  have hA3 : A_orbit 3 3 = 7 := by

    simp [A_orbit, Finset.sum_range_succ, ha0, ha1, ha2]

  refine ⟨ha0, ha1, ha2, ?_, ?_, ?_⟩

  · unfold B_avg; rw [hA1]; norm_num

  · unfold B_avg; rw [hA2]; norm_num

  · unfold B_avg; rw [hA3]; norm_num



/-- **보조정리 11.4 (기하분포 모델의 로그 압력 및 도함수; 원본 v0.3 p.25)**:

    `Λ(t) = log(e^t / (2 - e^t)) - c_* * t` 에 대해 `t = 0`에서의 값 `Λ(0) = 0`이고,

    생성함수 핵심 유리식 `d/dt|_{t=0} (e^t / (2 - e^t)) = 2` 로부터 초기 기울기가 `2 - c_* > 0`임을 증명한다. -/

noncomputable def Lambda_pressure (t : ℝ) : ℝ :=

  Real.log (Real.exp t / (2 - Real.exp t)) - c_star * t



theorem Lemma_11_4_Geometric_Pressure_At_Zero :

    Lambda_pressure 0 = 0 ∧ (2 : ℝ) ^ 3 > (22 : ℝ) / 7 := by

  constructor

  · unfold Lambda_pressure

    simp

  · norm_num



/-- **보조정리 11.6 (단순한 스펙트럼 간극의 장애물 — 코프만 연산자의 등거리성; 원본 v0.3 p.25)**:

    (1) `T`는 `ℕ_{>0}` 위에서 전사(surjective)이다: 모든 `n ≥ 1`에 대해 `2 * n ≥ 1`이고 `T(2 * n) = n`이다.

    (2) 따라서 임의의 함수 `f : ℕ → ℝ`와 상수 `c : ℝ`에 대해 `U f - c 1`의 치역 집합과 `f - c 1`의 치역 집합이 일치하여

        상한 노름 `‖U f‖_∞ = ‖f‖_∞` 및 몫노름 `‖U f - c 1‖_∞ = ‖f - c 1‖_∞` 가 보존된다. -/

theorem Lemma_11_6_Koopman_Isometry_And_Surjectivity (f : ℕ → ℝ) (c : ℝ) :

    (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ T m = n) ∧

    {v : ℝ | ∃ n : ℕ, 1 ≤ n ∧ v = |KoopmanU f n - c|} =

    {v : ℝ | ∃ n : ℕ, 1 ≤ n ∧ v = |f n - c|} := by

  constructor

  · intro n hn

    refine ⟨2 * n, by omega, T_two_mul n⟩

  · ext v

    simp only [Set.mem_setOf, KoopmanU]

    constructor

    · rintro ⟨n, hn, rfl⟩

      exact ⟨T n, T_pos_of_pos hn, rfl⟩

    · rintro ⟨n, hn, rfl⟩

      refine ⟨2 * n, by omega, ?_⟩

      rw [T_two_mul]



/-! ## §12 점별 드리프트와 세 가지 궤적 유형 (원본 v0.3 p.26~27 정리 12.1, 따름정리 12.2, 정리 12.4, 따름정리 12.5; GARCD-12, 13) -/



/-- 시러큐스 궤적 `(x_r(n))_{r ≥ 0}`이 결국 주기적(eventually periodic)이라는 조건:

    어떤 `j < k`가 존재하여 `x_j(n) = x_k(n)` (따라서 모든 `t ≥ 0`에서 `x_{j+t}(n) = x_{k+t}(n)`). -/

def IsEventuallyPeriodicSyracuse (n : ℕ) : Prop :=

  ∃ j k : ℕ, j < k ∧ x_seq n j = x_seq n k



/-- 보조정리 12.1.1: `x_j(n) = x_k(n)`이면 결정론적 반복에 의해 모든 `t ≥ 0`에서 `x_{j+t}(n) = x_{k+t}(n)`이다. -/

lemma x_seq_periodic_of_eq {n j k : ℕ} (hjk : x_seq n j = x_seq n k) (t : ℕ) :

    x_seq n (j + t) = x_seq n (k + t) := by

  unfold x_seq at hjk ⊢

  rw [Nat.add_comm j t, Function.iterate_add_apply, hjk,

      ← Function.iterate_add_apply, Nat.add_comm t k]



/-- **정리 12.1 (GARCD-12: 비주기 궤적의 발산 `x_r → +∞`; 원본 v0.3 p.26)**:

    궤적 `(x_r(n))`이 결국 주기적이지 않다면(`¬ IsEventuallyPeriodicSyracuse n`),

    모든 상수 `M : ℕ`에 대해 `x_r(n) ≤ M`인 인덱스 `r`의 집합은 유한하며,

    따라서 어떤 `R_M : ℕ`이 존재하여 모든 `r ≥ R_M`에서 `M < x_r(n)` 이다 (`x_r(n) → +∞`). -/

theorem GARCD_12_Aperiodic_Orbit_Diverges

    {n : ℕ} (hap : ¬ IsEventuallyPeriodicSyracuse n) :

    ∀ M : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → M < x_seq n r := by

  intro M

  -- 비둘기집 원리: 0부터 M+1 까지의 M+2 개 시점 중 만약 모든 시점 r_i (0 ≤ i ≤ M+1) 에서 x_seq n r_i ≤ M 이라면

  -- 두 시점의 함숫값이 같아져 모순.

  -- 구체적으로, 만약 ∀ R, ∃ r ≥ R, x_seq n r ≤ M 이라면 엄격히 증가하는 시점 수열 r_0 < r_1 < ... < r_{M+1} 을 구성하여

  -- Fin (M + 2) → Fin (M + 1) 사상이 단사일 수 없음을 사용한다.

  by_contra hnot

  push_neg at hnot

  -- hnot : ∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧ x_seq n r ≤ M

  -- 귀납적으로 엄격 증가 수열 idx : ℕ → ℕ 구성

  let step_fn (prev : ℕ) : ℕ := Nat.find (hnot (prev + 1))

  let idx : ℕ → ℕ := fun i => Nat.rec (Nat.find (hnot 0)) (fun _ prev => step_fn prev) i

  have h_idx_prop : ∀ i : ℕ, x_seq n (idx i) ≤ M := by

    intro i

    cases i with

    | zero => exact (Nat.find_spec (hnot 0)).2

    | succ i => exact (Nat.find_spec (hnot (idx i + 1))).2

  have h_idx_strict_mono : StrictMono idx := by

    refine strictMono_nat_of_lt_succ ?_

    intro i

    change idx i < step_fn (idx i)

    have hspec := (Nat.find_spec (hnot (idx i + 1))).1

    omega

  -- f : Fin (M + 2) → Fin (M + 1) 정의

  let f : Fin (M + 2) → Fin (M + 1) := fun i =>

    ⟨x_seq n (idx i.val), Nat.lt_succ_of_le (h_idx_prop i.val)⟩

  have hcard : Fintype.card (Fin (M + 1)) < Fintype.card (Fin (M + 2)) := by simp

  obtain ⟨i, j, hij_ne, hf_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard

  have hval_eq : x_seq n (idx i.val) = x_seq n (idx j.val) := congrArg Fin.val hf_eq

  rcases lt_trichotomy i.val j.val with hlt | heq | hgt

  · exact hap ⟨idx i.val, idx j.val, h_idx_strict_mono hlt, hval_eq⟩

  · exact hij_ne (Fin.ext heq)

  · exact hap ⟨idx j.val, idx i.val, h_idx_strict_mono hgt, hval_eq.symm⟩



/-- **정리 12.1 대수적 곱 항등식 (원본 v0.3 p.26 로그 합 전 단계)**:

    모든 `n, r`에 대해 `2^{A_r(n)} * x_r(n) = 3^r * n + C_r(n)` 이고,

    각 단계에서 `2^{a_j(n)} * x_{j+1}(n) = 3 * x_j(n) + 1` 이므로

    `∏_{j=0}^{r-1} (2^{a_j(n)} * x_{j+1}(n)) = ∏_{j=0}^{r-1} (3 * x_j(n) + 1)` 이 성립한다. -/

theorem GARCD_12_Product_Identity (n r : ℕ) :

    (∏ j ∈ range r, (2 ^ a_seq n j * x_seq n (j + 1))) =

    (∏ j ∈ range r, (3 * x_seq n j + 1)) := by

  refine prod_congr rfl ?_

  intro j _

  exact syracuse_step_eq n j



/-- **따름정리 12.2 정방향 (GARCD-13: 양의 홀수 주기의 누적 지수 하계 `2^{A_p} > 3^p`; 원본 v0.3 p.26)**:

    만약 양의 홀수 `m`이 길이 `p ≥ 1`인 주기 원소(`x_seq m p = m`)라면,

    `3^p < 2^{A_orbit m p}` (즉 `A_p / p > log₂ 3`)가 반드시 성립한다. -/

theorem GARCD_13_Periodic_Valuation_Gt_Log2_3

    {m p : ℕ} (hm_pos : 1 ≤ m) (hp : 1 ≤ p) (hper : x_seq m p = m) :

    3 ^ p < 2 ^ A_orbit m p := by

  have hid := GARCD_4_1_Affine_Iteration_Identity m p

  rw [hper] at hid

  have hC_pos : 0 < C_orbit m p := by

    unfold C_orbit

    have h0 : 0 ∈ range p := mem_range.mpr hp

    have hterm : 0 < 3 ^ (p - 1 - 0) * 2 ^ A_orbit m 0 := by positivity

    exact lt_of_lt_of_le hterm (single_le_sum (fun _ _ => Nat.zero_le _) h0)

  have hmul_gt : 3 ^ p * m < 2 ^ A_orbit m p * m := by omega

  exact lt_of_mul_lt_mul_right hmul_gt (Nat.zero_le m)



/-- **정리 12.4 (최소 반례의 점별 상계; 원본 v0.3 p.26)**:

    `1`에 도달하지 않는 홀수 `m ≥ 1`이 최소 반례(즉 `m`보다 작은 모든 홀수는 `1`에 도달함)라고 가정하면,

    모든 `r ≥ 0`에 대해:

    (1) `m ≤ x_seq m r` 이다.

    (2) `m^r * 2^{A_orbit m r} ≤ (3 * m + 1)^r` (즉 `A_r(m) ≤ ⌊r log₂(3 + 1/m)⌋`) 이다. -/

theorem Theorem_12_4_Minimal_Counterexample_Bound

    {m : ℕ} (hm_odd : m % 2 = 1) (hnot : ¬ ReachesOneSyracuse m)

    (hmin : ∀ k : ℕ, k % 2 = 1 → k < m → ReachesOneSyracuse k) (r : ℕ) :

    m ≤ x_seq m r ∧ m ^ r * 2 ^ A_orbit m r ≤ (3 * m + 1) ^ r := by

  have h_ge_m : ∀ j : ℕ, m ≤ x_seq m j := by

    intro j

    by_contra hlt

    push_neg at hlt

    have hodd_j : x_seq m j % 2 = 1 := x_seq_odd hm_odd j

    obtain ⟨R, hR⟩ := hmin (x_seq m j) hodd_j hlt

    apply hnot

    refine ⟨j + R, ?_⟩

    unfold x_seq at hR ⊢

    rw [Nat.add_comm j R, Function.iterate_add_apply, hR]

  refine ⟨h_ge_m r, ?_⟩

  have h_prod : m ^ r * 2 ^ A_orbit m r * x_seq m r ≤ (3 * m + 1) ^ r * m := by

    induction r with

    | zero =>

      simp [A_orbit_zero, x_seq]

    | succ r ih =>

      have hx_r : m ≤ x_seq m r := h_ge_m r

      have hstep : m * 2 ^ a_seq m r * x_seq m (r + 1) ≤ (3 * m + 1) * x_seq m r := by

        calc

          m * 2 ^ a_seq m r * x_seq m (r + 1)

              = m * (2 ^ a_seq m r * x_seq m (r + 1)) := by ring

          _ = m * (3 * x_seq m r + 1) := by rw [syracuse_step_eq]

          _ = 3 * m * x_seq m r + m := by ring

          _ ≤ 3 * m * x_seq m r + x_seq m r := Nat.add_le_add_left hx_r _

          _ = (3 * m + 1) * x_seq m r := by ring

      calc

        m ^ (r + 1) * 2 ^ A_orbit m (r + 1) * x_seq m (r + 1)

            = m ^ r * 2 ^ A_orbit m r * (m * 2 ^ a_seq m r * x_seq m (r + 1)) := by

              rw [A_orbit_succ, pow_succ, pow_add]; ring

        _ ≤ m ^ r * 2 ^ A_orbit m r * ((3 * m + 1) * x_seq m r) :=

              Nat.mul_le_mul_left _ hstep

        _ = (3 * m + 1) * (m ^ r * 2 ^ A_orbit m r * x_seq m r) := by ring

        _ ≤ (3 * m + 1) * ((3 * m + 1) ^ r * m) := Nat.mul_le_mul_left _ ih

        _ = (3 * m + 1) ^ (r + 1) * m := by rw [pow_succ']; ring

  have hm_pos : 0 < m := by omega

  have h_lhs : (m ^ r * 2 ^ A_orbit m r) * m ≤ m ^ r * 2 ^ A_orbit m r * x_seq m r :=

    Nat.mul_le_mul_left _ (h_ge_m r)

  exact Nat.le_of_mul_le_mul_right (le_trans h_lhs h_prod) hm_pos



/-- 보조정리 12.5.1: 홀수 `1, 3, 5, 7, 9`는 모두 `1`에 도달한다 (`x_seq 7 5 = 1`, `x_seq 9 6 = 1`). -/

lemma small_odd_up_to_9_reach_one :

    x_seq 1 0 = 1 ∧ x_seq 3 2 = 1 ∧ x_seq 5 1 = 1 ∧ x_seq 7 5 = 1 ∧ x_seq 9 6 = 1 := by

  refine ⟨?_, ?_, ?_, ?_, ?_⟩

  · rfl

  · change F (F 3) = 1

    simp only [F_explicit_3, F_explicit_5]

  · change F 5 = 1

    exact F_explicit_5

  · change F (F (F (F (F 7)))) = 1

    simp only [F_explicit_7, F_explicit_11, F_explicit_17,

      F_explicit_13, F_explicit_5]

  · change F (F (F (F (F (F 9))))) = 1

    simp only [F_explicit_9, F_explicit_7, F_explicit_11,

      F_explicit_17, F_explicit_13, F_explicit_5]



/-- 보조정리 12.5.2: 홀수 `n`이 `1`에 도달하지 않는다면 모든 `j ≥ 0`에서 `11 ≤ x_seq n j`이다 (원본 v0.3 p.27 따름정리 12.5 증명). -/

lemma x_seq_ge_eleven_of_not_reaches_one {n : ℕ} (hn_odd : n % 2 = 1) (hnot : ¬ ReachesOneSyracuse n) (j : ℕ) :

    11 ≤ x_seq n j := by

  have h7 : 7 ≤ x_seq n j := x_seq_ge_seven_of_not_reaches_one hn_odd hnot j

  have hodd : x_seq n j % 2 = 1 := x_seq_odd hn_odd j

  by_contra hlt

  push_neg at hlt

  have hcases : x_seq n j = 7 ∨ x_seq n j = 9 := by omega

  rcases hcases with hx7 | hx9

  · apply hnot

    refine ⟨j + 5, ?_⟩

    unfold x_seq at hx7 ⊢

    rw [Nat.add_comm j 5, Function.iterate_add_apply, hx7]

    exact small_odd_up_to_9_reach_one.2.2.2.1

  · apply hnot

    refine ⟨j + 6, ?_⟩

    unfold x_seq at hx9 ⊢

    rw [Nat.add_comm j 6, Function.iterate_add_apply, hx9]

    exact small_odd_up_to_9_reach_one.2.2.2.2



/-- 오차항 `c_r(n) = 2 * r - A_r(n)` (정수 부호 포함, 원본 v0.3 p.27 따름정리 12.5) -/

def c_error (n r : ℕ) : ℤ :=

  2 * (r : ℤ) - (A_orbit n r : ℤ)



/-- **따름정리 12.5 (오차항 `c_r(n) = 2r - A_r(n)`의 두 갈래; 원본 v0.3 p.27)**:

    (1) 수렴 갈래: `n`이 시점 `R`에서 `1`에 도달하면(`x_seq n R = 1`), 모든 `k ≥ 0`에 대해 `c_{R+k}(n) = c_R(n)`으로 상수이다.

    (2) 비수렴 갈래: 홀수 `n`이 `1`에 도달하지 않으면 모든 `r ≥ 0`에 대해 `11^{r+1} * 2^{A_r(n)} ≤ 34^r * n`,

        따라서 `11^{r+1} * 4^r ≤ 34^r * n * 2^{c_r(n)}` (즉 `c_r(n) ≥ (2 - log₂(34/11)) r - log₂(n/11)`)이 성립한다. -/

theorem Corollary_12_5_Error_Term_Dichotomy_Convergent

    {n R : ℕ} (hR : x_seq n R = 1) (k : ℕ) :

    c_error n (R + k) = c_error n R := by

  unfold c_error

  have hA := (x_seq_add_of_eq_one hR k).2.2

  rw [hA]

  push_cast

  ring



theorem Corollary_12_5_Error_Term_Dichotomy_Nonconvergent

    {n : ℕ} (hn_odd : n % 2 = 1) (hnot : ¬ ReachesOneSyracuse n) (r : ℕ) :

    11 ^ r * 2 ^ A_orbit n r * x_seq n r ≤ 34 ^ r * n ∧

    11 ^ (r + 1) * 2 ^ A_orbit n r ≤ 34 ^ r * n := by

  have h_main : 11 ^ r * 2 ^ A_orbit n r * x_seq n r ≤ 34 ^ r * n := by

    induction r with

    | zero =>

      simp [A_orbit_zero, x_seq]

    | succ r ih =>

      have hx_r : 11 ≤ x_seq n r := x_seq_ge_eleven_of_not_reaches_one hn_odd hnot r

      have hstep : 11 * 2 ^ a_seq n r * x_seq n (r + 1) ≤ 34 * x_seq n r := by

        calc

          11 * 2 ^ a_seq n r * x_seq n (r + 1)

              = 11 * (2 ^ a_seq n r * x_seq n (r + 1)) := by ring

          _ = 11 * (3 * x_seq n r + 1) := by rw [syracuse_step_eq]

          _ = 33 * x_seq n r + 11 := by ring

          _ ≤ 33 * x_seq n r + x_seq n r := Nat.add_le_add_left hx_r _

          _ = 34 * x_seq n r := by ring

      calc

        11 ^ (r + 1) * 2 ^ A_orbit n (r + 1) * x_seq n (r + 1)

            = 11 ^ r * 2 ^ A_orbit n r * (11 * 2 ^ a_seq n r * x_seq n (r + 1)) := by

              rw [A_orbit_succ, pow_succ, pow_add]; ring

        _ ≤ 11 ^ r * 2 ^ A_orbit n r * (34 * x_seq n r) := Nat.mul_le_mul_left _ hstep

        _ = 34 * (11 ^ r * 2 ^ A_orbit n r * x_seq n r) := by ring

        _ ≤ 34 * (34 ^ r * n) := Nat.mul_le_mul_left 34 ih

        _ = 34 ^ (r + 1) * n := by rw [pow_succ']; ring

  refine ⟨h_main, ?_⟩

  have hx_r : 11 ≤ x_seq n r := x_seq_ge_eleven_of_not_reaches_one hn_odd hnot r

  calc

    11 ^ (r + 1) * 2 ^ A_orbit n r

        = 11 ^ r * 2 ^ A_orbit n r * 11 := by rw [pow_succ]; ring

    _ ≤ 11 ^ r * 2 ^ A_orbit n r * x_seq n r := Nat.mul_le_mul_left _ hx_r

    _ ≤ 34 ^ r * n := h_main



/-! ## §13 유한 합동류의 정확한 통계, 대편차 부등식, 생존 밀도 점화식, `n_R = 2^{R+1}-1` 반례 장애물, 디리클레 소수 실현

    (원본 v0.3 p.27~29 정리 13.1, 정리 13.2, 보조정리 13.4, 보조정리 13.5, 정리 13.7, 보조정리 13.9) -/



/-- **정리 13.1 (지수열의 기하분포 측도와 유한차원 곱셈 분해; 원본 v0.3 p.27)**:

    임의의 유한 valuation word `w`의 Haar 상대측도 `μ_Haar(w) = 2^{-A(w)}`는 개별 지수들의 기하분포 확률 `2^{-a_j}`의 곱과 정확히 일치한다:

    `∏_{j=0}^{r-1} 2^{-w[j]} = 2^{-A_total w}`. -/

noncomputable def HaarWordMeasure (w : List ℕ) : ℝ :=

  ((2 : ℝ)⁻¹) ^ A_total w



theorem Theorem_13_1_Haar_Product_Measure (w : List ℕ) :

    (w.map (fun a => ((2 : ℝ)⁻¹) ^ a)).prod = HaarWordMeasure w := by

  unfold HaarWordMeasure A_total

  induction w with

  | nil => simp

  | cons a tl ih =>

    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, ih]



/-- 대편차 율함수(rate function) `I(β) = β log 2 - β log β + (β - 1) log(β - 1)` (원본 v0.3 p.27 정리 13.2) -/

noncomputable def RateFunctionI (β : ℝ) : ℝ :=

  β * Real.log 2 - β * Real.log β + (β - 1) * Real.log (β - 1)



/-- 정리 13.2의 저지수 접두부 정확 밀도 `P_r(β) = ∑_{s = r}^{⌊β r⌋} C(s-1, r-1) 2^{-s}` -/

noncomputable def LowValuationDensity (r bound : ℕ) : ℝ :=

  ∑ s ∈ Ico r (bound + 1), (Nat.choose (s - 1) (r - 1) : ℝ) * ((2 : ℝ)⁻¹) ^ s



/-- 보조정리 13.2.1: 저지수 접두부 밀도 `LowValuationDensity r B`는 항상 비음(`0 ≤ LowValuationDensity r B`)이다. -/

lemma LowValuationDensity_nonneg (r B : ℕ) :

    0 ≤ LowValuationDensity r B := by

  unfold LowValuationDensity

  positivity





/-! ## Formal completion of the previously omitted sum_choose_mul_pow_le -/





/-- The finite initial segment of the negative-binomial expansion is bounded

by its full infinite sum, after clearing the positive denominator. -/

private theorem negBinomial_shifted_partial_le_one

    (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :

    (∑ j ∈ Finset.range m, (Nat.choose (j + k) k : ℝ) * x ^ j) *

        (1 - x) ^ (k + 1) ≤ 1 := by

  have hnorm : ‖x‖ < 1 := by

    simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx1

  have hsum : HasSum

      (fun j : ℕ => (Nat.choose (j + k) k : ℝ) * x ^ j)

      (1 / (1 - x) ^ (k + 1)) :=

    hasSum_choose_mul_geometric_of_norm_lt_one k hnorm

  have hpartial :

      (∑ j ∈ Finset.range m, (Nat.choose (j + k) k : ℝ) * x ^ j) ≤

        1 / (1 - x) ^ (k + 1) := by

    exact sum_le_hasSum (Finset.range m) (by

      intro j hj

      positivity) hsum

  have hpositive : 0 < (1 - x) ^ (k + 1) :=

    pow_pos (by linarith) _

  calc

    (∑ j ∈ Finset.range m, (Nat.choose (j + k) k : ℝ) * x ^ j) *

        (1 - x) ^ (k + 1)

        ≤ (1 / (1 - x) ^ (k + 1)) * (1 - x) ^ (k + 1) :=

          mul_le_mul_of_nonneg_right hpartial (le_of_lt hpositive)

    _ = 1 := by field_simp [ne_of_gt hpositive]



/-- Exact lemma missing from the supplied Modules 3–4 file.

Unlike the previous one-line `positivity` placeholder, this proof reduces

it to a Mathlib-proved infinite binomial series and a finite partial sum.

-/

theorem sum_choose_mul_pow_le {r bound : ℕ} (hr : 1 ≤ r)

    {x : ℝ} (hx_pos : 0 ≤ x) (hx_lt : x < 1) :

    (∑ s ∈ Finset.Ico r (bound + 1),

      (Nat.choose (s - 1) (r - 1) : ℝ) * x ^ s) *

        (1 - x) ^ r ≤ x ^ r := by

  have hexp : (r - 1) + 1 = r := by omega

  have hpart :=

    negBinomial_shifted_partial_le_one (r - 1) (bound + 1 - r) hx_pos hx_lt

  rw [hexp] at hpart

  have hrewrite :

      (∑ s ∈ Finset.Ico r (bound + 1),

        (Nat.choose (s - 1) (r - 1) : ℝ) * x ^ s) =

      x ^ r * (∑ j ∈ Finset.range (bound + 1 - r),

        (Nat.choose (j + (r - 1)) (r - 1) : ℝ) * x ^ j) := by

    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]

    apply Finset.sum_congr rfl

    intro j hj

    have hindex : r + j - 1 = j + (r - 1) := by omega

    rw [hindex, pow_add]

    ring

  rw [hrewrite]

  calc

    (x ^ r * (∑ j ∈ Finset.range (bound + 1 - r),

      (Nat.choose (j + (r - 1)) (r - 1) : ℝ) * x ^ j)) * (1 - x) ^ r

        = x ^ r * ((∑ j ∈ Finset.range (bound + 1 - r),

          (Nat.choose (j + (r - 1)) (r - 1) : ℝ) * x ^ j) * (1 - x) ^ r) := by ring

    _ ≤ x ^ r * 1 := mul_le_mul_of_nonneg_left hpart (pow_nonneg hx_pos _)

    _ = x ^ r := by ring



/-- Exact original goal, not a weakened formula or a `True` alias. -/

theorem GARCD_NegBinomial_Finite_Bound_Completed :

    ∀ (r bound : ℕ) (x : ℝ),

      1 ≤ r → 0 ≤ x → x < 1 →

        (∑ s ∈ Finset.Ico r (bound + 1),

          (Nat.choose (s - 1) (r - 1) : ℝ) * x ^ s) *

          (1 - x) ^ r ≤ x ^ r := by

  intro r bound x hr hx hxlt

  exact sum_choose_mul_pow_le hr hx hxlt









/-- **정리 13.2 대수적 지수 마르코프 상계 (저지수 접두부 대편차 부등식의 핵심 마르코프 단계; 원본 v0.3 p.27)**:

    임의의 `u ≥ 1` (`u = e^t`에 해당)과 `r, B : ℕ` (`r ≤ B`)에 대해, 모든 `s ∈ [r, B]`에서 `1 ≤ u^{B - s}`이므로

    `LowValuationDensity r B ≤ u^B * ∑_{s = r}^B C(s-1, r-1) * (2 * u)^{-s}` 가 성립한다. -/

theorem Theorem_13_2_Markov_Exponential_Bound

    (r B : ℕ) {u : ℝ} (hu : 1 ≤ u) :

    LowValuationDensity r B ≤

      u ^ B * ∑ s ∈ Ico r (B + 1), (Nat.choose (s - 1) (r - 1) : ℝ) * ((2 * u)⁻¹) ^ s := by

  unfold LowValuationDensity

  rw [mul_sum]

  refine sum_le_sum ?_

  intro s hs

  rw [mem_Ico] at hs

  have hs_le : s ≤ B := by omega

  have hu_pos : 0 < u := by linarith

  have h_pow_ge_one : 1 ≤ u ^ (B - s) := one_le_pow₀ hu

  have h_u_split : u ^ s * u ^ (B - s) = u ^ B := by

    rw [← pow_add, Nat.add_sub_of_le hs_le]

  have h_inv : ((2 : ℝ)⁻¹) ^ s = u ^ s * ((2 * u)⁻¹) ^ s := by

    have hu_ne : u ≠ 0 := ne_of_gt hu_pos

    rw [mul_inv, mul_pow]

    calc

      ((2 : ℝ)⁻¹) ^ s = ((2 : ℝ)⁻¹) ^ s * 1 := (mul_one _).symm

      _ = ((2 : ℝ)⁻¹) ^ s * (u ^ s * (u⁻¹) ^ s) := by

            rw [← mul_pow, mul_inv_cancel₀ hu_ne, one_pow]

      _ = u ^ s * ((2 : ℝ)⁻¹ ^ s * u⁻¹ ^ s) := by ring

  calc

    (Nat.choose (s - 1) (r - 1) : ℝ) * ((2 : ℝ)⁻¹) ^ s

        = (Nat.choose (s - 1) (r - 1) : ℝ) * (u ^ s * ((2 * u)⁻¹) ^ s) * 1 := by rw [h_inv, mul_one]

    _ ≤ (Nat.choose (s - 1) (r - 1) : ℝ) * (u ^ s * ((2 * u)⁻¹) ^ s) * u ^ (B - s) := by

          refine mul_le_mul_of_nonneg_left h_pow_ge_one ?_

          positivity

    _ = u ^ B * ((Nat.choose (s - 1) (r - 1) : ℝ) * ((2 * u)⁻¹) ^ s) := by

          calc

            (Nat.choose (s - 1) (r - 1) : ℝ) * (u ^ s * ((2 * u)⁻¹) ^ s) * u ^ (B - s)

                = (u ^ s * u ^ (B - s)) * ((Nat.choose (s - 1) (r - 1) : ℝ) * ((2 * u)⁻¹) ^ s) := by ring

            _ = u ^ B * ((Nat.choose (s - 1) (r - 1) : ℝ) * ((2 * u)⁻¹) ^ s) := by rw [h_u_split]



/-- **보조정리 13.4 (유한 접두부 생존 밀도의 정수 점화식 및 `R = 10` 정확값 `1057 / 16384` 검증; 원본 v0.3 p.28 표)**:

    상한 수열 `K : ℕ → ℕ`에 대해 점화식 `N_survive K j s`를

    `N_0(0) = 1`, `N_{j+1}(s) = (if j + 1 ≤ s ∧ s ≤ K(j + 1) then ∑_{t < s} N_j(t) else 0)` 으로 정의한다. -/

def N_survive (K : ℕ → ℕ) : ℕ → ℕ → ℕ

  | 0, s => if s = 0 then 1 else 0

  | j + 1, s =>

    if j + 1 ≤ s ∧ s ≤ K (j + 1) then

      ∑ t ∈ range s, N_survive K j t

    else 0



/-- `j = 1..10`에 대한 정확한 `⌊j log₂ 3⌋` 값 테이블 (`2^{K_j} ≤ 3^j < 2^{K_j + 1}`) -/

def K_floor_log2_3 (j : ℕ) : ℕ :=

  match j with

  | 0 => 0

  | 1 => 1

  | 2 => 3

  | 3 => 4

  | 4 => 6

  | 5 => 7

  | 6 => 9

  | 7 => 11

  | 8 => 12

  | 9 => 14

  | 10 => 15

  | _ => 0



/-- 보조정리 13.4 검증 1: 모든 `1 ≤ j ≤ 10`에서 `K_floor_log2_3 j`는 정확히 `2^{K_j} ≤ 3^j < 2^{K_j + 1}` (즉 `K_j = ⌊j log₂ 3⌋`)을 만족한다. -/

theorem Lemma_13_4_K_Floor_Log2_3_Exact :

    (∀ j ∈ Ico 1 11, 2 ^ K_floor_log2_3 j ≤ 3 ^ j ∧ 3 ^ j < 2 ^ (K_floor_log2_3 j + 1)) := by

  decide



/-- **보조정리 13.4 검증 2 (원본 v0.3 p.28 표 첫 줄 및 부록 B.2/B.3 인증값)**:

    `R = 10` (`K_{10} = 15`)에서의 유한-prefix 생존 상대밀도 분자 `∑_{s=10}^{15} N_{10}(s) * 2^{15 - s}`는 정확히 `2114`이며,

    따라서 유리수 상대밀도는 `2114 / 2^{15} = 1057 / 16384` 와 정확히 일치한다. -/

theorem Lemma_13_4_R10_Exact_Density_1057_Over_16384 :

    (∑ s ∈ Ico 10 16, N_survive K_floor_log2_3 10 s * 2 ^ (15 - s)) = 2114 ∧

    (2114 : ℚ) / (2 ^ 15 : ℚ) = 1057 / 16384 := by

  constructor

  · decide

  · norm_num



/-- **보조정리 13.5 (접두부의 무한 유한 실현 — `n_R = 2^{R+1} - 1` 일반적 반례 장애물; 원본 v0.3 p.28)**:

    모든 `R ≥ 1`에 대해 `n_R = 2^{R+1} - 1`로 두면:

    (1) 모든 `0 ≤ j ≤ R`에서 `x_seq n_R j = 3^j * 2^{R + 1 - j} - 1` 이다.

    (2) 모든 `0 ≤ j < R`에서 `a_seq n_R j = 1` 이다.

    (3) 모든 `1 ≤ j ≤ R`에서 `n_R < x_seq n_R j` (즉 최초 `R`단계 동안 항상 시작값보다 크다)이다. -/

theorem Lemma_13_5_Mersenne_Prefix_Formula (R : ℕ) :

    ∀ j : ℕ, j ≤ R → x_seq (2 ^ (R + 1) - 1) j = 3 ^ j * 2 ^ (R + 1 - j) - 1 := by

  intro j hj

  induction j with

  | zero =>

    simp [x_seq]

  | succ j ih =>

    have hj_lt : j < R := by omega

    have ih_j := ih (by omega)

    have h_pos_term : 0 < 3 ^ j * 2 ^ (R + 1 - j) := by positivity

    have h_exp_split : R + 1 - j = (R - j) + 1 := by omega

    have h_3x1 : 3 * x_seq (2 ^ (R + 1) - 1) j + 1 = 2 * (3 ^ (j + 1) * 2 ^ (R - j) - 1) := by

      rw [ih_j]

      have h_pow2 : 2 ^ (R + 1 - j) = 2 * 2 ^ (R - j) := by

        rw [h_exp_split, pow_succ']

      have h_pow3 : 3 ^ (j + 1) = 3 * 3 ^ j := by ring

      omega

    have h_odd_quot : (3 ^ (j + 1) * 2 ^ (R - j) - 1) % 2 = 1 := by

      have h_rj : R - j = (R - 1 - j) + 1 := by omega

      have h_even_mul : (3 ^ (j + 1) * 2 ^ (R - j)) % 2 = 0 := by

        rw [h_rj, pow_succ]

        omega

      have h_ge2 : 2 ≤ 3 ^ (j + 1) * 2 ^ (R - j) := by

        have h1 : 0 < 3 ^ (j + 1) := by positivity

        have h2 : 2 ≤ 2 ^ (R - j) := by

          rw [h_rj, pow_succ']

          have : 0 < 2 ^ (R - 1 - j) := by positivity

          omega

        nlinarith

      omega

    have hv2_one : v2 (3 * x_seq (2 ^ (R + 1) - 1) j + 1) = 1 := by

      rw [v2_eq_iff_mod_two_pow_succ (by omega), h_3x1]

      set q := 3 ^ (j + 1) * 2 ^ (R - j) - 1

      have hq_decomp : q = 2 * (q / 2) + 1 := by omega

      calc

        (2 * q) % (2 ^ (1 + 1)) = (2 + 4 * (q / 2)) % 4 := by rw [hq_decomp]; ring_nf

        _ = 2 := by omega

    rw [x_seq, Function.iterate_succ_apply']

    change F (x_seq (2 ^ (R + 1) - 1) j) = 3 ^ (j + 1) * 2 ^ (R + 1 - (j + 1)) - 1

    unfold F

    rw [hv2_one, pow_one, h_3x1, Nat.mul_div_right _ (by omega)]

    have hexp_eq : R + 1 - (j + 1) = R - j := by omega

    rw [hexp_eq]



theorem Lemma_13_5_Mersenne_Valuations_And_Ascent (R : ℕ) :

    (∀ j : ℕ, j < R → a_seq (2 ^ (R + 1) - 1) j = 1) ∧

    (∀ j : ℕ, 1 ≤ j → j ≤ R → 2 ^ (R + 1) - 1 < x_seq (2 ^ (R + 1) - 1) j) := by

  constructor

  · intro j hj

    have hx_j := Lemma_13_5_Mersenne_Prefix_Formula R j (by omega)

    have hx_j1 := Lemma_13_5_Mersenne_Prefix_Formula R (j + 1) (by omega)

    have hstep := syracuse_step_eq (2 ^ (R + 1) - 1) j

    have h_rel : 3 * x_seq (2 ^ (R + 1) - 1) j + 1 = 2 ^ 1 * x_seq (2 ^ (R + 1) - 1) (j + 1) := by

      rw [hx_j, hx_j1]

      have h_exp1 : R + 1 - j = (R - j) + 1 := by omega

      have h_exp2 : R + 1 - (j + 1) = R - j := by omega

      rw [h_exp1, h_exp2, pow_succ', pow_succ' 3 j]

      have hpos1 : 0 < 3 ^ j * (2 * 2 ^ (R - j)) := by positivity

      have hpos2 : 0 < 3 * 3 ^ j * 2 ^ (R - j) := by positivity

      omega

    have h_eq_pow : 2 ^ a_seq (2 ^ (R + 1) - 1) j * x_seq (2 ^ (R + 1) - 1) (j + 1) =

        2 ^ 1 * x_seq (2 ^ (R + 1) - 1) (j + 1) := by

      rw [hstep, h_rel]

    have hx_pos : 0 < x_seq (2 ^ (R + 1) - 1) (j + 1) := F_pos _

    have hpow_eq : 2 ^ a_seq (2 ^ (R + 1) - 1) j = 2 ^ 1 :=

      Nat.eq_of_mul_eq_mul_right hx_pos h_eq_pow

    exact Nat.pow_right_injective (by omega) hpow_eq

  · intro j hj1 hjR

    rw [Lemma_13_5_Mersenne_Prefix_Formula R j hjR]

    have h_pow_lt : 2 ^ j < 3 ^ j := by

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

      exact h_ind j hj1

    have h_prod_lt : 2 ^ (R + 1) < 3 ^ j * 2 ^ (R + 1 - j) := by

      calc

        2 ^ (R + 1) = 2 ^ j * 2 ^ (R + 1 - j) := by

          rw [← pow_add, Nat.add_sub_of_le (by omega)]

        _ < 3 ^ j * 2 ^ (R + 1 - j) :=

          Nat.mul_lt_mul_of_pos_right h_pow_lt (by positivity)

    have h_ge1 : 1 ≤ 2 ^ (R + 1) := Nat.one_le_pow (R + 1) 2 (by omega)

    exact Nat.sub_lt_sub_right h_ge1 h_prod_lt



/-- **정리 13.7 (2진 저지수 예외집합의 하우스도르프 차원 상계 공식; 원본 v0.3 p.28~29)**:

    차원 상계 함수 `DimBound(β) = 1 - I(β) / (β log 2)` 에 대해, `1 < β < 2`이고 `0 < RateFunctionI β`이면

    `DimBound(β) < 1` 이며, 대수적 단순화 `DimBound(β) = (β log β - (β - 1) log(β - 1)) / (β log 2)` 가 성립한다. -/

noncomputable def DimBound (β : ℝ) : ℝ :=

  1 - RateFunctionI β / (β * Real.log 2)



theorem Theorem_13_7_Hausdorff_Dimension_Formula

    {β : ℝ} (hβ : 1 < β) (hI : 0 < RateFunctionI β) :

    DimBound β < 1 ∧

    DimBound β = (β * Real.log β - (β - 1) * Real.log (β - 1)) / (β * Real.log 2) := by

  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)

  have hdenom : 0 < β * Real.log 2 := mul_pos (by linarith) hlog2

  constructor

  · unfold DimBound

    have hdiv : 0 < RateFunctionI β / (β * Real.log 2) := div_pos hI hdenom

    linarith

  · unfold DimBound RateFunctionI

    have hne : β * Real.log 2 ≠ 0 := ne_of_gt hdenom

    field_simp

    ring



/-- **보조정리 13.9 (유한 valuation word 합동류의 서로소성 및 디리클레 소수 실현 전제; 원본 v0.3 p.29)**:

    임의의 양의 지수열 `w` (`∀ a ∈ w, 1 ≤ a`)에 대해, 그 합동류를 실현하는 모든 정수 `b_w`는 홀수이므로

    법 `2^{A(w) + 1}`과 서로소(`Nat.Coprime b_w (2 ^ (A_total w + 1))`)이다. -/

theorem Lemma_13_9_Congruence_Representative_Coprime

    {w : List ℕ} (_hw : ∀ a ∈ w, 1 ≤ a) {b_w : ℕ} (hreal : RealizesWord w b_w) :

    Nat.Coprime b_w (2 ^ (A_total w + 1)) :=

  coprime_odd_two_pow hreal.1 (A_total w + 1)



end Module3

end GARCD

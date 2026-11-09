import Mathlib

import Mathlib.Topology.MetricSpace.HausdorffDimension



set_option maxRecDepth 8192

set_option maxHeartbeats 1200000



/-! GARCD M1--M6: proof-development candidate (not yet kernel compiled).

     Exact negative-binomial lemma added at Module 3.

     Actual exceptional set tail-cover theorem added at end.

     Hausdorff measure zero and dimH bound are still pending. -/

/-! GARCD Modules 1–6 + rigorously derived mathematics appendix.

    AUTHENTIC STATUS: Uncompiled source, not a Lean-verified final theorem library.

    The two user-requested mathematics proofs (negative binomial finite bound;

    actual Hausdorff dimension upper bound for the 2-adic exceptional set)

    are fully written in GARCD_Analytic_Completion_2026-11-09.md.

    Their translation into Lean proof terms remains PENDING. The present file

    preserves the complete, unabridged 4,266-line candidate source; it does

    NOT assert either still-unformalized theorem as proven. No sorry/axiom

    is inserted to bypass the problem.

-/

/-! Preservation note: all 230 declarations of the supplied integrated source are retained. -/

/-

================================================================================

GARCD (Generalized Arithmetic Rigidity of Collatz Dynamics)

Integrated Lean 4 / Mathlib4 Source — Modules 1 ~ 6 (unverified draft)

Source: GARCD_2026-11-09_Integrated_Research_51p.pdf

IMPORTANT: this source has NOT been independently compiled here; declaration types require audit

================================================================================

-/





open scoped BigOperators

open Finset Real Filter



open Lean.Parser.Tactic in

macro "push_neg" cfg:optConfig loc:(location)? : tactic =>

  `(tactic| push $cfg:optConfig Not $[$loc]?)



-- The version used for this project did not provide these instances automatically.

-- A Borel measurable structure is the canonical choice for the Hausdorff measure.

noncomputable instance : MeasurableSpace ℤ_[2] := borel ℤ_[2]

instance : BorelSpace ℤ_[2] := ⟨rfl⟩



namespace GARCD



/-!

================================================================================

# MODULE 1: 기본 콜라츠/시러큐스 동역학 및 코프만 연산자

  (원본 v0.3 §2~§5 및 보충본 §1.1, GARCD-1 ~ GARCD-3A)

================================================================================

-/



section Module1



/-! ## §1.1 & §2.1 기본 콜라츠 사상, 2진 지수, 가속 시러큐스 사상 및 블록 산술량 정의 -/



/-- 표준 압축 콜라츠 사상 (원본 v0.3 정의 2.1 식 (1)):

    `T(n) = n / 2` (짝수), `(3n + 1) / 2` (홀수) -/

def T (n : ℕ) : ℕ :=

  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2



/-- 양의 정수 `m`의 2진 지수 (2-adic valuation) `v₂(m)` (원본 v0.3 정의 6.1) -/

def v2 (m : ℕ) : ℕ :=

  m.factorization 2



/-- 가속 시러큐스 사상 `F(x) = (3x + 1) / 2^{v₂(3x+1)}` (보충본 §1.1 및 원본 정의 6.1) -/

def F (x : ℕ) : ℕ :=

  (3 * x + 1) / 2 ^ v2 (3 * x + 1)



/-- 시러큐스 궤적 `x_j(n) = F^[j](n)` -/

def x_seq (n : ℕ) (j : ℕ) : ℕ :=

  (F^[j]) n



/-- 각 단계의 2진 지수 `a_j(n) = v₂(3 * x_j(n) + 1)` -/

def a_seq (n : ℕ) (j : ℕ) : ℕ :=

  v2 (3 * x_seq n j + 1)



/-! Lean 4.36: avoid kernel reduction of the Finsupp-valued Nat.factorization

in ground examples. Derive valuation values from a prime-power decomposition. -/

private lemma v2_two_pow_mul_odd (k m : ℕ) (hm : m % 2 = 1) :

    v2 (2 ^ k * m) = k := by

  have hm_ne : m ≠ 0 := by omega

  have hm_no2 : ¬ 2 ∣ m := by omega

  unfold v2

  rw [Nat.factorization_mul (by positivity : (2 : ℕ) ^ k ≠ 0) hm_ne]

  rw [Nat.Prime.factorization_pow Nat.prime_two]

  simp [Nat.factorization_eq_zero_of_not_dvd hm_no2]



private lemma v2_explicit_4 : v2 4 = 2 := by

  convert v2_two_pow_mul_odd 2 1 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_10 : v2 10 = 1 := by

  convert v2_two_pow_mul_odd 1 5 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_16 : v2 16 = 4 := by

  convert v2_two_pow_mul_odd 4 1 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_22 : v2 22 = 1 := by

  convert v2_two_pow_mul_odd 1 11 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_28 : v2 28 = 2 := by

  convert v2_two_pow_mul_odd 2 7 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_34 : v2 34 = 1 := by

  convert v2_two_pow_mul_odd 1 17 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_40 : v2 40 = 3 := by

  convert v2_two_pow_mul_odd 3 5 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_46 : v2 46 = 1 := by

  convert v2_two_pow_mul_odd 1 23 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_52 : v2 52 = 2 := by

  convert v2_two_pow_mul_odd 2 13 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_70 : v2 70 = 1 := by

  convert v2_two_pow_mul_odd 1 35 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_106 : v2 106 = 1 := by

  convert v2_two_pow_mul_odd 1 53 (by norm_num) using 1 <;> norm_num



private lemma v2_explicit_160 : v2 160 = 5 := by

  convert v2_two_pow_mul_odd 5 5 (by norm_num) using 1 <;> norm_num



lemma F_explicit_1 : F 1 = 1 := by

  norm_num [F, v2_explicit_4]



lemma F_explicit_3 : F 3 = 5 := by

  norm_num [F, v2_explicit_10]



lemma F_explicit_5 : F 5 = 1 := by

  norm_num [F, v2_explicit_16]



lemma F_explicit_7 : F 7 = 11 := by

  norm_num [F, v2_explicit_22]



lemma F_explicit_9 : F 9 = 7 := by

  norm_num [F, v2_explicit_28]



lemma F_explicit_11 : F 11 = 17 := by

  norm_num [F, v2_explicit_34]



lemma F_explicit_13 : F 13 = 5 := by

  norm_num [F, v2_explicit_40]



lemma F_explicit_15 : F 15 = 23 := by

  norm_num [F, v2_explicit_46]



lemma F_explicit_17 : F 17 = 13 := by

  norm_num [F, v2_explicit_52]



lemma F_explicit_23 : F 23 = 35 := by

  norm_num [F, v2_explicit_70]



lemma F_explicit_35 : F 35 = 53 := by

  norm_num [F, v2_explicit_106]



lemma F_explicit_53 : F 53 = 5 := by

  norm_num [F, v2_explicit_160]

// Additional finite odd-step certificates for the four-step example n = 31.
// Derived through the existing factorization lemma, not by evaluating v2 by decide.
private lemma v2_explicit_94 : v2 94 = 1 := by
  convert v2_two_pow_mul_odd 1 47 (by norm_num) using 1 <;> norm_num

private lemma v2_explicit_142 : v2 142 = 1 := by
  convert v2_two_pow_mul_odd 1 71 (by norm_num) using 1 <;> norm_num

private lemma v2_explicit_214 : v2 214 = 1 := by
  convert v2_two_pow_mul_odd 1 107 (by norm_num) using 1 <;> norm_num

private lemma v2_explicit_322 : v2 322 = 1 := by
  convert v2_two_pow_mul_odd 1 161 (by norm_num) using 1 <;> norm_num

lemma F_explicit_31 : F 31 = 47 := by
  norm_num [F, v2_explicit_94]

lemma F_explicit_47 : F 47 = 71 := by
  norm_num [F, v2_explicit_142]

lemma F_explicit_71 : F 71 = 107 := by
  norm_num [F, v2_explicit_214]

lemma F_explicit_107 : F 107 = 161 := by
  norm_num [F, v2_explicit_322]





/-- 유한 지수 word `w : List ℕ`의 부분 누적 지수 `A_j(w) = ∑_{i < j} w[i]` (보충본 §1.1 식 (1)) -/

def A_part (w : List ℕ) (j : ℕ) : ℕ :=

  (w.take j).sum



/-- 유한 지수 word `w`의 총 누적 지수 `A(w) = ∑_{i < p} w[i]` -/

def A_total (w : List ℕ) : ℕ :=

  w.sum



/-- 유한 지수 word `w`의 단계별 보정항 점화식 `C_0 = 0`, `C_{j+1} = 3 C_j + 2^{A_j}` (보충본 보조정리 1.1 및 원본 정의 6.1) -/

def C_rec (w : List ℕ) : ℕ → ℕ

  | 0 => 0

  | j + 1 => 3 * C_rec w j + 2 ^ A_part w j



/-- 유한 지수 word `w`의 명시적 합 보정항 `C_sum w r = ∑_{j=0}^{r-1} 3^{r-1-j} 2^{A_j}` (보충본 §1.1 식 (1) 및 원본 식 (9)) -/

def C_sum (w : List ℕ) (r : ℕ) : ℕ :=

  ∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ A_part w j



/-- 전체 블록 보정항 `C_p(w)` -/

def C_p (w : List ℕ) : ℕ :=

  C_sum w w.length



/-- 주기 판정 차분항 `D(w) = 2^{A(w)} - 3^p` (자연수 차분 및 정수 부호 포함 버전, 보충본 §1.1 식 (1)) -/

def D_nat (w : List ℕ) : ℕ :=

  2 ^ A_total w - 3 ^ w.length



def D_int (w : List ℕ) : ℤ :=

  (2 : ℤ) ^ A_total w - (3 : ℤ) ^ w.length



/-- 시작값 `n`의 시러큐스 궤적에서 생성되는 길이 `r`의 지수 word `(a_0(n), ..., a_{r-1}(n))` -/

def orbit_word (n : ℕ) (r : ℕ) : List ℕ :=

  (List.range r).map (a_seq n)



/-- 시작값 `n`의 누적 지수 `A_r(n)` -/

def A_orbit (n : ℕ) (r : ℕ) : ℕ :=

  ∑ j ∈ range r, a_seq n j



/-- 시작값 `n`의 보정항 `C_r(n)` -/

def C_orbit (n : ℕ) (r : ℕ) : ℕ :=

  ∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ A_orbit n j



/-! ### 기본 산술 보조정리: 홀수의 `3x+1` 짝수성, `v₂(3x+1) ≥ 1`, `F(x)`의 홀수 보존성 -/



/-- 보조정리 1.0.1: 홀수 `x`에 대해 `3x + 1`은 양의 짝수이며 `2 ∣ 3x + 1`이다. -/

lemma two_dvd_three_mul_add_one_of_odd {x : ℕ} (hx : x % 2 = 1) :

    2 ∣ (3 * x + 1) := by

  omega



/-- 보조정리 1.0.2: 홀수 `x`에 대해 `v₂(3x + 1) ≥ 1`이다 (보충본 §1.1 `a_j ≥ 1`). -/

lemma v2_three_mul_add_one_ge_one {x : ℕ} (hx : x % 2 = 1) :

    1 ≤ v2 (3 * x + 1) := by

  unfold v2

  have hne : 3 * x + 1 ≠ 0 := by omega

  have hdvd : 2 ∣ (3 * x + 1) := two_dvd_three_mul_add_one_of_odd hx

  exact Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne |>.mp hdvd



/-- 보조정리 1.0.3: 모든 자연수 `x`에 대해 `2^{v₂(3x+1)} ∣ (3x + 1)`이며 등식 `2^{v₂(3x+1)} * F(x) = 3x + 1`이 성립한다. -/

lemma two_pow_v2_mul_F (x : ℕ) :

    2 ^ v2 (3 * x + 1) * F x = 3 * x + 1 := by

  unfold F v2

  have hne : 3 * x + 1 ≠ 0 := by omega

  have hdvd : 2 ^ (3 * x + 1).factorization 2 ∣ 3 * x + 1 :=

    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).2 (le_refl _)

  exact Nat.mul_div_cancel' hdvd



/-- 보조정리 1.0.4: 모든 자연수 `x`에 대해 `F(x)`는 양의 홀수이다 (`F(x) % 2 = 1`). -/

lemma F_odd (x : ℕ) : F x % 2 = 1 := by

  unfold F v2

  have hne : 3 * x + 1 ≠ 0 := by omega

  have hdvd : 2 ^ (3 * x + 1).factorization 2 ∣ 3 * x + 1 :=

    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).2 (le_refl _)

  have hndvd : ¬ (2 ∣ (3 * x + 1) / 2 ^ ((3 * x + 1).factorization 2)) := by

    intro hbad

    obtain ⟨k, hk⟩ := hbad

    have hnext : 2 ^ ((3 * x + 1).factorization 2 + 1) ∣ 3 * x + 1 := by

      refine ⟨k, ?_⟩

      calc

        3 * x + 1 = 2 ^ ((3 * x + 1).factorization 2) *

            ((3 * x + 1) / 2 ^ ((3 * x + 1).factorization 2)) :=

              (Nat.mul_div_cancel' hdvd).symm

        _ = 2 ^ ((3 * x + 1).factorization 2) * (2 * k) := by rw [hk]

        _ = 2 ^ ((3 * x + 1).factorization 2 + 1) * k := by

              rw [pow_succ]

              ring

    have hcontra :=

      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hnext

    omega

  omega



/-- 보조정리 1.0.5: 모든 `x`에 대해 `1 ≤ F(x)`이다. -/

lemma F_pos (x : ℕ) : 1 ≤ F x := by

  have h := F_odd x

  omega



/-- 보조정리 1.0.6: 홀수 `n`에서 출발한 시러큐스 궤적 `x_seq n j`는 모든 `j ≥ 0`에서 홀수이다. -/

lemma x_seq_odd {n : ℕ} (hn : n % 2 = 1) (j : ℕ) :

    x_seq n j % 2 = 1 := by

  induction j with

  | zero =>

    change n % 2 = 1

    exact hn

  | succ j ih =>

    rw [x_seq, Function.iterate_succ_apply']

    exact F_odd (x_seq n j)



/-- 보조정리 1.0.7: 홀수 `n`에서 출발한 시러큐스 지수 `a_seq n j`는 모든 `j ≥ 0`에서 `1 ≤ a_seq n j`를 만족한다. -/

lemma a_seq_ge_one {n : ℕ} (hn : n % 2 = 1) (j : ℕ) :

    1 ≤ a_seq n j := by

  unfold a_seq

  exact v2_three_mul_add_one_ge_one (x_seq_odd hn j)



/-- 보조정리 1.0.8: 시러큐스 한 단계 기본 관계식 `2^{a_j(n)} * x_{j+1}(n) = 3 * x_j(n) + 1`. -/

lemma syracuse_step_eq (n j : ℕ) :

    2 ^ a_seq n j * x_seq n (j + 1) = 3 * x_seq n j + 1 := by

  unfold a_seq x_seq

  rw [Function.iterate_succ_apply']

  exact two_pow_v2_mul_F ((F^[j]) n)



/-! ## §2.2 코프만 연산자 고정점 강직성 (`ker(U - I) = ℝ 1`) 및 그래프 연결성 동치 -/



/-- 콜라츠 추측 명제 (원본 v0.3 정의 2.1): 모든 양의 정수 `n ≥ 1`에 대해 어떤 `k ≥ 0`가 존재하여 `T^[k](n) = 1`. -/

def CollatzConjectureProp : Prop :=

  ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (T^[k]) n = 1



/-- 코프만 연산자 `U` (원본 v0.3 정의 2.1): `(U f)(n) = f(T(n))` -/

def KoopmanU (f : ℕ → ℝ) (n : ℕ) : ℝ :=

  f (T n)



/-- 양의 정수 위에서 `T`-불변인 함수 (`f ∈ ker(U - I)` on `ℕ_{>0}`) -/

def IsTInvariantOnPos (f : ℕ → ℝ) : Prop :=

  ∀ n : ℕ, 1 ≤ n → f (T n) = f n



/-- 양의 정수 위에서 유계인 함수 (`f ∈ ℓ^∞(ℕ_{>0}; ℝ)`) -/

def IsBoundedOnPos (f : ℕ → ℝ) : Prop :=

  ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 1 ≤ n → |f n| ≤ M



/-- 양의 정수 위에서 상수함수 (`f ∈ ℝ 1` on `ℕ_{>0}`) -/

def IsConstantOnPos (f : ℕ → ℝ) : Prop :=

  ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c



/-- 보조정리 2.1.1: `n ≥ 1`이면 `T(n) ≥ 1`이다 (`ℕ_{>0}`는 `T` 아래 닫혀 있다). -/

lemma T_pos_of_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ T n := by

  unfold T

  split_ifs with h

  · omega

  · omega



/-- 보조정리 2.1.2: `n ≥ 1`이면 모든 반복 `k`에 대해 `T^[k](n) ≥ 1`이다. -/

lemma T_iterate_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 1 ≤ (T^[k]) n := by

  induction k with

  | zero => exact hn

  | succ k ih =>

    rw [Function.iterate_succ_apply']

    exact T_pos_of_pos ih



/-- 보조정리 2.1.3: `f`가 양의 정수 위에서 `T`-불변이면 모든 `k ≥ 0`와 `n ≥ 1`에 대해 `f(T^[k](n)) = f(n)`이다. -/

lemma TInvariant_iterate {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :

    f ((T^[k]) n) = f n := by

  induction k with

  | zero => rfl

  | succ k ih =>

    rw [Function.iterate_succ_apply']

    have hpos : 1 ≤ (T^[k]) n := T_iterate_pos hn k

    rw [hf ((T^[k]) n) hpos, ih]



/-- 1에 도달하는 수들의 집합의 특성함수 `1_A` (원본 v0.3 정리 2.2 증명) -/

noncomputable def indicatorReachesOne (n : ℕ) : ℝ :=

  by

    classical

    exact if ∃ k : ℕ, (T^[k]) n = 1 then 1 else 0



/-- 보조정리 2.2.1: `1`은 `0`번 반복으로 `1`에 도달하므로 `indicatorReachesOne 1 = 1`이다. -/

lemma indicatorReachesOne_one : indicatorReachesOne 1 = 1 := by

  unfold indicatorReachesOne

  have h : ∃ k : ℕ, (T^[k]) 1 = 1 := ⟨0, rfl⟩

  simp [h]



/-- 보조정리 2.2.2: `n ≥ 1`에 대해 `n`이 1에 도달할 필요충분조건은 `T(n)`이 1에 도달하는 것이다 (원본 v0.3 정리 2.2 증명: `n ∈ A ↔ T(n) ∈ A`). -/

lemma reachesOne_iff_T_reachesOne {n : ℕ} (_hn : 1 ≤ n) :

    (∃ k : ℕ, (T^[k]) n = 1) ↔ (∃ k : ℕ, (T^[k]) (T n) = 1) := by

  constructor

  · rintro ⟨k, hk⟩

    cases k with

    | zero =>

      change n = 1 at hk

      subst hk

      refine ⟨1, ?_⟩

      change T (T 1) = 1

      decide

    | succ k =>

      refine ⟨k, ?_⟩

      rw [← Function.iterate_succ_apply]

      exact hk

  · rintro ⟨k, hk⟩

    refine ⟨k + 1, ?_⟩

    rw [Function.iterate_succ_apply]

    exact hk



/-- 보조정리 2.2.3: 특성함수 `indicatorReachesOne`은 유계 `T`-불변함수이다. -/

lemma indicatorReachesOne_invariant_and_bounded :

    IsBoundedOnPos indicatorReachesOne ∧ IsTInvariantOnPos indicatorReachesOne := by

  constructor

  · refine ⟨1, by norm_num, ?_⟩

    intro n _

    unfold indicatorReachesOne

    split_ifs <;> norm_num

  · intro n hn

    unfold indicatorReachesOne

    have heq := reachesOne_iff_T_reachesOne hn

    by_cases h : ∃ k : ℕ, (T^[k]) n = 1

    · have hT : ∃ k : ℕ, (T^[k]) (T n) = 1 := heq.mp h

      simp [h, hT]

    · have hT : ¬ ∃ k : ℕ, (T^[k]) (T n) = 1 := fun hc => h (heq.mpr hc)

      simp [h, hT]



/-- **정리 2.2 (코프만 고정점의 강직성과 콜라츠 추측; 원본 v0.3 p.19 식 (2))**:

    콜라츠 추측이 성립할 필요충분조건은 모든 유계 `T`-불변함수가 상수함수(`ker(U - I) = ℝ 1`)인 것이다. -/

theorem Theorem_2_2_Koopman_Rigidity :

    CollatzConjectureProp ↔

      (∀ f : ℕ → ℝ, IsBoundedOnPos f → IsTInvariantOnPos f → IsConstantOnPos f) := by

  constructor

  · intro hCC f _ hfInv

    refine ⟨f 1, ?_⟩

    intro n hn

    obtain ⟨k, hk⟩ := hCC n hn

    have hiter := TInvariant_iterate hfInv hn k

    rw [hk] at hiter

    exact hiter.symm

  · intro hRig n hn

    have ⟨hBdd, hInv⟩ := indicatorReachesOne_invariant_and_bounded

    obtain ⟨c, hc⟩ := hRig indicatorReachesOne hBdd hInv

    have h1 : indicatorReachesOne 1 = c := hc 1 (by omega)

    rw [indicatorReachesOne_one] at h1

    have hn_val : indicatorReachesOne n = 1 := by linarith [hc n hn]

    unfold indicatorReachesOne at hn_val

    by_contra hnot

    simp [hnot] at hn_val



/-- 정리 2.3을 위한 궤적 합류 관계 `x ~ y ⇔ ∃ a b : ℕ, T^[a](x) = T^[b](y)` (원본 v0.3 p.19) -/

def CollatzOrbitRel (x y : ℕ) : Prop :=

  ∃ a b : ℕ, (T^[a]) x = (T^[b]) y



/-- 콜라츠 그래프 `G_T`의 무향 인접 관계: `x = T(y)` 또는 `y = T(x)` -/

def CollatzEdge (x y : ℕ) : Prop :=

  y = T x ∨ x = T y



/-- 콜라츠 무향 그래프 `G_T`의 경로 연결성 (반사·대칭·추이 폐포) -/

inductive CollatzGraphConnected : ℕ → ℕ → Prop

  | refl (x : ℕ) : CollatzGraphConnected x x

  | step {x y z : ℕ} : CollatzEdge x y → CollatzGraphConnected y z → CollatzGraphConnected x z



/-- 보조정리 2.3.1: `CollatzOrbitRel`은 동치관계이다 (결정론적 사상의 궤적 합류 성질). -/

lemma CollatzOrbitRel_equivalence : Equivalence CollatzOrbitRel := by

  refine ⟨?_, ?_, ?_⟩

  · intro x

    exact ⟨0, 0, rfl⟩

  · rintro x y ⟨a, b, hab⟩

    exact ⟨b, a, hab.symm⟩

  · rintro x y z ⟨a, b, hab⟩ ⟨c, d, hcd⟩

    refine ⟨a + c, d + b, ?_⟩

    calc
      (T^[a + c]) x = (T^[c]) ((T^[a]) x) := by
        rw [Nat.add_comm a c, Function.iterate_add_apply]
      _ = (T^[c]) ((T^[b]) y) := congrArg (T^[c]) hab
      _ = (T^[b]) ((T^[c]) y) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
          Nat.add_comm c b]
      _ = (T^[b]) ((T^[d]) z) := congrArg (T^[b]) hcd
      _ = (T^[d + b]) z := by
        rw [Nat.add_comm d b, Function.iterate_add_apply]



/-- 보조정리 2.3.2: 무향 간선으로 이어진 두 정점은 `CollatzOrbitRel` 관계를 만족한다. -/

lemma CollatzEdge_imp_OrbitRel {x y : ℕ} (h : CollatzEdge x y) : CollatzOrbitRel x y := by

  rcases h with rfl | rfl

  · exact ⟨1, 0, rfl⟩

  · exact ⟨0, 1, rfl⟩



/-- 보조정리 2.3.3: 무향 경로로 연결된 두 정점은 `CollatzOrbitRel` 관계를 만족한다. -/

lemma CollatzGraphConnected_imp_OrbitRel {x y : ℕ} (h : CollatzGraphConnected x y) :

    CollatzOrbitRel x y := by

  induction h with

  | refl x => exact CollatzOrbitRel_equivalence.refl x

  | step hedge _ ih =>

    exact CollatzOrbitRel_equivalence.trans (CollatzEdge_imp_OrbitRel hedge) ih



/-- 보조정리 2.3.4: `k`번의 유향 반복 `(T^[k]) x = y`는 무향 그래프 경로 연결 `CollatzGraphConnected x y`를 함의한다. -/

lemma iterate_imp_CollatzGraphConnected (x k : ℕ) :

    CollatzGraphConnected x ((T^[k]) x) := by

  induction k generalizing x with

  | zero => exact CollatzGraphConnected.refl x

  | succ k ih =>

    rw [Function.iterate_succ_apply]

    exact CollatzGraphConnected.step (Or.inl rfl) (ih (T x))



/-- 보조정리 2.3.5: 무향 그래프 연결성의 대칭성 및 추이성 -/

lemma CollatzGraphConnected_trans {x y z : ℕ}

    (hxy : CollatzGraphConnected x y) (hyz : CollatzGraphConnected y z) :

    CollatzGraphConnected x z := by

  induction hxy with

  | refl _ => exact hyz

  | step hedge _ ih => exact CollatzGraphConnected.step hedge (ih hyz)



lemma CollatzGraphConnected_symm {x y : ℕ} (h : CollatzGraphConnected x y) :

    CollatzGraphConnected y x := by

  induction h with

  | refl x => exact CollatzGraphConnected.refl x

  | step hedge _ ih =>

    have hsym : CollatzEdge _ _ := hedge.symm

    exact CollatzGraphConnected_trans ih (CollatzGraphConnected.step hsym (CollatzGraphConnected.refl _))



/-- 보조정리 2.3.6: `1`의 `T`-궤적 원소 `(T^[b]) 1`에 도달한 모든 정점 `(T^[a]) n = (T^[b]) 1`은 추가 반복으로 `1`에 도달한다 (`T(1) = 2`, `T(2) = 1`). -/

lemma T_iterate_one_reaches_one (b : ℕ) :

    ∃ r : ℕ, (T^[r]) ((T^[b]) 1) = 1 := by

  have h_period : ∀ m : ℕ, (T^[m]) 1 = 1 ∨ (T^[m]) 1 = 2 := by

    intro m

    induction m with

    | zero => left; rfl

    | succ m ih =>

      rw [Function.iterate_succ_apply']

      rcases ih with h1 | h2

      · right; rw [h1]; decide

      · left; rw [h2]; decide

  rcases h_period b with h1 | h2

  · exact ⟨0, h1⟩

  · refine ⟨1, ?_⟩

    change T ((T^[b]) 1) = 1

    rw [h2]

    decide



/-- **정리 2.3 (그래프 연결성에 의한 재정식화; 원본 v0.3 p.19)**:

    콜라츠 추측이 성립할 필요충분조건은 꼭짓점이 `ℕ_{>0}`인 무향 콜라츠 그래프 `G_T`에서 모든 양의 정수 `n ≥ 1`이 `1`과 연결되어 있는 것이다. -/

theorem Theorem_2_3_Graph_Connectivity :

    CollatzConjectureProp ↔ (∀ n : ℕ, 1 ≤ n → CollatzGraphConnected n 1) := by

  constructor

  · intro hCC n hn

    obtain ⟨k, hk⟩ := hCC n hn

    have hconn := iterate_imp_CollatzGraphConnected n k

    rwa [hk] at hconn

  · intro hConn n hn

    have hrel := CollatzGraphConnected_imp_OrbitRel (hConn n hn)

    obtain ⟨a, b, hab⟩ := hrel

    obtain ⟨r, hr⟩ := T_iterate_one_reaches_one b

    refine ⟨r + a, ?_⟩

    rw [Function.iterate_add_apply, hab, hr]



/-! ## §3 2진 진동 보존 및 최적 합동류 근사 (GARCD-1, GARCD-2A, 따름정리 3.4) -/



/-- 보조정리 3.1.1: 짝수 분기 공식 `T(2 * m) = m`. -/

lemma T_two_mul (m : ℕ) : T (2 * m) = m := by

  unfold T

  have h : (2 * m) % 2 = 0 := by omega

  rw [if_pos h]

  omega



/-- 보조정리 3.1.2: 모든 `k ≥ 0`와 `n ≥ 0`에 대해 `T^[k](2^k * n) = n` (원본 v0.3 정리 3.2 증명 첫 줄). -/

lemma T_iterate_two_pow_mul (k n : ℕ) : (T^[k]) (2 ^ k * n) = n := by

  induction k generalizing n with

  | zero => simp

  | succ k ih =>

    rw [Function.iterate_succ_apply]

    have hpow : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring

    rw [hpow, T_two_mul, ih]



/-- 보조정리 3.1.3: `f`가 양의 정수 위에서 `T`-불변이면 모든 `k ≥ 0`와 `n ≥ 1`에 대해 `f(2^k * n) = f(n)`이다. -/

lemma TInvariant_two_pow_mul {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :

    f (2 ^ k * n) = f n := by

  have hpos : 1 ≤ 2 ^ k * n := by

    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)

    exact Nat.mul_le_mul this hn

  have hiter := TInvariant_iterate hf hpos k

  rw [T_iterate_two_pow_mul] at hiter

  exact hiter.symm



/-- **정리 3.2 (GARCD-1: 2진 진동 항등식 / Dyadic oscillation identity; 원본 v0.3 p.19 식 (5))**:

    양의 정수 위의 모든 `T`-불변함수 `f ∈ ker(U - I)`와 `k ≥ 0`, `a, b ≥ 1`에 대해

    `2^k * a ≡ 2^k * b (mod 2^k)`이며 `|f(2^k * a) - f(2^k * b)| = |f(a) - f(b)|`이다.

    따라서 법 `2^k` 합동류 내부의 진동 상한 `ω_k(f)`는 전역 진동 `Osc(f)`와 정확히 일치한다. -/

theorem GARCD_1_Dyadic_Oscillation_Identity

    {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) (k : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :

    (2 ^ k * a) % (2 ^ k) = (2 ^ k * b) % (2 ^ k) ∧

    |f (2 ^ k * a) - f (2 ^ k * b)| = |f a - f b| := by

  constructor

  · simp [Nat.mul_mod_right]

  · rw [TInvariant_two_pow_mul hf k ha, TInvariant_two_pow_mul hf k hb]



/-- 정리 3.2의 진동 집합 일치 버전: 법 `2^k` 합동류 위에서의 차이 집합과 전체 양의 정수 위에서의 차이 집합이 완전히 같다. -/

theorem GARCD_1_Oscillation_Set_Eq

    {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) (k : ℕ) :

    {d : ℝ | ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ m % (2 ^ k) = n % (2 ^ k) ∧ d = |f m - f n|} =

    {d : ℝ | ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ d = |f a - f b|} := by

  ext d

  simp only [Set.mem_setOf]

  constructor

  · rintro ⟨m, n, hm, hn, _, hd⟩

    exact ⟨m, n, hm, hn, hd⟩

  · rintro ⟨a, b, ha, hb, hd⟩

    have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)

    refine ⟨2 ^ k * a, 2 ^ k * b, Nat.mul_le_mul hpow ha, Nat.mul_le_mul hpow hb, ?_, ?_⟩

    · exact (GARCD_1_Dyadic_Oscillation_Identity hf k ha hb).1

    · rw [(GARCD_1_Dyadic_Oscillation_Identity hf k ha hb).2]

      exact hd



/-- 법 `2^k`에만 의존하는 주기함수 공간 `P_k = {h ∘ π_k : h : ℤ/2^kℤ → ℝ}` (원본 v0.3 정리 3.3) -/

def IsModTwoPowPeriodic (k : ℕ) (g : ℕ → ℝ) : Prop :=

  ∀ m n : ℕ, m % (2 ^ k) = n % (2 ^ k) → g m = g n



/-- **정리 3.3 (GARCD-2A: 최적 합동류 근사오차; 원본 v0.3 p.20 식 (6))**:

    (1) 하계: 임의의 `f ∈ ker(U - I)`와 임의의 `g ∈ P_k`에 대해, 만약 모든 `n ≥ 1`에서 `|f(n) - g(n)| ≤ E`이면

        모든 `a, b ≥ 1`에 대해 `|f(a) - f(b)| ≤ 2 * E` (즉 `Osc(f) / 2 ≤ ‖f - g‖_∞`)이다.

    (2) 상계 도달: 만약 모든 `n ≥ 1`에 대해 `L ≤ f(n) ≤ M`이면, 상수함수 `g_0(n) = (M + L) / 2 ∈ P_k`는

        모든 `n ≥ 1`에서 `|f(n) - g_0(n)| ≤ (M - L) / 2`를 달성한다. -/

theorem GARCD_2A_Optimal_Approximation_Lower

    {f g : ℕ → ℝ} (hf : IsTInvariantOnPos f) (k : ℕ) (hg : IsModTwoPowPeriodic k g)

    {E : ℝ} (hE : ∀ n : ℕ, 1 ≤ n → |f n - g n| ≤ E)

    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :

    |f a - f b| ≤ 2 * E := by

  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)

  have ha' : 1 ≤ 2 ^ k * a := Nat.mul_le_mul hpow ha

  have hb' : 1 ≤ 2 ^ k * b := Nat.mul_le_mul hpow hb

  have hmod : (2 ^ k * a) % (2 ^ k) = (2 ^ k * b) % (2 ^ k) := by

    simp [Nat.mul_mod_right]

  have hg_eq : g (2 ^ k * a) = g (2 ^ k * b) := hg _ _ hmod

  have hf_eq : |f a - f b| = |f (2 ^ k * a) - f (2 ^ k * b)| :=

    (GARCD_1_Dyadic_Oscillation_Identity hf k ha hb).2.symm

  have h1 : |f (2 ^ k * a) - g (2 ^ k * a)| ≤ E := hE (2 ^ k * a) ha'

  have h2 : |f (2 ^ k * b) - g (2 ^ k * b)| ≤ E := hE (2 ^ k * b) hb'

  calc

    |f a - f b| = |f (2 ^ k * a) - f (2 ^ k * b)| := hf_eq

    _ = |(f (2 ^ k * a) - g (2 ^ k * a)) - (f (2 ^ k * b) - g (2 ^ k * b))| := by

      rw [hg_eq]; ring_nf

    _ ≤ |f (2 ^ k * a) - g (2 ^ k * a)| + |f (2 ^ k * b) - g (2 ^ k * b)| :=

      abs_sub (f (2 ^ k * a) - g (2 ^ k * a)) (f (2 ^ k * b) - g (2 ^ k * b))

    _ ≤ E + E := add_le_add h1 h2

    _ = 2 * E := by ring



theorem GARCD_2A_Optimal_Approximation_Upper

    {f : ℕ → ℝ} {L M : ℝ} (hL : ∀ n : ℕ, 1 ≤ n → L ≤ f n) (hM : ∀ n : ℕ, 1 ≤ n → f n ≤ M) (k : ℕ) :

    IsModTwoPowPeriodic k (fun _ => (M + L) / 2) ∧

    (∀ n : ℕ, 1 ≤ n → |f n - (M + L) / 2| ≤ (M - L) / 2) := by

  constructor

  · intro _ _ _

    rfl

  · intro n hn

    rw [abs_le]

    constructor

    · linarith [hL n hn]

    · linarith [hM n hn]



/-- **따름정리 3.4 (2진 불연속성 장애물; 원본 v0.3 p.20)**:

    비상수 `T`-불변함수 `f` (`f(a) ≠ f(b)`인 `a, b ≥ 1` 존재)에 대해, 수열 `m_k = 2^k a`, `n_k = 2^k b`는

    모든 `k`에서 `2^k ∣ (m_k - n_k)` (즉 2진 거리가 `2^{-k} |a - b|_2 → 0`으로 수렴)를 만족하지만,

    함숫값의 차이는 모든 `k`에서 `|f(m_k) - f(n_k)| = |f(a) - f(b)| > 0`으로 일정하여 2진 위상에서 균등연속일 수 없다. -/

theorem Corollary_3_4_Dyadic_Discontinuity_Obstruction

    {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : f a ≠ f b) :

    ∃ ε > 0, ∀ k : ℕ,

      ((2 : ℤ) ^ k ∣ ((2 ^ k * a : ℕ) : ℤ) - ((2 ^ k * b : ℕ) : ℤ)) ∧

      |f (2 ^ k * a) - f (2 ^ k * b)| = ε := by

  refine ⟨|f a - f b|, abs_pos.mpr (sub_ne_zero.mpr hab), ?_⟩

  intro k

  constructor

  · refine ⟨(a : ℤ) - (b : ℤ), ?_⟩

    push_cast

    ring

  · exact (GARCD_1_Dyadic_Oscillation_Identity hf k ha hb).2



/-! ## §4 홀수 분기의 추가 진동 집중 (GARCD-3A; 원본 v0.3 p.20 정리 4.1) -/



/-- 홀수 분기 사상 `H(u) = 4u + 1` 및 수열 `c_k = (4^k - 1) / 3` (원본 v0.3 정리 4.1) -/

def H_map (u : ℕ) : ℕ := 4 * u + 1



def c_seq (k : ℕ) : ℕ := (4 ^ k - 1) / 3



/-- 보조정리 4.1.1: 모든 `k ≥ 0`에 대해 `3 * c_k + 1 = 4^k`이며 `c_{k+1} = 4 * c_k + 1`이다. -/

lemma three_mul_c_seq_add_one (k : ℕ) : 3 * c_seq k + 1 = 4 ^ k := by
  unfold c_seq
  have hmod : 4 ^ k % 3 = 1 := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      omega
  have hpos : 0 < 4 ^ k := by positivity
  omega



lemma c_seq_succ (k : ℕ) : c_seq (k + 1) = 4 * c_seq k + 1 := by

  have h1 := three_mul_c_seq_add_one k

  have h2 := three_mul_c_seq_add_one (k + 1)

  have hpow : 4 ^ (k + 1) = 4 * 4 ^ k := by ring

  omega



/-- 보조정리 4.1.2: 모든 `k ≥ 0`와 `u`에 대해 `H_map^[k](u) = 4^k * u + c_k` (원본 v0.3 식 (7) 첫째 식). -/

lemma H_map_iterate_eq (k u : ℕ) : (H_map^[k]) u = 4 ^ k * u + c_seq k := by

  induction k with

  | zero =>

    simp [c_seq]

  | succ k ih =>

    rw [Function.iterate_succ_apply', ih, H_map, c_seq_succ]

    ring



/-- 보조정리 4.1.3: 모든 홀수 `u`에 대해 `T(4u + 1) = 6u + 2`, `T^2(4u + 1) = 3u + 1`, `T^3(4u + 1) = T(u)` (원본 v0.3 정리 4.1 증명). -/

lemma T_three_H_map_of_odd {u : ℕ} (hu : u % 2 = 1) :

    T (H_map u) = 6 * u + 2 ∧

    (T^[2]) (H_map u) = 3 * u + 1 ∧

    (T^[3]) (H_map u) = T u := by

  have h1 : T (H_map u) = 6 * u + 2 := by

    unfold T H_map

    have hodd : (4 * u + 1) % 2 = 1 := by omega

    rw [if_neg (by omega)]

    omega

  have h2 : (T^[2]) (H_map u) = 3 * u + 1 := by

    change T (T (H_map u)) = 3 * u + 1

    rw [h1]

    unfold T

    have heven : (6 * u + 2) % 2 = 0 := by omega

    rw [if_pos heven]

    omega

  have h3 : (T^[3]) (H_map u) = T u := by

    change T ((T^[2]) (H_map u)) = T u

    rw [h2]

    unfold T

    have heven : (3 * u + 1) % 2 = 0 := by omega

    rw [if_pos heven, if_neg (by omega)]

  exact ⟨h1, h2, h3⟩



/-- 보조정리 4.1.4: 홀수 `u ≥ 1`와 `T`-불변함수 `f`에 대해 `f(H(u)) = f(u)`이다. -/

lemma TInvariant_H_map {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) {u : ℕ} (hu : u % 2 = 1) :

    f (H_map u) = f u := by

  have hu_pos : 1 ≤ u := by omega

  have hH_pos : 1 ≤ H_map u := by unfold H_map; omega

  have hiter := TInvariant_iterate hf hH_pos 3

  rw [(T_three_H_map_of_odd hu).2.2] at hiter

  rw [← hiter, hf u hu_pos]



/-- 보조정리 4.1.5: 홀수 `u`에 대해 `H_map^[k](u)`도 항상 홀수이다. -/

lemma H_map_iterate_odd {u : ℕ} (hu : u % 2 = 1) (k : ℕ) :

    ((H_map^[k]) u) % 2 = 1 := by

  induction k with

  | zero => exact hu

  | succ k ih =>

    rw [Function.iterate_succ_apply', H_map]

    omega



/-- **정리 4.1 (GARCD-3A: 홀수 분기와 `-1/3`으로의 진동 집중; 원본 v0.3 p.20 식 (7), (8))**:

    양의 정수 위의 모든 `T`-불변함수 `f`와 `k ≥ 1`, 홀수 `u, v`에 대해:

    (1) `H^[k](u) = 4^k * u + c_k` 이고 `f(H^[k](u)) = f(u)`이다.

    (2) `H^[k](u) ≡ H^[k](v) ≡ c_k (mod 4^k)`이며 `|f(H^[k](u)) - f(H^[k](v))| = |f(u) - f(v)|`이다.

    (3) `3 * H^[k](u) + 1 = 4^k * (3 * u + 1)`이 성립하여 `H^[k](u) ≡ -1/3 (mod 4^k)`로 집중된다. -/

theorem GARCD_3A_Odd_Branch_Concentration

    {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) (k : ℕ) {u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1) :

    (H_map^[k]) u = 4 ^ k * u + c_seq k ∧

    f ((H_map^[k]) u) = f u ∧

    ((H_map^[k]) u) % (4 ^ k) = c_seq k % (4 ^ k) ∧

    |f ((H_map^[k]) u) - f ((H_map^[k]) v)| = |f u - f v| ∧

    3 * (H_map^[k]) u + 1 = 4 ^ k * (3 * u + 1) := by

  have h_inv_iter : ∀ {w : ℕ}, w % 2 = 1 → f ((H_map^[k]) w) = f w := by

    intro w hw

    induction k with

    | zero => rfl

    | succ k ih =>

      rw [Function.iterate_succ_apply', TInvariant_H_map hf (H_map_iterate_odd hw k), ih]

  refine ⟨H_map_iterate_eq k u, h_inv_iter hu, ?_, ?_, ?_⟩

  · rw [H_map_iterate_eq]

    simp [Nat.mul_add_mod]

  · rw [h_inv_iter hu, h_inv_iter hv]

  · rw [H_map_iterate_eq]

    have hc := three_mul_c_seq_add_one k

    linarith



/-! ## §5 연속 불변함수 강직성 (원본 v0.3 p.21 정리 5.1) -/



/-- `ℕ_{>0}` 위에서 2진 거리로 `0`에서 연속(또는 균등연속)인 조건:

    임의의 `ε > 0`에 대해 어떤 `K : ℕ`가 존재하여 `2^K ∣ (m - n)`인 모든 `m, n ≥ 1`에서 `|f(m) - f(n)| < ε`. -/

def IsDyadicUniformlyContinuousOnPos (f : ℕ → ℝ) : Prop :=

  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →

    ((2 : ℤ) ^ K ∣ (m : ℤ) - (n : ℤ)) → |f m - f n| < ε



/-- **정리 5.1 (2진 연속 불변함수의 강직성; 원본 v0.3 p.21)**:

    `ℕ_{>0}`에서 정의된 `T`-불변함수가 2진 거리로 균등연속이면 반드시 상수함수이다. -/

theorem Theorem_5_1_Dyadic_Continuous_Invariant_Rigidity

    {f : ℕ → ℝ} (hf : IsTInvariantOnPos f) (hcont : IsDyadicUniformlyContinuousOnPos f) :

    IsConstantOnPos f := by

  refine ⟨f 1, ?_⟩

  intro n hn

  by_contra hne

  have hpos : 0 < |f n - f 1| := abs_pos.mpr (sub_ne_zero.mpr hne)

  obtain ⟨K, hK⟩ := hcont |f n - f 1| hpos

  have hpow : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)

  have hm_pos : 1 ≤ 2 ^ K * n := Nat.mul_le_mul hpow hn

  have h1_pos : 1 ≤ 2 ^ K * 1 := Nat.mul_le_mul hpow (le_refl 1)

  have hdvd : (2 : ℤ) ^ K ∣ ((2 ^ K * n : ℕ) : ℤ) - ((2 ^ K * 1 : ℕ) : ℤ) := by

    refine ⟨(n : ℤ) - 1, ?_⟩

    push_cast

    ring

  have hlt := hK (2 ^ K * n) (2 ^ K * 1) hm_pos h1_pos hdvd

  have heq := (GARCD_1_Dyadic_Oscillation_Identity hf K hn (le_refl 1)).2

  linarith



end Module1

end GARCD

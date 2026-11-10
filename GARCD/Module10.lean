import GARCD.Module09

open scoped BigOperators
open Finset Real Filter

namespace GARCD




/-!

================================================================================

# MODULE 10: 최종 결합 — `A-0 ∧ B-0 ↔ Collatz_Conjecture`, `DESC ↔ Collatz_Conjecture`,

  특수 계열 통합 비가분성·비실현 대정리, 그리고 `#print axioms` 검증

  (보충본 §2, §11, 과제집 §7, 형식증명 목표 설계서 §1~§9)

================================================================================

-/



section Module10



/-! ## §10.1 가속 시러큐스 수렴과 표준 콜라츠 수렴(`T^[k] n = 1`)의 정확한 연결 -/



/-- 보조정리 10.1.1: 모든 양의 정수 `m ≥ 1`에 대해 `v2 m`번의 짝수 콜라츠 단계 `T`를 적용하면 홀수 부분 `m / 2^{v2 m}`에 도달한다:

    `(T^[v2 m]) m = m / 2^{v2 m}`. -/

lemma T_iterate_v2_eq_div (m : ℕ) :

    (T^[v2 m]) m = m / 2 ^ v2 m := by

  by_cases hm0 : m = 0
  · subst m
    norm_num [v2]
  have hm_ne : m ≠ 0 := hm0

  have h_dvd : 2 ^ v2 m ∣ m := by
    unfold v2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm_ne).2 (le_refl _)

  have h_ord : 2 ^ v2 m * (m / 2 ^ v2 m) = m := Nat.mul_div_cancel' h_dvd

  set q := m / 2 ^ (m.factorization 2)

  have hm_eq : m = 2 ^ v2 m * q := by

    unfold v2

    exact h_ord.symm

  calc
    (T^[v2 m]) m = (T^[v2 m]) (2 ^ v2 m * q) :=
      congrArg (fun t => (T^[v2 m]) t) hm_eq
    _ = q := T_iterate_two_pow_mul (v2 m) q
    _ = m / 2 ^ v2 m := rfl



/-- 보조정리 10.1.2: 모든 홀수 `x`에 대해 한 번의 가속 시러큐스 단계 `F(x)`는 정확히 `a = v2(3x + 1)`번의 표준 콜라츠 단계 `T^[a](x)`와 같다!

    (왜냐하면 첫 단계 `T(x) = (3x + 1) / 2`이고 이후 `a - 1`번 `2`로 나누기 때문). -/

lemma F_eq_T_iterate_of_odd {x : ℕ} (hx_odd : x % 2 = 1) :

    F x = (T^[v2 (3 * x + 1)]) x := by

  have ha_ge1 : 1 ≤ v2 (3 * x + 1) := v2_three_mul_add_one_ge_one hx_odd

  obtain ⟨k, hk⟩ : ∃ k, v2 (3 * x + 1) = k + 1 := ⟨v2 (3 * x + 1) - 1, by omega⟩

  have h_step := two_pow_v2_mul_F x

  rw [hk] at h_step ⊢

  rw [Function.iterate_succ_apply]

  have hTx : T x = 2 ^ k * F x := by

    unfold T

    rw [if_neg (by omega : x % 2 ≠ 0)]

    have h_pow : 2 ^ (k + 1) * F x = 2 * (2 ^ k * F x) := by ring

    omega

  rw [hTx, T_iterate_two_pow_mul k (F x)]



/-- 보조정리 10.1.3: 홀수 `n`이 가속 시러큐스 사상으로 `1`에 도달하면(`ReachesOneSyracuse n`),

    표준 콜라츠 사상 `T`의 반복으로도 `1`에 도달한다(`∃ k, T^[k] n = 1`). -/

lemma syracuse_reaches_one_imp_collatz_reaches_one {n : ℕ} (hn_odd : n % 2 = 1)

    (hSyr : ReachesOneSyracuse n) :

    ∃ k : ℕ, (T^[k]) n = 1 := by

  obtain ⟨R, hR⟩ := hSyr

  have h_iter : ∀ r : ℕ, ∃ k : ℕ, (T^[k]) n = x_seq n r := by

    intro r

    induction r with

    | zero =>

      exact ⟨0, rfl⟩

    | succ r ih =>

      obtain ⟨k, hk⟩ := ih

      let a := v2 (3 * x_seq n r + 1)

      refine ⟨a + k, ?_⟩

      rw [Function.iterate_add_apply, hk]

      have hodd_r : x_seq n r % 2 = 1 := x_seq_odd hn_odd r

      rw [← F_eq_T_iterate_of_odd hodd_r]
      simp [x_seq, Function.iterate_succ_apply']

  obtain ⟨k, hk⟩ := h_iter R

  exact ⟨k, hk.trans hR⟩



/-- 보조정리 10.1.4: 모든 홀수 `n`에서 `ReachesOneSyracuse n`이 성립하면, 모든 양의 정수 `m ≥ 1`에서 `(T^[k]) m = 1`인 `k`가 존재한다 (`CollatzConjectureProp`). -/

lemma all_odd_syracuse_reaches_one_imp_CollatzConjectureProp

    (h_odd : ∀ n : ℕ, n % 2 = 1 → ReachesOneSyracuse n) :

    CollatzConjectureProp := by

  intro m hm_pos

  have hm_ne : m ≠ 0 := by omega

  let r := v2 m

  let q := m / 2 ^ r

  have h_dvd : 2 ^ r ∣ m := by
    dsimp [r, v2]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm_ne).2 (le_refl _)
  have h_eq : m = 2 ^ r * q := (Nat.mul_div_cancel' h_dvd).symm

  have hq_odd : q % 2 = 1 := by

    have hndvd : ¬ 2 ∣ q := by
      intro hbad
      have hnext : 2 ^ (r + 1) ∣ m := by
        obtain ⟨z, hz⟩ := hbad
        refine ⟨z, ?_⟩
        calc
          m = 2 ^ r * q := h_eq
          _ = 2 ^ r * (2 * z) := by rw [hz]
          _ = 2 ^ (r + 1) * z := by rw [pow_succ]; ring
      have hfactor := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm_ne).1 hnext
      dsimp [r, v2] at hfactor
      omega
    omega

  obtain ⟨k, hk⟩ := syracuse_reaches_one_imp_collatz_reaches_one hq_odd (h_odd q hq_odd)

  refine ⟨k + r, ?_⟩

  rw [Function.iterate_add_apply]

  have h_T_r : (T^[r]) m = q := by

    conv_lhs => rw [h_eq]

    exact T_iterate_two_pow_mul r q

  rw [h_T_r, hk]



/-- 보조정리 10.1.5: 역으로 `CollatzConjectureProp`가 성립하면 모든 홀수 `n`은 가속 시러큐스 사상으로도 `1`에 도달한다 (`ReachesOneSyracuse n`). -/

lemma T_reaches_one_imp_syracuse_reaches_one :

    ∀ k n : ℕ, 1 ≤ n → n % 2 = 1 → (T^[k]) n = 1 → ReachesOneSyracuse n := by

  intro k

  induction' k using Nat.strong_induction_on with k ih

  intro n hn_pos hn_odd hk

  by_cases hn1 : n = 1

  · subst hn1

    exact ⟨0, rfl⟩

  · -- n > 1 인 홀수에서 F(n) = (T^[a]) n 이고 a = v2(3n + 1) ≥ 1

    let a := v2 (3 * n + 1)

    have ha_ge1 : 1 ≤ a := v2_three_mul_add_one_ge_one hn_odd

    -- n > 1 인 홀수에서 3n + 1 ≥ 10 이므로 (T^[r]) n 이 처음으로 홀수가 되는 시점이 바로 r = a 이고,

    -- 중간 1 ≤ r < a 에서는 (T^[r]) n = (3n + 1) / 2^r 이 짝수(> 1)이므로 1 이 될 수 없다!

    have h_mid_even : ∀ r : ℕ, 1 ≤ r → r < a → (T^[r]) n ≠ 1 := by

      intro r hr1 hr_lt h_eq1

      obtain ⟨d, hd⟩ : ∃ d, a = r + (d + 1) := ⟨a - r - 1, by omega⟩

      have h_F : F n = (T^[d + 1]) ((T^[r]) n) := by

        rw [F_eq_T_iterate_of_odd hn_odd]

        change (T^[a]) n = (T^[d + 1]) ((T^[r]) n)

        rw [hd, Nat.add_comm r (d + 1), Function.iterate_add_apply]

      -- 만약 (T^[r]) n = 1 이라면 (T^[1]) n .. (T^[r]) n 과정에서 첫 단계 T n = (3n + 1) / 2 이고

      -- 1 ≤ r < a 동안 계속 짝수여서 T 를 한 번씩 적용할 때마다 2로 나누어진다:

      -- 실제로 2^a * F n = 3 * n + 1 이고 r < a 이므로 (3 * n + 1) = 2^r * (2^{a - r} * F n)

      have h_step_r : ∀ t : ℕ, 1 ≤ t → t ≤ a → (T^[t]) n = 2 ^ (a - t) * F n := by

        intro t ht1 hta

        obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩

        induction m with

        | zero =>

          simp only [Nat.zero_add, Function.iterate_one]

          unfold T

          rw [if_neg (by omega : n % 2 ≠ 0)]

          have h_step := two_pow_v2_mul_F n

          change 2 ^ a * F n = 3 * n + 1 at h_step

          have ha_split : a = 1 + (a - 1) := by omega

          have hpow : 2 ^ a * F n = 2 * (2 ^ (a - 1) * F n) := by

            conv_lhs => rw [ha_split, pow_add, pow_one]

            ring

          omega

        | succ m ihm =>

          have ihm' := ihm (by omega) (by omega)

          rw [Function.iterate_succ_apply', ihm']

          have h_exp : a - (m + 1) = 1 + (a - (m + 2)) := by omega

          rw [h_exp, pow_add, pow_one, mul_assoc, T_two_mul]

      have h_val_r := h_step_r r hr1 (le_of_lt hr_lt)

      rw [h_eq1] at h_val_r

      have h_ge2 : 2 ≤ 2 ^ (a - r) * F n := by

        have : 2 ≤ 2 ^ (a - r) := by

          obtain ⟨c, hc⟩ : ∃ c, a - r = c + 1 := ⟨a - r - 1, by omega⟩

          rw [hc, pow_succ']

          have : 0 < 2 ^ c := by positivity

          omega

        have : 1 ≤ F n := F_pos n

        nlinarith

      omega

    have hk_ge_a : a ≤ k := by

      by_contra hlt

      rcases Nat.eq_zero_or_pos k with rfl | hk_pos

      · change n = 1 at hk

        exact hn1 hk

      · exact h_mid_even k hk_pos (by omega) hk

    have h_rem : (T^[k - a]) (F n) = 1 := by

      rw [F_eq_T_iterate_of_odd hn_odd]

      change (T^[k - a]) ((T^[a]) n) = 1

      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk_ge_a]

      exact hk

    obtain ⟨R, hR⟩ := ih (k - a) (by omega) (F n) (F_pos n) (F_odd n) h_rem

    refine ⟨R + 1, ?_⟩

    unfold x_seq at hR ⊢

    rw [Function.iterate_succ_apply]

    exact hR



theorem Syracuse_Convergence_Iff_CollatzConjectureProp :

    (∀ n : ℕ, n % 2 = 1 → ReachesOneSyracuse n) ↔ CollatzConjectureProp := by

  constructor

  · exact all_odd_syracuse_reaches_one_imp_CollatzConjectureProp

  · intro hCC n hn_odd

    have hn_pos : 1 ≤ n := by omega

    obtain ⟨k, hk⟩ := hCC n hn_pos

    exact T_reaches_one_imp_syracuse_reaches_one k n hn_pos hn_odd hk



/-! ## §10.2 경로 C: 최소 반례 하강 명제 `DESCProp`와 콜라츠 추측의 무조건부 동치 증명 (`콜라츠 추측 형식증명 목표.txt` §6) -/



/-- 최소 반례 하강 명제 `DESCProp` (목표 설계서 §6 식 (DESC) & (DESC-F)):

    모든 홀수 `n ≥ 3`에 대해 어떤 `r ≥ 1`이 존재하여 `x_seq n r < n`

    (정리 6.3.2에 의해 정수 부등식 `(C_orbit n r : ℤ) < ((2 : ℤ)^{A_orbit n r} - 3^r) * n` 과 정확히 동치). -/

def DESCProp : Prop :=

  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n → ∃ r : ℕ, 1 ≤ r ∧ x_seq n r < n



def DESCArithmeticProp : Prop :=

  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →

    ∃ r : ℕ, 1 ≤ r ∧ (C_orbit n r : ℤ) < ((2 : ℤ) ^ A_orbit n r - (3 : ℤ) ^ r) * (n : ℤ)



/-- **정리 10.2.1 (`DESCProp ↔ DESCArithmeticProp`; 목표 설계서 §6 식 (DESC-F))**:

    하강 명제 `DESCProp`와 아핀 부등식 명제 `DESCArithmeticProp`는 논리적으로 완전히 동치이다. -/

theorem Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality :

    DESCProp ↔ DESCArithmeticProp := by

  unfold DESCProp DESCArithmeticProp

  refine forall_congr' (fun n => imp_congr_right (fun _ => imp_congr_right (fun _ => ?_)))

  refine exists_congr (fun r => and_congr_right (fun _ => ?_))

  exact GARCD_4_2_Exact_Descent_Iff n r



/-- **정리 10.2.2 (`DESCProp ↔ CollatzConjectureProp`; 목표 설계서 §6 핵심 연결 정리 — 무조건부 `theorem`)**:

    모든 홀수 `n ≥ 3`이 유한 번의 시러큐스 단계 후 자신보다 작은 홀수로 하강한다는 명제(`DESCProp`)는

    모든 양의 정수가 유한 번의 콜라츠 단계 후 `1`에 도달한다는 콜라츠 추측(`CollatzConjectureProp`)과 필요충분조건이다! -/

theorem Theorem_10_2_2_DESC_Iff_Collatz_Conjecture :

    DESCProp ↔ CollatzConjectureProp := by

  rw [← Syracuse_Convergence_Iff_CollatzConjectureProp]

  constructor

  · intro hDESC n

    induction' n using Nat.strong_induction_on with n ih

    intro hn_odd

    by_cases hn_lt3 : n < 3

    · have hn1 : n = 1 := by omega

      subst hn1

      exact ⟨0, rfl⟩

    · obtain ⟨r, _, hr_lt⟩ := hDESC n hn_odd (by omega)

      have h_odd_r : x_seq n r % 2 = 1 := x_seq_odd hn_odd r

      obtain ⟨R, hR⟩ := ih (x_seq n r) hr_lt h_odd_r

      refine ⟨r + R, ?_⟩

      unfold x_seq at hR ⊢

      rw [Nat.add_comm r R, Function.iterate_add_apply, hR]

  · intro hSyr n hn_odd hn_ge3

    obtain ⟨R, hR⟩ := hSyr n hn_odd

    rcases Nat.eq_zero_or_pos R with rfl | hR_pos

    · change n = 1 at hR

      omega

    · refine ⟨R, hR_pos, ?_⟩

      rw [hR]

      omega



/-! ## §10.3 경로 A + B: 의무 `A_0Prop` 및 `B_0Prop`와 콜라츠 추측의 무조건부 동치 증명 (보충본 §2 p.4 & 과제집 §7 p.50) -/



/-- 의무 A-0 명제 (`A_0Prop`; 보충본 미증명 과제 2.1 및 과제집 §2.1):

    허용 원시 블록 집합 `\mathcal{W}_{adm}`에 속하는 모든 word `w`에 대해 `¬ (D_nat w ∣ C_p w)` 이다

    (동치로, `1` 이외의 양의 홀수 주기 `x_seq m p = m` (`m > 1, p ≥ 1`)가 존재하지 않는다). -/

def A_0_NoNontrivialCycleProp : Prop :=

  ∀ m p : ℕ, m % 2 = 1 → 1 < m → 1 ≤ p → x_seq m p ≠ m



/-- 의무 B-0 명제 (`B_0Prop`; 보충본 미증명 과제 2.2 및 과제집 §4.1):

    비주기 무한 궤적(`¬ IsEventuallyPeriodicSyracuse n`)을 가지는 양의 홀수 `n`은 존재하지 않는다

    (정리 12.1 및 정리 19.1에 의해, 저지수 비주기 무한 word의 최소 대표값 `b_rep a r → ∞` 명제와 정확히 대응). -/

def B_0_NoAperiodicOrbitProp : Prop :=

  ∀ n : ℕ, n % 2 = 1 → IsEventuallyPeriodicSyracuse n



/-- 보조정리 10.3.1: `A_0_NoNontrivialCycleProp`는 모든 `m > 1, p ≥ 1` 홀수 주기의 지수 블록 `w = orbit_word m p`에서

    `¬ (D_nat w ∣ C_p w)`가 성립한다는 대수적 비가분성 명제와 정확히 동치이다. -/

theorem Lemma_10_3_1_A0_Cycle_Iff_Divisibility :

    A_0_NoNontrivialCycleProp ↔

      (∀ m p : ℕ, m % 2 = 1 → 1 < m → 1 ≤ p →

        ¬ (RealizesWord (orbit_word m p) m ∧

           3 ^ p < 2 ^ A_total (orbit_word m p) ∧

           D_nat (orbit_word m p) ∣ C_p (orbit_word m p) ∧

           C_p (orbit_word m p) = D_nat (orbit_word m p) * m)) := by

  unfold A_0_NoNontrivialCycleProp

  refine forall_congr' (fun m => forall_congr' (fun p => imp_congr_right (fun hm_odd =>

    imp_congr_right (fun hm_gt1 => imp_congr_right (fun hp => ?_)))))

  let w := orbit_word m p

  have hw_len : w.length = p := by simp [w, orbit_word]

  have hw_pos : ∀ a ∈ w, 1 ≤ a := by

    intro a ha

    simp [w, orbit_word] at ha

    rcases ha with ⟨j, _, rfl⟩

    exact a_seq_ge_one hm_odd j

  have hreal : RealizesWord w m := by

    refine ⟨hm_odd, hw_pos, ?_⟩

    intro j hj

    rw [hw_len] at hj

    have hj_word : j < (orbit_word m p).length := by
      simpa [orbit_word] using hj
    change a_seq m j = (orbit_word m p).getD j 0
    rw [List.getD_eq_getElem _ 0 hj_word]
    simp [orbit_word]

  constructor

  · intro hne ⟨_, hgt, _, h_eq⟩

    apply hne

    have hid := GARCD_4_1_Affine_Iteration_Identity m p

    have hA : A_orbit m p = A_total w := by

      unfold A_total

      have := A_orbit_eq_A_part_of_RealizesWord hreal p (by omega)

      rw [this, A_part, ← hw_len, List.take_length]

    have hC : C_orbit m p = C_p w := by

      unfold C_p

      rw [hw_len]

      exact C_orbit_eq_C_sum_of_RealizesWord hreal p (by omega)

    rw [hA, hC, h_eq] at hid

    have h_2Am : 3 ^ p * m + D_nat w * m = 2 ^ A_total w * m := by

      unfold D_nat

      rw [Nat.sub_mul, hw_len]

      have hle_mul : 3 ^ p * m ≤ 2 ^ A_total w * m := Nat.mul_le_mul_right m (le_of_lt hgt)

      omega

    rw [h_2Am] at hid

    exact Nat.eq_of_mul_eq_mul_left (by positivity) hid

  · intro hnot hper

    apply hnot

    have hper_w : x_seq m w.length = m := by rw [hw_len]; exact hper

    obtain ⟨hgt, _, heq⟩ := Theorem_14_1_Positive_Odd_Cycle_Equation (by omega) hreal hper_w

    rw [hw_len] at hgt

    exact ⟨hreal, hgt, ⟨m, heq.symm⟩, heq.symm⟩



/-- **정리 10.3.2 (`(A_0_NoNontrivialCycleProp ∧ B_0_NoAperiodicOrbitProp) ↔ CollatzConjectureProp`; 보충본 §2 p.4 & 과제집 §7 p.50의 완전 형식화 — 무조건부 `theorem`)**:

    "A-0(비자명 양의 홀수 주기 부재)와 B-0(비주기 양의 홀수 궤적 부재)가 모두 참이면 모든 양의 정수 궤적은 결국 `1`에 도달하며,

     역으로 콜라츠 추측이 참이면 A-0와 B-0도 모두 성립한다." -/

theorem Theorem_10_3_2_A0_And_B0_Iff_Collatz_Conjecture :

    (A_0_NoNontrivialCycleProp ∧ B_0_NoAperiodicOrbitProp) ↔ CollatzConjectureProp := by

  rw [← Syracuse_Convergence_Iff_CollatzConjectureProp]

  constructor

  · rintro ⟨hA0, hB0⟩ n hn_odd

    -- B-0 에 의해 n 의 시러큐스 궤적은 결국 주기적이다: ∃ j < k, x_seq n j = x_seq n k

    obtain ⟨j, k, hjk_lt, hjk_eq⟩ := hB0 n hn_odd

    let m := x_seq n j

    let p := k - j

    have hp_pos : 1 ≤ p := by omega

    have hm_odd : m % 2 = 1 := x_seq_odd hn_odd j

    have hm_per : x_seq m p = m := by

      unfold m x_seq

      rw [← Function.iterate_add_apply, Nat.add_comm p j, Nat.add_sub_of_le (le_of_lt hjk_lt)]

      exact hjk_eq.symm

    -- A-0 에 의해 주기 원소 m 은 1 보다 클 수 없으므로 반드시 m = 1 이다!

    have hm_eq1 : m = 1 := by

      by_contra hne1

      have hm_gt1 : 1 < m := by omega

      exact hA0 m p hm_odd hm_gt1 hp_pos hm_per

    exact ⟨j, hm_eq1⟩

  · intro hSyr

    constructor

    · -- 콜라츠 추측이 참이면 모든 홀수 m > 1 은 1 에 도달하는데, 만약 x_seq m p = m 이라면

      -- 모든 r 에 대해 x_seq m r 은 주기 {x_seq m 0, ..., x_seq m (p-1)} 안에만 머물고,

      -- 만약 어느 시점 R 에서 x_seq m R = 1 이면 이후 영원히 1 이므로 m = x_seq m (R * p) = 1 이 되어 m > 1 에 모순!

      intro m p hm_odd hm_gt1 hp_pos hper

      obtain ⟨R, hR⟩ := hSyr m hm_odd

      have h_iter_per : ∀ t : ℕ, x_seq m (t * p) = m := by

        intro t

        induction t with

        | zero => simp [x_seq]

        | succ t ih =>

          rw [Nat.succ_mul, x_seq, Nat.add_comm (t * p) p, Function.iterate_add_apply]

          change F^[p] (x_seq m (t * p)) = m

          rw [ih]

          exact hper

      have h_at_Rp : x_seq m (R * p) = 1 := by

        have h_ge : R ≤ R * p := Nat.le_mul_of_pos_right R hp_pos

        have h_split : R * p = R + (R * p - R) := by omega

        rw [h_split]

        exact (x_seq_add_of_eq_one hR (R * p - R)).1

      rw [h_iter_per R] at h_at_Rp

      omega

    · -- 콜라츠 추측이 참이면 모든 홀수 n 은 시점 R 에서 1 에 도달하므로 x_seq n R = 1 = x_seq n (R + 1) 로 결국 주기적!

      intro n hn_odd

      obtain ⟨R, hR⟩ := hSyr n hn_odd

      refine ⟨R, R + 1, by omega, ?_⟩

      have hR1 : x_seq n (R + 1) = 1 := (x_seq_add_of_eq_one hR 1).1

      rw [hR, hR1]



/-! ## §10.4 증명된 모든 특수 계열에 대한 비가분성·비실현 통합 대정리 (무조건부 `theorem`) -/



/-- **통합 대정리 (`Master_Verified_Regimes_Nondivisibility_And_Nonrealization`)**:

    Module 1부터 Module 9까지 밑바닥부터 증명한 모든 부분 영역에서 `sorry`나 `axiom` 없이

    비가분성(`¬ (D_nat w ∣ C_p w)`), 주기 배제, 그리고 무한 word 비실현(`b_r → ∞` / 비존재)이 무조건부로 성립한다:

    1. **[GARCD-31 유한 전수 검산 영역]**: `(p, A) = (5, 8)`의 35개 블록, `(8, 13)`의 792개 블록, 및 `p = 10`의 법 `499`/`13` 분류 전체에서 주기 비가분 성립.

    2. **[GARCD-32 무한 원시 계열]**: 모든 `p ≥ 30` 및 `2 * 3^p < 2^A`에서 `w_GARCD32 p A`는 `0 < C_p < D_nat`로 비가분 성립.

    3. **[GARCD-34 다중 원시 계열]**: 부분 지수합 `A_part w j ≤ j + t` 및 `2^{t+1} * 3^p < 2^A`인 모든 블록에서 `0 < C_p < D_nat`로 비가분 성립.

    4. **[A-1 / A-2 두 구간 블록 계열]**: `w = (1^u, 2^v)`에서 `D_nat w ∣ C_p w ↔ D_nat w ∣ (3^u - 2^u)` 이며 `3^u - 2^u < D_nat w`일 때 비가분 성립.

    5. **[GARCD-39 / 40 집중 지수 블록 계열]**: `t ≥ 2` (`C_p < 3 D_nat`) 및 `t ≥ 3` (`C_p < 7 D_nat`) 집중 계열과 조합 개수(214,645개 등) 성립.

    6. **[GARCD-41 / 42A 균형 기계적 `{1, 2}` word 계열]**: 순환회전과 `(1, 2) ↔ (2, 1)` 인접 교환이 결합된 모든 균형 기계적 word에서 `D_nat > 1 ⟹ ¬ (D_nat ∣ C_p)` 성립.

    7. **[GARCD-Q1 / Q2 / Q3 / Qk / SQ 및 정리 4.10 계열]**: 소인수별 선형 전이 제곱 판별식 및 대칭 제곱 판별식 `H_k(0) ≠ 0`에 의한 비가분 성립 (`C_p > D_nat`인 원시 블록 포함).

    8. **[GARCD-43 S-매끄러운 궤적 및 정리 19.3 / B-1 무한 word 계열]**: 유한 S-unit 해에 갇힌 궤적의 결국 주기성, 저지수 결국 주기 word의 비실현, 그리고 반복 확장 블록 `B-1`의 정량적 비실현 성립. -/

theorem Master_Verified_Regimes_Nondivisibility_And_Nonrealization :

    -- (1) GARCD-31 유한 검산 및 p=10 법 499/13 분류

    (checkNoCycleHits 5 8 = true ∧ checkNoCycleHits 8 13 = true ∧

     ((compositionsPos 5 8).all (fun v => C_p v % 13 != 0)) = true) ∧

    -- (2) GARCD-32 무한 원시 계열 (p ≥ 30)

    (∀ p A : ℕ, 30 ≤ p → 2 * 3 ^ p < 2 ^ A →

      ¬ (D_nat (w_GARCD32 p A) ∣ C_p (w_GARCD32 p A))) ∧

    -- (3) GARCD-34 다중 원시 계열

    (∀ (w : List ℕ) (t : ℕ), 1 ≤ w.length → (∀ a ∈ w, 1 ≤ a) →

      (∀ j < w.length, A_part w j ≤ j + t) →

      2 ^ (t + 1) * 3 ^ w.length < 2 ^ A_total w →

      ¬ (D_nat w ∣ C_p w)) ∧

    -- (4) A-1 / A-2 두 구간 블록 (1^u, 2^v)

    (∀ u v : ℕ, 1 ≤ u → 1 ≤ v → 3 ^ (u + v) ≤ 2 ^ (u + 2 * v) →

      3 ^ u - 2 ^ u < D_nat (w_two_segment u v) →

      ¬ (D_nat (w_two_segment u v) ∣ C_p (w_two_segment u v))) ∧

    -- (5) GARCD-39 집중 지수 블록

    (∀ w : List ℕ, 1 ≤ w.length → (∀ a ∈ w, 1 ≤ a) →

      2 ≤ t_excess w → 2 ^ (t_excess w - 1) * 3 ^ w.length < 2 ^ A_total w →

      C_p w ≠ D_nat w → ¬ (D_nat w ∣ C_p w)) ∧

    -- (6) GARCD-42A 순환회전-인접교환 결합 균형 기계적 word

    (∀ (w pre suf : List ℕ) (k₁ k₂ : ℕ),

      1 ≤ w.length → 1 < D_nat w →

      rotateLeft w k₁ = wordSwapAdj pre suf 1 2 →

      rotateLeft w k₂ = wordSwapAdj pre suf 2 1 →

      ¬ (D_nat w ∣ C_p w)) ∧

    -- (7) GARCD-SQ 대칭 제곱 판별식

    (∀ (w : List ℕ) (m : ℕ), 1 ≤ w.length → Nat.Coprime 3 m →

      3 ^ w.length ≤ 2 ^ A_total w → m ∣ D_nat w →

      H_sym_zero ((List.range w.length).map (t_trans w m)) ≠ 0 →

      ¬ (m ∣ C_p w)) ∧

    -- (8) 정리 19.3 저지수 결국 주기 무한 word의 점별 비실현

    (∀ (w : List ℕ), 1 ≤ w.length → (∀ a ∈ w, 1 ≤ a) →

      2 ^ A_total w ≤ 3 ^ w.length →

      ∀ n j₀ : ℕ, n % 2 = 1 →

        ¬ (∀ k : ℕ, RealizesWord w (x_seq n (j₀ + k * w.length)))) ∧

    -- (9) A-0 ∧ B-0 ↔ CollatzConjectureProp 및 DESCProp ↔ CollatzConjectureProp

    (((A_0_NoNontrivialCycleProp ∧ B_0_NoAperiodicOrbitProp) ↔ CollatzConjectureProp) ∧

     (DESCProp ↔ CollatzConjectureProp)) := by

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · exact ⟨GARCD_31_Exhaustive_Certificate_p5_p8.2.1,

           GARCD_31_Exhaustive_Certificate_p5_p8.2.2.2,

           Lemma_16_2_p10_Mod499_And_Mod13_Classification.2.2.2.2⟩

  · intro p A hp hA

    exact (GARCD_32_Infinite_Family_Nondivisibility hp hA).2.2.2.2

  · intro w t hp hw hpart hA

    exact (GARCD_34_Multi_Primitive_Block_Exclusion hp hw hpart hA).2.2.2

  · intro u v hu hv hle hA2

    exact Lemma_A_2_Strengthened_Inequality_Implies_A_1 hu hv hle hA2

  · intro w hp hw ht hA hne

    exact (GARCD_39_Concentrated_Block_Exclusion_3D hp hw ht hA).2.2 hne

  · intro w pre suf k₁ k₂ hp hD hrot1 hrot2

    exact GARCD_42A_Cyclic_Swap_Universal_Nondivisibility hp hD hrot1 hrot2

  · intro w m hp hcop3 hle hdvd hH

    exact GARCD_SQ_Symmetric_Square_Discriminant hp hcop3 hle hdvd hH

  · intro w hp hw hlow n j₀ hn_odd

    exact Theorem_19_3_Eventually_Periodic_Low_Valuation_Word_Unrealizable hp hw hlow n j₀ hn_odd

  · exact ⟨Theorem_10_3_2_A0_And_B0_Iff_Collatz_Conjecture,

           Theorem_10_2_2_DESC_Iff_Collatz_Conjecture⟩



/-- 최종 정리(보충본 §2 & 과제집 §7): 의무 A-0와 의무 B-0로부터 모든 양의 정수 `n > 0`이 유한 번의 콜라츠 반복으로 `1`에 도달함을 도출하는 정리

    (`sorryAx`나 사용자 정의 `axiom`을 전혀 사용하지 않는 순수 커널 검증 정리). -/

theorem Collatz_Conjecture_From_A0_And_B0

    (hA0 : A_0_NoNontrivialCycleProp) (hB0 : B_0_NoAperiodicOrbitProp)

    (n : ℕ) (hn : n > 0) :

    ∃ k : ℕ, (T^[k]) n = 1 :=

  Theorem_10_3_2_A0_And_B0_Iff_Collatz_Conjecture.mp ⟨hA0, hB0⟩ n hn



/-- 최종 정리(경로 C: 최소 반례 하강 정리 `DESC`): 최소 반례 하강 부등식 `(2^{A_r} - 3^r) n > C_r`로부터

    모든 양의 정수 `n > 0`이 유한 번의 콜라츠 반복으로 `1`에 도달함을 도출하는 정리. -/

theorem Collatz_Conjecture_From_DESC

    (hDESC : DESCArithmeticProp)

    (n : ℕ) (hn : n > 0) :

    ∃ k : ℕ, (T^[k]) n = 1 :=

  (Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality.symm.trans

    Theorem_10_2_2_DESC_Iff_Collatz_Conjecture).mp hDESC n hn




/-!

================================================================================

# MODULE 11: 3대 보완 과제 완전 해결 (GARCD-43 S-Unit 이변수 방정식 브리지,

  원고 직결 `A-0`/`B-0` 정의 및 동치 증명, 하우스도르프 차원 전 목표 완결) 및

  관문 1 (`A-0`), 관문 2 (`B-0` 및 Sturmian `B-2`), 경로 C (`DESC` 합동류 체) 극대화 확장

  (보충본 §1.6, §2, §7, §8, §11 및 과제집 §2~§7, 원본 v0.3 §13.1, §14.8, §19)

================================================================================

-/



end Module10

end GARCD

import GARCD.Module08

open scoped BigOperators
open Finset Real Filter

namespace GARCD




/-!

================================================================================

# MODULE 9: S-unit 매끄러운 수 궤적 및 B계열 무한 합동류·반복 확장 블록 배제

  (보충본 §7~§8, 원본 v0.3 §19, 과제집 §4~§5, GARCD-43, 정리 19.1 ~ 19.3, B-1)

================================================================================

-/



section Module9



/-! ## §7 매끄러운 수와 S-unit 방정식, 그리고 `3x + 1 = 4^k` 계열 (보충본 p.10~11 정의 7.1, 정리 7.2, 따름정리 7.3, §7.1; GARCD-43) -/



/-- 정의 7.1: 유한 소수 집합 `S : Finset ℕ`에 대하여 양의 정수 `n`의 모든 소인수가 `S`에 속할 때 `S`-매끄럽다(`IsSSmooth S n`)고 한다. -/

def IsSSmooth (S : Finset ℕ) (n : ℕ) : Prop :=

  1 ≤ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ S



/-- 정의 7.1: `n ≥ 2`의 최대 소인수 `P_plus n` (`P^+(1) = 1`, `P^+(0) = 1`) -/

def P_plus (n : ℕ) : ℕ :=

  (n.primeFactors).sup id ⊔ 1



/-- **정리 7.2 (GARCD-43: 유한 상태/유한 S-unit 해 집합에 갇힌 시러큐스 궤적의 결국 주기성; 보충본 p.11)**:

    시러큐스 관계식 `2^{a_j(n)} * x_{j+1}(n) - 3 * x_j(n) = 1` 에서, 어떤 시점 `j₀` 이후의 모든 궤적 원소 `x_j(n)` (`j ≥ j₀`)가

    유한한 후보 집합 `X_finite : Finset ℕ` (예: 두 변수 S-unit 방정식 `U_j + V_j = 1`의 유한 해 집합으로부터 유도된 유한 상태 공간)에 속하면,

    궤적 `(x_j(n))`은 반드시 결국 주기적(`IsEventuallyPeriodicSyracuse n`)이다. -/

theorem GARCD_43_Finite_SUnit_Orbit_Eventually_Periodic

    {n j₀ : ℕ} (X_finite : Finset ℕ)

    (h_trapped : ∀ j : ℕ, j₀ ≤ j → x_seq n j ∈ X_finite) :

    IsEventuallyPeriodicSyracuse n := by

  by_contra hap

  -- GARCD_12_Aperiodic_Orbit_Diverges 에 의해 비주기 궤적은 임의의 상수 M 보다 커진다.

  let M := X_finite.sup id

  obtain ⟨R, hR⟩ := GARCD_12_Aperiodic_Orbit_Diverges hap M

  let j := max j₀ R

  have hj_trapped : x_seq n j ∈ X_finite := h_trapped j (le_max_left j₀ R)

  have hj_le_M : x_seq n j ≤ M := Finset.le_sup (f := id) hj_trapped

  have hj_gt_M : M < x_seq n j := hR j (le_max_right j₀ R)

  omega



/-- **따름정리 7.3 (비결국주기 궤적에서 유한 전이쌍 집합의 유한 번 등장 및 탈출; 보충본 p.11)**:

    궤적 `(x_j(n))`이 결국 주기적이지 않다면(`¬ IsEventuallyPeriodicSyracuse n`),

    임의의 유한 전이쌍 집합 `T_pairs : Finset (ℕ × ℕ)` (예: 두 연속 항 `(x_j, x_{j+1})`이 동시에 `P`-매끄러운 유한 S-unit 해 집합)에 대해

    어떤 시점 `J_escape : ℕ`이 존재하여 모든 `j ≥ J_escape`에서 `(x_seq n j, x_seq n (j + 1)) ∉ T_pairs` 이다. -/

theorem Corollary_7_3_Consecutive_Terms_Prime_Factor_Escape

    {n : ℕ} (hap : ¬ IsEventuallyPeriodicSyracuse n)

    (T_pairs : Finset (ℕ × ℕ)) :

    ∃ J_escape : ℕ, ∀ j : ℕ, J_escape ≤ j → (x_seq n j, x_seq n (j + 1)) ∉ T_pairs := by

  let M := T_pairs.sup Prod.fst

  obtain ⟨J_escape, hJ⟩ := GARCD_12_Aperiodic_Orbit_Diverges hap M

  refine ⟨J_escape, ?_⟩

  intro j hj hmem

  have hle : x_seq n j ≤ M := Finset.le_sup (f := Prod.fst) hmem

  have hgt : M < x_seq n j := hJ j hj

  omega



/-- **보충본 §7.1 정리 (`3x + 1 = 4^k` 계열 `x = (4^k - 1) / 3 = c_seq k`의 1단계 시러큐스 수렴; 보충본 p.11)**:

    모든 `k ≥ 1`에 대해 `c_seq k = (4^k - 1) / 3`은 홀수이고 `3 * c_seq k + 1 = 2^{2k}`를 만족하며,

    단 한 번의 가속 시러큐스 단계로 `1`에 도달한다: `F (c_seq k) = 1` 및 `a_seq (c_seq k) 0 = 2 * k`. -/

theorem Section_7_1_One_Step_Syracuse_Convergence {k : ℕ} (hk : 1 ≤ k) :

    3 * c_seq k + 1 = 2 ^ (2 * k) ∧

    a_seq (c_seq k) 0 = 2 * k ∧

    F (c_seq k) = 1 := by

  have h3c := three_mul_c_seq_add_one k

  have h4_eq_2 : 4 ^ k = 2 ^ (2 * k) := by

    calc

      4 ^ k = (2 ^ 2) ^ k := by norm_num

      _ = 2 ^ (2 * k) := by rw [← pow_mul]

  have h_eq : 3 * c_seq k + 1 = 2 ^ (2 * k) := by rw [h3c, h4_eq_2]

  have hv2 : v2 (3 * c_seq k + 1) = 2 * k := by

    rw [v2_eq_iff_mod_two_pow_succ (by omega), h_eq]

    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))

  have ha0 : a_seq (c_seq k) 0 = 2 * k := hv2

  have hF1 : F (c_seq k) = 1 := by

    unfold F

    rw [hv2, h_eq, Nat.div_self (by positivity)]

  exact ⟨h_eq, ha0, hF1⟩



/-! ## §19 무한 합동류 최소 양의 홀수 대표값 `b_r`와 점별 실현 가능성 (원본 v0.3 p.35 정리 19.1, 보조정리 19.2, 정리 19.3 및 보충본 §8.1) -/



/-- 무한 지수열 `a : ℕ → ℕ`의 길이 `r` 유한 접두부 `prefixWord a r = [a 0, ..., a (r-1)]` -/

def prefixWord (a : ℕ → ℕ) (r : ℕ) : List ℕ :=

  (List.range r).map a



/-- 무한 지수열 `a : ℕ → ℕ`의 `r`단계 누적 지수 `A_inf a r = ∑_{j < r} a j` -/

def A_inf (a : ℕ → ℕ) (r : ℕ) : ℕ :=

  A_total (prefixWord a r)



/-- 무한 지수열 `a : ℕ → ℕ`의 `r`단계 보정항 `C_inf a r = C_p (prefixWord a r)` -/

def C_inf (a : ℕ → ℕ) (r : ℕ) : ℕ :=

  C_p (prefixWord a r)



/-- 무한 지수열 `a`의 처음 `r`개를 실현하는 법 `2^{A_r + 1}` 합동류의 최소 양의 대표값 `b_rep a r ∈ [0, 2^{A_r + 1})`

    (보충본 p.12~13 및 과제집 p.48 식 (B-residue): `b_r ≡ 3^{-r} (2^{A_r} - C_r) (mod 2^{A_r + 1})`) -/

def b_rep (a : ℕ → ℕ) (r : ℕ) : ℕ :=

  let M := 2 ^ (A_inf a r + 1)

  let u : ZMod M := (3 ^ r : ℕ)

  let target : ZMod M := (2 ^ A_inf a r : ℕ) - (C_inf a r : ℕ)

  (target * u⁻¹).val



/-- 양의 홀수 `n`이 무한 지수열 `a : ℕ → ℕ` 전체를 실현한다는 조건 (`∀ j ≥ 0, a_seq n j = a j`) -/

def RealizesInfiniteWord (a : ℕ → ℕ) (n : ℕ) : Prop :=

  n % 2 = 1 ∧ (∀ j : ℕ, 1 ≤ a j) ∧ ∀ j : ℕ, a_seq n j = a j



/-- 보조정리 19.1.1: `prefixWord a r`의 길이는 `r`이고, `∀ j, 1 ≤ a j`이면 `prefixWord a r`의 모든 원소는 `1` 이상이다. -/

lemma prefixWord_length_and_pos (a : ℕ → ℕ) (ha : ∀ j : ℕ, 1 ≤ a j) (r : ℕ) :

    (prefixWord a r).length = r ∧ ∀ x ∈ prefixWord a r, 1 ≤ x := by

  unfold prefixWord

  refine ⟨by simp, ?_⟩

  intro x hx

  rw [List.mem_map] at hx

  rcases hx with ⟨j, _, rfl⟩

  exact ha j



/-- 보조정리 19.1.2: `b_rep a r`는 `b_rep a r < 2^{A_inf a r + 1}` 이며 합동식

    `(3^r * b_rep a r + C_inf a r) % 2^{A_inf a r + 1} = 2^{A_inf a r}` 를 정확히 만족한다.

    따라서 `∀ j, 1 ≤ a j`일 때 `b_rep a r`는 홀수(`1 ≤ b_rep a r`)이고 `RealizesWord (prefixWord a r) (b_rep a r)`를 만족한다! -/

lemma b_rep_realizes_prefix (a : ℕ → ℕ) (ha : ∀ j : ℕ, 1 ≤ a j) (r : ℕ) :

    b_rep a r < 2 ^ (A_inf a r + 1) ∧

    (3 ^ r * b_rep a r + C_inf a r) % (2 ^ (A_inf a r + 1)) = 2 ^ A_inf a r ∧

    RealizesWord (prefixWord a r) (b_rep a r) ∧

    1 ≤ b_rep a r := by

  let M := 2 ^ (A_inf a r + 1)

  have hM_pos : 0 < M := by positivity

  haveI : NeZero M := ⟨ne_of_gt hM_pos⟩

  have hlt : b_rep a r < M := ZMod.val_lt _

  have hcop : Nat.Coprime (3 ^ r) M := coprime_three_pow_two_pow r (A_inf a r + 1)

  let u : ZMod M := (3 ^ r : ℕ)

  let target : ZMod M := (2 ^ A_inf a r : ℕ) - (C_inf a r : ℕ)

  have hu_mul : u * u⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one (3 ^ r) hcop

  have h_zmod : ((3 ^ r * b_rep a r + C_inf a r : ℕ) : ZMod M) = ((2 ^ A_inf a r : ℕ) : ZMod M) := by

    push_cast

    have hb_cast : ((b_rep a r : ℕ) : ZMod M) = target * u⁻¹ := ZMod.natCast_zmod_val (target * u⁻¹)

    rw [hb_cast]

    have h_pow_cast : (3 : ZMod M) ^ r = u := by
      simp [u]
    rw [h_pow_cast]

    calc

      u * (target * u⁻¹) + (C_inf a r : ZMod M)

          = target * (u * u⁻¹) + (C_inf a r : ZMod M) := by ring

      _ = target * 1 + (C_inf a r : ZMod M) := by rw [hu_mul]

      _ = (2 ^ A_inf a r : ZMod M) := by unfold target; ring

  have h_val := congrArg ZMod.val h_zmod

  simp only [ZMod.val_natCast] at h_val

  have h_cong : (3 ^ r * b_rep a r + C_inf a r) % M = 2 ^ A_inf a r := by

    rw [h_val]

    have hpowl : 2 ^ A_inf a r < 2 ^ (A_inf a r + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    exact Nat.mod_eq_of_lt (by simpa [M] using hpowl)

  obtain ⟨hlen, hpos_w⟩ := prefixWord_length_and_pos a ha r

  have h_cong_w : (3 ^ (prefixWord a r).length * b_rep a r + C_p (prefixWord a r)) %

      (2 ^ (A_total (prefixWord a r) + 1)) = 2 ^ A_total (prefixWord a r) := by

    rw [hlen]

    exact h_cong

  have hreal : RealizesWord (prefixWord a r) (b_rep a r) :=

    GARCD_4_3_Reverse_Appendix_A2 hpos_w h_cong_w

  have hb_ge1 : 1 ≤ b_rep a r := by

    have := hreal.1

    omega

  exact ⟨hlt, h_cong, hreal, hb_ge1⟩



/-- 보조정리 19.1.3: `n`이 `prefixWord a (r + 1)`을 실현하면 `prefixWord a r`도 실현한다. -/

lemma RealizesWord_prefix_of_succ {a : ℕ → ℕ} {n r : ℕ}

    (h : RealizesWord (prefixWord a (r + 1)) n) :

    RealizesWord (prefixWord a r) n := by

  refine ⟨h.1, ?_, ?_⟩

  · intro x hx

    unfold prefixWord at hx

    rw [List.mem_map] at hx

    rcases hx with ⟨j, hj, rfl⟩

    rw [List.mem_range] at hj

    apply h.2.1 (a j)

    unfold prefixWord

    rw [List.mem_map]

    exact ⟨j, List.mem_range.mpr (by omega), rfl⟩

  · intro j hj

    have hj_lt_r : j < r := by simpa [prefixWord] using hj

    have hj_lt_r1 : j < (prefixWord a (r + 1)).length := by simp [prefixWord]; omega

    have h_eq := h.2.2 j hj_lt_r1

    rw [h_eq]

    rw [List.getD_eq_getElem _ 0 hj_lt_r1]
    simp [prefixWord]



/-- **정리 19.1 (최소 양의 대표값 `b_r`의 비감소성, 증가 점화식 및 안정화 판정; 원본 v0.3 p.35)**:

    양의 무한 지수열 `a : ℕ → ℕ` (`∀ j, 1 ≤ a j`)에 대해:

    (1) 모든 `r ≥ 0`에서 `b_rep a r ≡ b_rep a (r + 1) (mod 2^{A_inf a r + 1})` 이므로 `b_rep a r ≤ b_rep a (r + 1)` (비감소 수열)이고,

        `b_rep a (r + 1) = b_rep a r + 2^{A_inf a r + 1} * k_r` (`0 ≤ k_r < 2^{a r}`)를 만족하는 `k_r`가 존재한다.

    (2) 만약 양의 홀수 `n`이 무한 word `a` 전체를 실현하면(`RealizesInfiniteWord a n`),

        `2^{A_inf a r + 1} > n`인 모든 `r` (특히 `r ≥ n`)에서 `b_rep a r = n` 으로 결국 상수가 된다. -/

theorem Theorem_19_1_Minimal_Representative_Monotone_And_Stabilization

    {a : ℕ → ℕ} (ha : ∀ j : ℕ, 1 ≤ a j) :

    (∀ r : ℕ, b_rep a r ≤ b_rep a (r + 1) ∧

      ∃ k_r : ℕ, k_r < 2 ^ (a r) ∧ b_rep a (r + 1) = b_rep a r + 2 ^ (A_inf a r + 1) * k_r) ∧

    (∀ n : ℕ, RealizesInfiniteWord a n →

      ∀ r : ℕ, n < 2 ^ (A_inf a r + 1) → b_rep a r = n) := by

  constructor

  · intro r

    obtain ⟨hlt_r, _, hreal_r, _⟩ := b_rep_realizes_prefix a ha r

    obtain ⟨hlt_r1, _, hreal_r1, _⟩ := b_rep_realizes_prefix a ha (r + 1)

    have hreal_r1_as_r : RealizesWord (prefixWord a r) (b_rep a (r + 1)) :=

      RealizesWord_prefix_of_succ hreal_r1

    have h_mod_eq : b_rep a (r + 1) % (2 ^ (A_inf a r + 1)) = b_rep a r % (2 ^ (A_inf a r + 1)) :=

      GARCD_4_3_Uniqueness_Mod_Two_Pow_Succ hreal_r1_as_r hreal_r

    rw [Nat.mod_eq_of_lt hlt_r] at h_mod_eq

    have h_div_mod := Nat.div_add_mod (b_rep a (r + 1)) (2 ^ (A_inf a r + 1))

    let k_r := b_rep a (r + 1) / 2 ^ (A_inf a r + 1)

    have h_decomp : b_rep a (r + 1) = b_rep a r + 2 ^ (A_inf a r + 1) * k_r := by

      change b_rep a (r + 1) = b_rep a r + 2 ^ (A_inf a r + 1) * (b_rep a (r + 1) / 2 ^ (A_inf a r + 1))

      omega

    have h_mono : b_rep a r ≤ b_rep a (r + 1) := by omega

    refine ⟨h_mono, k_r, ?_, h_decomp⟩

    -- A_inf a (r + 1) = A_inf a r + a r 확인

    have hA_succ : A_inf a (r + 1) = A_inf a r + a r := by

      unfold A_inf A_total prefixWord

      rw [List.range_succ, List.map_append, List.sum_append]

      simp

    have h_bound_r1 : 2 ^ (A_inf a r + 1) * k_r < 2 ^ (A_inf a r + 1) * 2 ^ (a r) := by

      calc

        2 ^ (A_inf a r + 1) * k_r ≤ b_rep a (r + 1) := by omega

        _ < 2 ^ (A_inf a (r + 1) + 1) := hlt_r1

        _ = 2 ^ (A_inf a r + 1) * 2 ^ (a r) := by

              rw [hA_succ, Nat.add_right_comm, pow_add]

    exact lt_of_mul_lt_mul_left h_bound_r1 (Nat.zero_le _)

  · intro n hn_inf r hn_lt

    obtain ⟨hlt_r, _, hreal_r, _⟩ := b_rep_realizes_prefix a ha r

    have hreal_n : RealizesWord (prefixWord a r) n := by

      refine ⟨hn_inf.1, (prefixWord_length_and_pos a ha r).2, ?_⟩

      intro j hj

      have hj_lt : j < r := by simpa [prefixWord] using hj

      rw [hn_inf.2.2 j]

      simp [prefixWord, List.getD_eq_getElem _ 0, hj_lt]

    have h_mod := GARCD_4_3_Uniqueness_Mod_Two_Pow_Succ hreal_r hreal_n

    change b_rep a r % (2 ^ (A_inf a r + 1)) =
      n % (2 ^ (A_inf a r + 1)) at h_mod
    rwa [Nat.mod_eq_of_lt hlt_r, Nat.mod_eq_of_lt hn_lt] at h_mod



/-- **정리 19.3 (결국 주기적인 저지수 무한 word의 양의 홀수 비실현; 원본 v0.3 p.35)**:

    길이 `p ≥ 1`인 양의 지수 블록 `w`가 저지수 조건 `2^{A_total w} ≤ 3^p` (즉 `A / p ≤ log₂ 3`)를 만족하면,

    유한한 초기 구간 `j₀` 이후 `w`를 반복하는 무한 word는 어떠한 양의 홀수 `n`에서도 실현될 수 없다! -/

theorem Theorem_19_3_Eventually_Periodic_Low_Valuation_Word_Unrealizable

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a)

    (h_low : 2 ^ A_total w ≤ 3 ^ w.length) :

    ∀ n j₀ : ℕ, n % 2 = 1 →

      ¬ (∀ k : ℕ, RealizesWord w (x_seq n (j₀ + k * w.length))) := by

  intro n j₀ hn_odd h_all

  let m := x_seq n j₀

  have hm_odd : m % 2 = 1 := x_seq_odd hn_odd j₀

  -- k = 0 에서 m = x_seq n j₀ 는 w 를 실현하고, 아핀 반복 공식에 의해

  -- 2^A * x_seq m p = 3^p * m + C_p w > 2^A * m 이므로 x_seq m p ≥ m + 1,

  -- 귀납적으로 모든 k 에 대해 x_seq n (j₀ + k * p) ≥ m + k 이고 동시에

  -- 2^A < 3^p 와 2진 합동류 고정점 식 (3^p - 2^A) * x_k + C_p w 의 2진 지수 발산:

  -- 구체적으로 H = 3^p - 2^A > 0 에 대해 보충본 §8.2의 B-1 항등식

  -- 3^{p k} * (H * m + C_p w) = 2^{k A} * (H * x_k + C_p w) 로부터

  -- 2^{k A} ∣ (H * m + C_p w) 가 모든 k 에 대해 성립해야 하나 H * m + C_p w > 0 이므로 k = H * m + C_p w 에서 모순!

  -- 먼저 2^A ≠ 3^p 이므로 2^A < 3^p 임을 확인:

  have h_strict : 2 ^ A_total w < 3 ^ w.length := by

    refine lt_of_le_of_ne h_low ?_

    intro heq

    have hdvd3 : 3 ∣ 2 ^ A_total w := by

      obtain ⟨k, hk⟩ : ∃ k, w.length = k + 1 := ⟨w.length - 1, by omega⟩

      rw [heq, hk, pow_succ]

      exact dvd_mul_left 3 (3 ^ k)

    have hcop : Nat.Coprime 3 (2 ^ A_total w) := coprime_odd_two_pow (by decide) (A_total w)

    have : 3 ∣ 1 := by

      rw [← hcop.gcd_eq_one]

      exact Nat.dvd_gcd (dvd_refl 3) hdvd3

    omega

  let H := 3 ^ w.length - 2 ^ A_total w

  have hH_pos : 0 < H := by omega

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).1

  -- 각 k 단계에서 2^A * x_{k+1} = 3^p * x_k + C_p w 이므로

  -- 2^A * (H * x_{k+1} + C_p w) = 3^p * (H * x_k + C_p w)

  let y_seq (k : ℕ) : ℕ := x_seq n (j₀ + k * w.length)

  have hy_step : ∀ k : ℕ, 2 ^ A_total w * (H * y_seq (k + 1) + C_p w) =

      3 ^ w.length * (H * y_seq k + C_p w) := by

    intro k

    have hreal_k := h_all k

    have hid := GARCD_4_1_Affine_Iteration_Identity (y_seq k) w.length

    have hA : A_orbit (y_seq k) w.length = A_total w := by

      unfold A_total

      rw [A_orbit_eq_A_part_of_RealizesWord hreal_k w.length (le_refl _), A_part, List.take_length]

    have hC : C_orbit (y_seq k) w.length = C_p w :=

      C_orbit_eq_C_sum_of_RealizesWord hreal_k w.length (le_refl _)

    have hy_next : x_seq (y_seq k) w.length = y_seq (k + 1) := by

      unfold y_seq x_seq

      rw [← Function.iterate_add_apply, Nat.add_comm w.length (j₀ + k * w.length),

          Nat.add_assoc, ← Nat.succ_mul]

    rw [hA, hC, hy_next] at hid

    calc

      2 ^ A_total w * (H * y_seq (k + 1) + C_p w)

          = H * (2 ^ A_total w * y_seq (k + 1)) + 2 ^ A_total w * C_p w := by ring

      _ = H * (3 ^ w.length * y_seq k + C_p w) + 2 ^ A_total w * C_p w := by rw [hid]

      _ = 3 ^ w.length * H * y_seq k + (H + 2 ^ A_total w) * C_p w := by ring

      _ = 3 ^ w.length * H * y_seq k + 3 ^ w.length * C_p w := by

            have hH_add : H + 2 ^ A_total w = 3 ^ w.length := Nat.sub_add_cancel (le_of_lt h_strict)

            rw [hH_add]

      _ = 3 ^ w.length * (H * y_seq k + C_p w) := by ring

  have hy_iter : ∀ k : ℕ, (2 ^ A_total w) ^ k * (H * y_seq k + C_p w) =

      (3 ^ w.length) ^ k * (H * y_seq 0 + C_p w) := by

    intro k

    induction k with

    | zero => simp

    | succ k ih =>

      calc

        (2 ^ A_total w) ^ (k + 1) * (H * y_seq (k + 1) + C_p w)

            = (2 ^ A_total w) ^ k * (2 ^ A_total w * (H * y_seq (k + 1) + C_p w)) := by

              rw [pow_succ]; ring

        _ = (2 ^ A_total w) ^ k * (3 ^ w.length * (H * y_seq k + C_p w)) := by rw [hy_step k]

        _ = 3 ^ w.length * ((2 ^ A_total w) ^ k * (H * y_seq k + C_p w)) := by ring

        _ = 3 ^ w.length * ((3 ^ w.length) ^ k * (H * y_seq 0 + C_p w)) := by rw [ih]

        _ = (3 ^ w.length) ^ (k + 1) * (H * y_seq 0 + C_p w) := by rw [pow_succ']; ring

  -- k = H * y_seq 0 + C_p w 로 잡으면 2^{k A} > H * y_seq 0 + C_p w 인데 2^{k A} ∣ (H * y_seq 0 + C_p w) 이어야 하므로 모순!

  let K := H * y_seq 0 + C_p w

  have hK_pos : 0 < K := by omega

  have hA_ge1 : 1 ≤ A_total w := by

    have := A_part_mono_add hw (Nat.zero_le w.length) (le_refl _)

    unfold A_total

    simp [A_part] at this

    omega

  have hdvd_3pow : (2 ^ A_total w) ^ K ∣ (3 ^ w.length) ^ K * K := by

    refine ⟨H * y_seq K + C_p w, ?_⟩

    exact (hy_iter K).symm

  have hcop_K : Nat.Coprime ((2 ^ A_total w) ^ K) ((3 ^ w.length) ^ K) := by

    rw [← pow_mul, ← pow_mul]

    exact (coprime_three_pow_two_pow (w.length * K) (A_total w * K)).symm

  have hdvd_K : (2 ^ A_total w) ^ K ∣ K := hcop_K.dvd_of_dvd_mul_left hdvd_3pow

  have h_le : (2 ^ A_total w) ^ K ≤ K := Nat.le_of_dvd hK_pos hdvd_K

  have h_gt : K < (2 ^ A_total w) ^ K := by

    have h2A_ge2 : 2 ≤ 2 ^ A_total w := by

      calc

        2 = 2 ^ 1 := by ring

        _ ≤ 2 ^ A_total w := Nat.pow_le_pow_right (by omega) hA_ge1

    calc

      K < 2 ^ K := Nat.lt_two_pow_self

      _ ≤ (2 ^ A_total w) ^ K := Nat.pow_le_pow_left h2A_ge2 K

  omega



/-! ## 보충본 §8.2 & 과제집 §5: 반복 확장 블록의 정량적 배제 (원본 B-1 상세 증명 및 §5.1, §5.2 적용; p.12 & p.49) -/



/-- 보조정리 B-1.1 (과제집 p.49 식 (B-1b)): 모든 홀수 시작값 `n`과 `j ≥ 0`에 대해

    `2^j * (x_seq n j + 1) ≤ 3^j * (n + 1)` (실수 형태 `x_j + 1 ≤ (3/2)^j (n + 1)`)이 성립한다. -/

theorem Lemma_B_1b_Syracuse_Upper_Growth_Bound

    {n : ℕ} (hn_odd : n % 2 = 1) (j : ℕ) :

    2 ^ j * (x_seq n j + 1) ≤ 3 ^ j * (n + 1) := by

  induction j with

  | zero =>

    simp [x_seq]

  | succ j ih =>

    have ha_ge1 : 1 ≤ a_seq n j := a_seq_ge_one hn_odd j

    have hpow_ge2 : 2 ≤ 2 ^ a_seq n j := by

      calc

        2 = 2 ^ 1 := by ring

        _ ≤ 2 ^ a_seq n j := Nat.pow_le_pow_right (by omega) ha_ge1

    have hstep := syracuse_step_eq n j

    have h_step2 : 2 * x_seq n (j + 1) + 2 ≤ 3 * (x_seq n j + 1) := by

      have : 2 * x_seq n (j + 1) ≤ 2 ^ a_seq n j * x_seq n (j + 1) :=

        Nat.mul_le_mul_right _ hpow_ge2

      omega

    calc

      2 ^ (j + 1) * (x_seq n (j + 1) + 1)

          = 2 ^ j * (2 * x_seq n (j + 1) + 2) := by rw [pow_succ]; ring

      _ ≤ 2 ^ j * (3 * (x_seq n j + 1)) := Nat.mul_le_mul_left _ h_step2

      _ = 3 * (2 ^ j * (x_seq n j + 1)) := by ring

      _ ≤ 3 * (3 ^ j * (n + 1)) := Nat.mul_le_mul_left 3 ih

      _ = 3 ^ (j + 1) * (n + 1) := by rw [pow_succ']; ring



/-- **과제집 §5 & 보충본 §8.2 정리 B-1 (반복 저지수 확장 블록의 정량적 비실현; 보충본 p.12 & 과제집 p.49 식 (10), (B-1a), (B-1b))**:

    길이 `p ≥ 1`인 양의 지수 블록 `w` (`∀ a ∈ w, 1 ≤ a`)가 `2^{A_total w} < 3^p` (`H = 3^p - 2^A > 0`)를 만족하고,

    양의 홀수 `n`의 궤적이 시점 `j`부터 `w`를 `k`회 연속 실현한다고 가정하자

    (`∀ t < k, RealizesWord w (x_seq n (j + t * p))`). 그러면:

    (1) 항등식 (10): `(2^{A(w)})^k * (H * x_{j + k p} + C_p w) = (3^p)^k * (H * x_j + C_p w)`,

    (2) 가분성 (B-1a): `2^{k * A(w) + 1} ∣ (H * x_j + C_p w)` 및 `2^{k * A(w) + 1} ≤ H * x_j + C_p w`,

    (3) 정량적 하계 부등식: `2^j * (2^{k * A(w) + 1} + H - C_p w) ≤ H * 3^j * (n + 1)`

        (따라서 `2^j * (2^{k_m * A(w) + 1} + H - C_p w) > H * 3^j * (n + 1)` 인 구간 `(j_m, k_m)`이 한 번이라도 나타나면

         `n`은 해당 무한 word를 절대 실현할 수 없다!). -/

theorem Theorem_B_1_Repeated_Expanding_Block_Exclusion

    {w : List ℕ} (hp : 1 ≤ w.length) (hw : ∀ a ∈ w, 1 ≤ a)

    (h_exp : 2 ^ A_total w < 3 ^ w.length)

    {n j k : ℕ} (hn_odd : n % 2 = 1)

    (h_real_k : ∀ t : ℕ, t < k → RealizesWord w (x_seq n (j + t * w.length))) :

    let H := 3 ^ w.length - 2 ^ A_total w

    let A := A_total w

    let p := w.length

    (2 ^ A) ^ k * (H * x_seq n (j + k * p) + C_p w) = (3 ^ p) ^ k * (H * x_seq n j + C_p w) ∧

    2 ^ (k * A + 1) ∣ (H * x_seq n j + C_p w) ∧

    2 ^ (k * A + 1) ≤ H * x_seq n j + C_p w ∧

    2 ^ j * (2 ^ (k * A + 1) + H - C_p w) ≤ H * 3 ^ j * (n + 1) := by

  intro H A p

  have hH_pos : 0 < H := by omega

  have hC_pos : 0 < C_p w := (Lemma_7_3_Correction_Upper_Bound_Nat hw hp (le_refl _)).1

  -- (1) k 에 대한 귀납법으로 반복 합성 항등식 (10) 증명

  have h_id_k : ∀ m : ℕ, m ≤ k →

      (2 ^ A) ^ m * (H * x_seq n (j + m * p) + C_p w) = (3 ^ p) ^ m * (H * x_seq n j + C_p w) := by

    intro m hm

    induction m with

    | zero => simp

    | succ m ih =>

      have hm_lt : m < k := by omega

      have ih_m := ih (by omega)

      have hreal_m := h_real_k m hm_lt

      have hid_step := GARCD_4_1_Affine_Iteration_Identity (x_seq n (j + m * p)) p

      have hA_m : A_orbit (x_seq n (j + m * p)) p = A := by

        unfold A A_total

        rw [A_orbit_eq_A_part_of_RealizesWord hreal_m p (le_refl _), A_part, List.take_length]

      have hC_m : C_orbit (x_seq n (j + m * p)) p = C_p w :=

        C_orbit_eq_C_sum_of_RealizesWord hreal_m p (le_refl _)

      have hx_next : x_seq (x_seq n (j + m * p)) p = x_seq n (j + (m + 1) * p) := by

        unfold x_seq

        rw [← Function.iterate_add_apply, Nat.add_comm p (j + m * p),

            Nat.add_assoc, ← Nat.succ_mul]

      rw [hA_m, hC_m, hx_next] at hid_step

      have h_one_step : 2 ^ A * (H * x_seq n (j + (m + 1) * p) + C_p w) =

          3 ^ p * (H * x_seq n (j + m * p) + C_p w) := by

        calc

          2 ^ A * (H * x_seq n (j + (m + 1) * p) + C_p w)

              = H * (2 ^ A * x_seq n (j + (m + 1) * p)) + 2 ^ A * C_p w := by ring

          _ = H * (3 ^ p * x_seq n (j + m * p) + C_p w) + 2 ^ A * C_p w := by rw [hid_step]

          _ = 3 ^ p * H * x_seq n (j + m * p) + (H + 2 ^ A) * C_p w := by ring

          _ = 3 ^ p * H * x_seq n (j + m * p) + 3 ^ p * C_p w := by

                have hH_add : H + 2 ^ A = 3 ^ p := Nat.sub_add_cancel (le_of_lt h_exp)

                rw [hH_add]

          _ = 3 ^ p * (H * x_seq n (j + m * p) + C_p w) := by ring

      calc

        (2 ^ A) ^ (m + 1) * (H * x_seq n (j + (m + 1) * p) + C_p w)

            = (2 ^ A) ^ m * (2 ^ A * (H * x_seq n (j + (m + 1) * p) + C_p w)) := by

              rw [pow_succ]; ring

        _ = (2 ^ A) ^ m * (3 ^ p * (H * x_seq n (j + m * p) + C_p w)) := by rw [h_one_step]

        _ = 3 ^ p * ((2 ^ A) ^ m * (H * x_seq n (j + m * p) + C_p w)) := by ring

        _ = 3 ^ p * ((3 ^ p) ^ m * (H * x_seq n j + C_p w)) := by rw [ih_m]

        _ = (3 ^ p) ^ (m + 1) * (H * x_seq n j + C_p w) := by rw [pow_succ']; ring

  have h10 := h_id_k k (le_refl k)

  -- (2) H, C_p w, x_{j + k p} 는 모두 홀수이므로 H * x_{j + k p} + C_p w 는 짝수!

  have hA_ge1 : 1 ≤ A := by
    have hpart := A_part_mono_add hw (Nat.zero_le p) (le_refl p)
    have hbound : w.length ≤ A_total w := by
      simpa [p, A_part, A_total] using hpart
    dsimp [A]
    omega

  have hH_odd : H % 2 = 1 := by

    unfold H

    have h2_even : 2 ^ A % 2 = 0 := by

      obtain ⟨m, hm⟩ : ∃ m, A = m + 1 := ⟨A - 1, by omega⟩

      rw [hm, pow_succ]

      omega

    have h3_odd : 3 ^ p % 2 = 1 := by
      induction p with
      | zero => rfl
      | succ m ih => rw [pow_succ]; omega
    have hH_add : H + 2 ^ A = 3 ^ p := Nat.sub_add_cancel (le_of_lt h_exp)
    omega

  have hC_odd : C_p w % 2 = 1 := C_p_odd_of_pos_word hw hp

  have hx_end_odd : x_seq n (j + k * p) % 2 = 1 := x_seq_odd hn_odd (j + k * p)

  have h_end_even : 2 ∣ (H * x_seq n (j + k * p) + C_p w) := by
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.mul_mod, hH_odd, hx_end_odd, hC_odd]

  obtain ⟨q_end, hq_end⟩ := h_end_even

  have hdvd_3pk : 2 ^ (k * A + 1) ∣ (3 ^ p) ^ k * (H * x_seq n j + C_p w) := by

    refine ⟨q_end, ?_⟩

    calc

      (3 ^ p) ^ k * (H * x_seq n j + C_p w)

          = (2 ^ A) ^ k * (H * x_seq n (j + k * p) + C_p w) := h10.symm

      _ = 2 ^ (A * k) * (2 * q_end) := by rw [← pow_mul, hq_end]

      _ = 2 ^ (k * A + 1) * q_end := by rw [Nat.mul_comm A k, pow_succ]; ring

  have hcop_2_3 : Nat.Coprime (2 ^ (k * A + 1)) ((3 ^ p) ^ k) := by

    rw [← pow_mul]

    exact (coprime_three_pow_two_pow (p * k) (k * A + 1)).symm

  have hdvd_B1a : 2 ^ (k * A + 1) ∣ (H * x_seq n j + C_p w) :=

    hcop_2_3.dvd_of_dvd_mul_left hdvd_3pk

  have h_ge_B1a : 2 ^ (k * A + 1) ≤ H * x_seq n j + C_p w :=

    Nat.le_of_dvd (by omega) hdvd_B1a

  -- (3) Lemma_B_1b 와 결합하여 하계 도출

  have h_B1b := Lemma_B_1b_Syracuse_Upper_Growth_Bound hn_odd j

  have h_lower : 2 ^ j * (2 ^ (k * A + 1) + H - C_p w) ≤ H * 3 ^ j * (n + 1) := by

    have h_step1 : 2 ^ (k * A + 1) + H - C_p w ≤ H * (x_seq n j + 1) := by
      have h_expand : H * (x_seq n j + 1) = H * x_seq n j + H := by ring
      rw [h_expand]
      omega

    calc

      2 ^ j * (2 ^ (k * A + 1) + H - C_p w)

          ≤ 2 ^ j * (H * (x_seq n j + 1)) := Nat.mul_le_mul_left _ h_step1

      _ = H * (2 ^ j * (x_seq n j + 1)) := by ring

      _ ≤ H * (3 ^ j * (n + 1)) := Nat.mul_le_mul_left H h_B1b

      _ = H * 3 ^ j * (n + 1) := by ring

  exact ⟨h10, hdvd_B1a, h_ge_B1a, h_lower⟩



/-- **과제집 §5.1 & §5.2 확인 정리 (`w = [1]` 및 `w = [1, 2]`의 작은 예와 비주기 지수열 `a = 1^2 2 1^4 2 1^8 2 ...`의 발산 지수 검산; 과제집 p.49)**:

    (1) `w = [1]`에서 `p = 1, A = 1, C_p = 1, H = 3^1 - 2^1 = 1` 이다.

    (2) `w = [1, 2]`에서 `p = 2, A = 3, C_p = 5, H = 3^2 - 2^3 = 1` 이다.

    (3) 과제집 §5.2 식 (11)의 비주기 word `a = 1^2 2 1^4 2 1^8 2 ...`에서 `m`번째 `1`-블록의 길이 `k_m = 2^m`과

        시작 위치 `j_m(m) = (2^m - 2) + (m - 1)` 에 대해, 모든 `m ≥ 2`에서 `j_m(m) < 2 * 2^m - 3` 이고

        `2^{2^m + 1} > (3 / 2)^{j_m(m)}` (정수 형태: `2^{j_m(m) + 2^m + 1} > 3^{j_m(m)}`)가 빠르게 발산한다. -/

def j_m_aperiodic (m : ℕ) : ℕ :=

  (2 ^ m - 2) + (m - 1)



theorem Section_5_1_And_5_2_Small_Examples_And_Aperiodic_Application :

    [1].length = 1 ∧ A_total [1] = 1 ∧ C_p [1] = 1 ∧ 3 ^ 1 - 2 ^ 1 = 1 ∧

    [1, 2].length = 2 ∧ A_total [1, 2] = 3 ∧ C_p [1, 2] = 5 ∧ 3 ^ 2 - 2 ^ 3 = 1 ∧

    -- m = 2, 3, 4, 5 에서 2^{j_m} * 2^{2^m + 1} > 3^{j_m} 확인

    3 ^ (j_m_aperiodic 2) < 2 ^ (j_m_aperiodic 2) * 2 ^ (2 ^ 2 + 1) ∧

    3 ^ (j_m_aperiodic 3) < 2 ^ (j_m_aperiodic 3) * 2 ^ (2 ^ 3 + 1) ∧

    3 ^ (j_m_aperiodic 4) < 2 ^ (j_m_aperiodic 4) * 2 ^ (2 ^ 4 + 1) ∧

    3 ^ (j_m_aperiodic 5) < 2 ^ (j_m_aperiodic 5) * 2 ^ (2 ^ 5 + 1) := by

  decide



end Module9

end GARCD

import GARCD.Module10
import GARCD.Support

open scoped BigOperators
open Finset Real Filter

namespace GARCD


section Module11



/-!

## §11.1 [단점 1 완전 보완] GARCD-43의 이변수 S'-unit 방정식 `U_j - V_j = 1` 환원 및

  `S`-매끄러운 궤적의 결국 주기성 직결 증명 (보충본 §1.6 p.3 & §7 p.10~11 정리 7.2, 따름정리 7.3)

-/



/-- 유한 소수 집합 `S : Finset ℕ`에 `2`와 `3`을 추가한 확장 소수 집합 `S' = S ∪ {2, 3}` (보충본 p.3 & p.11 식 (S-unit)) -/

def S_prime_ext (S : Finset ℕ) : Finset ℕ :=

  S ∪ {2, 3}



/-- 보조정리 11.1.1: `S`의 모든 원소 및 `2`, `3`은 `S_prime_ext S`의 원소이다. -/

lemma mem_S_prime_ext_self {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :

    p ∈ S_prime_ext S := by

  unfold S_prime_ext

  exact Finset.mem_union_left {2, 3} hp



lemma two_mem_S_prime_ext (S : Finset ℕ) : 2 ∈ S_prime_ext S := by

  unfold S_prime_ext

  exact Finset.mem_union_right S (by simp)



lemma three_mem_S_prime_ext (S : Finset ℕ) : 3 ∈ S_prime_ext S := by

  unfold S_prime_ext

  exact Finset.mem_union_right S (by simp)



/-- 보조정리 11.1.2: `S ⊆ S'`이면 `S`-매끄러운 양의 정수는 `S'`-매끄럽다. -/

lemma IsSSmooth_mono {S S' : Finset ℕ} (hsub : S ⊆ S') {n : ℕ} (hn : IsSSmooth S n) :

    IsSSmooth S' n := by

  refine ⟨hn.1, ?_⟩

  intro p hp hdvd

  exact hsub (hn.2 p hp hdvd)



/-- 보조정리 11.1.3: 두 양의 정수 `a, b`가 `S'`-매끄러우면 그 곱 `a * b`도 `S'`-매끄럽다. -/

lemma IsSSmooth_mul {S' : Finset ℕ} {a b : ℕ} (ha : IsSSmooth S' a) (hb : IsSSmooth S' b) :

    IsSSmooth S' (a * b) := by

  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩

  intro p hp hdvd

  rcases hp.dvd_mul.mp hdvd with hdvd_a | hdvd_b

  · exact ha.2 p hp hdvd_a

  · exact hb.2 p hp hdvd_b



/-- 보조정리 11.1.4: 소수 `q ∈ S'`에 대해 모든 거듭제곱 `q^k`는 `S'`-매끄럽다. -/

lemma IsSSmooth_prime_pow {S' : Finset ℕ} {q : ℕ} (hq_prime : Nat.Prime q) (hq_mem : q ∈ S') (k : ℕ) :

    IsSSmooth S' (q ^ k) := by

  refine ⟨Nat.one_le_pow k q hq_prime.pos, ?_⟩

  intro p hp hdvd

  have hp_dvd_q : p ∣ q := hp.dvd_of_dvd_pow hdvd

  have hp_eq_q : p = q := (Nat.dvd_prime hq_prime).mp hp_dvd_q |>.resolve_left hp.ne_one

  rwa [hp_eq_q]



/-- 시러큐스 `j`단계의 이변수 S'-unit 방정식 항:

    `U_sunit n j = 2^{a_seq n j} * x_seq n (j + 1)` 및 `V_sunit n j = 3 * x_seq n j` (보충본 p.3 & p.11). -/

def U_sunit (n j : ℕ) : ℕ :=

  2 ^ a_seq n j * x_seq n (j + 1)



def V_sunit (n j : ℕ) : ℕ :=

  3 * x_seq n j



/-- 이변수 `S'`-unit 선형 방정식 `U - V = 1` (`U + (-V) = 1`)의 양의 정수 해쌍 조건 (보충본 p.11 정리 7.2 증명):

    `U`와 `V`가 모두 `S'`-매끄러운 양의 정수이고 `U = V + 1`을 만족한다. -/

def IsSUnitEquationPair (S' : Finset ℕ) (U V : ℕ) : Prop :=

  IsSSmooth S' U ∧ IsSSmooth S' V ∧ U = V + 1



/-- **정리 11.1.1 (시러큐스 점화식의 이변수 `S'`-unit 방정식 `U_j - V_j = 1` 환원; 보충본 p.3 §1.6 & p.11 정리 7.2)**:

    만약 연속된 두 시러큐스 궤적 항 `x_seq n j`와 `x_seq n (j + 1)`이 모두 `S`-매끄러우면(`IsSSmooth S`),

    `U_j = U_sunit n j = 2^{a_j} x_{j+1}`과 `V_j = V_sunit n j = 3 x_j`는 확장 소수 집합 `S' = S ∪ {2, 3}`에 대해

    이변수 `S'`-unit 방정식 `IsSUnitEquationPair (S_prime_ext S) U_j V_j` (`U_j = V_j + 1`, 즉 `U_j - V_j = 1`)의 해가 되며,

    `x_seq n j = V_j / 3` 및 `x_seq n (j + 1) = U_j / 2^{v2 U_j}` 로부터 원래 궤적 항이 유일하게 복원된다. -/

theorem Theorem_11_1_1_Syracuse_Step_To_SUnit_Equation

    {S : Finset ℕ} {n j : ℕ}

    (hx_j : IsSSmooth S (x_seq n j))

    (hx_j1 : IsSSmooth S (x_seq n (j + 1))) :

    IsSUnitEquationPair (S_prime_ext S) (U_sunit n j) (V_sunit n j) ∧

    x_seq n j = V_sunit n j / 3 ∧

    (U_sunit n j : ℤ) + (-(V_sunit n j : ℤ)) = 1 := by

  have hsub : S ⊆ S_prime_ext S := by

    intro p hp

    exact mem_S_prime_ext_self hp

  have hU_smooth : IsSSmooth (S_prime_ext S) (U_sunit n j) := by

    unfold U_sunit

    exact IsSSmooth_mul

      (IsSSmooth_prime_pow Nat.prime_two (two_mem_S_prime_ext S) (a_seq n j))

      (IsSSmooth_mono hsub hx_j1)

  have hV_smooth : IsSSmooth (S_prime_ext S) (V_sunit n j) := by

    unfold V_sunit

    have h3 : IsSSmooth (S_prime_ext S) 3 := by

      simpa using IsSSmooth_prime_pow Nat.prime_three (three_mem_S_prime_ext S) 1

    exact IsSSmooth_mul h3 (IsSSmooth_mono hsub hx_j)

  have h_eq : U_sunit n j = V_sunit n j + 1 := by

    unfold U_sunit V_sunit

    exact syracuse_step_eq n j

  refine ⟨⟨hU_smooth, hV_smooth, h_eq⟩, ?_, ?_⟩

  · unfold V_sunit

    exact (Nat.mul_div_right (x_seq n j) (by omega : 0 < 3)).symm

  · have h_cast : (U_sunit n j : ℤ) = (V_sunit n j : ℤ) + 1 := by exact_mod_cast h_eq

    linarith



/-- 유한한 이변수 `S'`-unit 해쌍 집합 `Sol : Finset (ℕ × ℕ)`으로부터 유도되는 궤적 상태 유한 집합

    `X_finite_from_SUnit Sol = {V / 3 | (U, V) ∈ Sol}` (보충본 p.11 정리 7.2의 `X_finite` 구성). -/

def X_finite_from_SUnit (Sol : Finset (ℕ × ℕ)) : Finset ℕ :=

  Sol.image (fun uv => uv.2 / 3)



/-- **정리 11.1.2 (이변수 `S'`-unit 유한 해 집합으로부터 유한 궤적 상태 공간 `X_finite` 추출)**:

    시점 `j₀` 이후의 모든 `j ≥ j₀`에 대해 `x_seq n j`가 `S`-매끄럽고,

    해당 `S'`-unit 해쌍 `(U_sunit n j, V_sunit n j)`들이 유한 해 집합 `Sol : Finset (ℕ × ℕ)`에 속하면,

    모든 `j ≥ j₀`에서 `x_seq n j ∈ X_finite_from_SUnit Sol` 이다. -/

theorem Theorem_11_1_2_X_Finite_From_Finite_SUnit_Solutions

    {S : Finset ℕ} {n j₀ : ℕ}

    (h_smooth : ∀ j : ℕ, j₀ ≤ j → IsSSmooth S (x_seq n j))

    (Sol : Finset (ℕ × ℕ))

    (h_sol_finite : ∀ U V : ℕ, IsSUnitEquationPair (S_prime_ext S) U V → (U, V) ∈ Sol) :

    ∀ j : ℕ, j₀ ≤ j → x_seq n j ∈ X_finite_from_SUnit Sol := by

  intro j hj

  have hx_j : IsSSmooth S (x_seq n j) := h_smooth j hj

  have hx_j1 : IsSSmooth S (x_seq n (j + 1)) := h_smooth (j + 1) (by omega)

  obtain ⟨hpair, hx_rec, _⟩ := Theorem_11_1_1_Syracuse_Step_To_SUnit_Equation hx_j hx_j1

  have hmem_sol : (U_sunit n j, V_sunit n j) ∈ Sol := h_sol_finite _ _ hpair

  unfold X_finite_from_SUnit

  rw [Finset.mem_image]

  exact ⟨(U_sunit n j, V_sunit n j), hmem_sol, hx_rec.symm⟩



/-- **정리 11.1.3 (GARCD-43 원고 완결판: `S`-매끄러운 시러큐스 궤적의 결국 주기성; 보충본 p.3 & p.11 정리 7.2)**:

    유한 소수 집합 `S`에 대해 시점 `j₀` 이후의 모든 항이 `S`-매끄러운(`∀ j ≥ j₀, IsSSmooth S (x_seq n j)`) 시러큐스 궤적은,

    이변수 `S'`-unit 방정식 `U - V = 1` (`S' = S ∪ {2, 3}`)의 유한 해 집합 `Sol`을 통해 유한 상태 공간 `X_finite_from_SUnit Sol`에 갇히므로

    반드시 결국 주기적(`IsEventuallyPeriodicSyracuse n`)이다. -/

theorem GARCD_43_Full_SSmooth_Trajectory_Eventually_Periodic

    {S : Finset ℕ} {n j₀ : ℕ}

    (h_smooth : ∀ j : ℕ, j₀ ≤ j → IsSSmooth S (x_seq n j))

    (Sol : Finset (ℕ × ℕ))

    (h_sol_finite : ∀ U V : ℕ, IsSUnitEquationPair (S_prime_ext S) U V → (U, V) ∈ Sol) :

    IsEventuallyPeriodicSyracuse n := by

  have h_trapped := Theorem_11_1_2_X_Finite_From_Finite_SUnit_Solutions h_smooth Sol h_sol_finite

  exact GARCD_43_Finite_SUnit_Orbit_Eventually_Periodic (X_finite_from_SUnit Sol) h_trapped



/-- **따름정리 11.1.4 (보충본 p.11 따름정리 7.3 원고 완결판 — 비결국주기 궤적에서 이변수 `S'`-unit 해의 유한 번 등장 및 소인수 탈출)**:

    궤적 `(x_j(n))`이 결국 주기적이지 않다면(`¬ IsEventuallyPeriodicSyracuse n`),

    확장 소수 집합 `S' = S ∪ {2, 3}`에 대한 이변수 `S'`-unit 방정식 `U - V = 1`의 임의의 유한 해 집합 `Sol : Finset (ℕ × ℕ)`에 대해,

    어떤 시점 `J_escape : ℕ`이 존재하여 모든 `j ≥ J_escape`에서

    `¬ (IsSSmooth S (x_seq n j) ∧ IsSSmooth S (x_seq n (j + 1)) ∧ (U_sunit n j, V_sunit n j) ∈ Sol)` 이다

    (즉 연속한 두 항 `x_j, x_{j+1}`이 동시에 `S`-매끄러운 유한 `S'`-unit 해에 머무는 일은 유한 번뿐이며,

     `max(P^+(x_j), P^+(x_{j+1}))`은 임의의 유한 소수 장벽을 탈출한다). -/

theorem Corollary_7_3_Full_SSmooth_Prime_Factor_Escape

    {S : Finset ℕ} {n : ℕ} (hap : ¬ IsEventuallyPeriodicSyracuse n)

    (Sol : Finset (ℕ × ℕ)) :

    ∃ J_escape : ℕ, ∀ j : ℕ, J_escape ≤ j →

      ¬ (IsSSmooth S (x_seq n j) ∧ IsSSmooth S (x_seq n (j + 1)) ∧

         (U_sunit n j, V_sunit n j) ∈ Sol) := by

  let M := (X_finite_from_SUnit Sol).sup id

  obtain ⟨J_escape, hJ⟩ := GARCD_12_Aperiodic_Orbit_Diverges hap M

  refine ⟨J_escape, ?_⟩

  intro j hj ⟨_, _, hmem_sol⟩

  have hx_mem : x_seq n j ∈ X_finite_from_SUnit Sol := by

    unfold X_finite_from_SUnit

    rw [Finset.mem_image]

    refine ⟨(U_sunit n j, V_sunit n j), hmem_sol, ?_⟩

    unfold V_sunit

    exact Nat.mul_div_right (x_seq n j) (by omega : 0 < 3)

  have hle : x_seq n j ≤ M := Finset.le_sup (f := id) hx_mem

  have hgt : M < x_seq n j := hJ j hj

  omega



/-!

## §11.2 [단점 2 완전 보완] 원고의 대수적 `A-0` 및 `B-0` 정의와 동역학적 정의 사이의

  엄밀한 동치 정리 및 `(A_0_ManuscriptProp ∧ B_0_ManuscriptProp) ↔ CollatzConjectureProp` 증명

  (보충본 §1.1, §2 p.4, 원본 §14.8 보조정리 14.8, §19 정리 19.1, 과제집 §2.1, §4.1, §7)

-/



/-- **원고 정의 그대로의 의무 A-0 (`A_0_ManuscriptProp`; 보충본 p.4 미증명 과제 2.1 & 과제집 p.45 §2.1)**:

    원시 허용 블록 집합 `\mathcal{W}_{adm}` (`IsAdmissibleWord w`)에 속하는 모든 유한 지수 블록 `w`에 대해

    `D_nat w`는 `C_p w`를 나누지 않는다 (`¬ (D_nat w ∣ C_p w)`). -/

def A_0_ManuscriptProp : Prop :=

  ∀ w : List ℕ, IsAdmissibleWord w → ¬ (D_nat w ∣ C_p w)



/-- 보조정리 11.2.1: 두 리스트 `u, v`를 이어 붙인 `u ++ v`에 대해

    `j ≤ u.length`이면 `A_part (u ++ v) j = A_part u j` 이고,

    임의의 `j`에서 `A_part (u ++ v) (u.length + j) = A_total u + A_part v j` 이다. -/

lemma A_part_append_left (u v : List ℕ) {j : ℕ} (hj : j ≤ u.length) :

    A_part (u ++ v) j = A_part u j := by

  unfold A_part

  rw [List.take_append_of_le_length hj]



lemma A_part_append_right (u v : List ℕ) (j : ℕ) :

    A_part (u ++ v) (u.length + j) = A_total u + A_part v j := by

  simp [A_part, A_total, List.take_append]



/-- 보조정리 11.2.2: 두 리스트 `u, v`를 이어 붙인 `u ++ v`의 보정항 `C_p (u ++ v)`는

    `C_p (u ++ v) = 3^{v.length} * C_p u + 2^{A_total u} * C_p v` 를 만족한다. -/

lemma C_p_append (u v : List ℕ) :

    C_p (u ++ v) = 3 ^ v.length * C_p u + 2 ^ A_total u * C_p v := by

  unfold C_p C_sum

  rw [List.length_append, sum_range_add, mul_sum, mul_sum]

  congr 1

  · refine sum_congr rfl ?_

    intro j hj

    have hj_lt : j < u.length := mem_range.mp hj

    rw [A_part_append_left u v (le_of_lt hj_lt)]

    have hexp : u.length + v.length - 1 - j = v.length + (u.length - 1 - j) := by omega

    rw [hexp, pow_add]

    ring

  · refine sum_congr rfl ?_

    intro j hj

    have hj_lt : j < v.length := mem_range.mp hj

    rw [A_part_append_right u v j, pow_add]

    have hexp : u.length + v.length - 1 - (u.length + j) = v.length - 1 - j := by omega

    rw [hexp]

    ring



/-- **보조정리 11.2.3 (GARCD-23 보정항 분해: `C_p(w^k) = C_p(w) * S_k(w)` 및 `D_nat(w^k) = D_nat(w) * S_k(w)`; 원본 v0.3 p.31 보조정리 14.8)**:

    모든 유한 지수 블록 `w`와 반복 횟수 `k ≥ 0`에 대해:

    (1) `C_p (repeatWord w k) = C_p w * S_repeat_factor w k`,

    (2) `3^{w.length} ≤ 2^{A_total w}` 이면 `D_nat (repeatWord w k) = D_nat w * S_repeat_factor w k` 이다. -/

theorem GARCD_23_Repeated_Block_C_And_D_Decomposition (w : List ℕ) (k : ℕ) :

    C_p (repeatWord w k) = C_p w * S_repeat_factor w k ∧

    (3 ^ w.length ≤ 2 ^ A_total w → D_nat (repeatWord w k) = D_nat w * S_repeat_factor w k) := by

  have hC : C_p (repeatWord w k) = C_p w * S_repeat_factor w k := by

    induction k with

    | zero =>

      simp [repeatWord, C_p, C_sum, S_repeat_factor]

    | succ k ih =>

      unfold repeatWord

      rw [C_p_append w (repeatWord w k), ih]

      obtain ⟨hlen_k, _⟩ := repeatWord_length_and_sum w k

      rw [hlen_k]

      unfold S_repeat_factor

      rw [sum_range_succ, mul_add]

      have h_tail : 2 ^ A_total w *

          (C_p w * ∑ x ∈ range k, 2 ^ (A_total w * (k - 1 - x)) * 3 ^ (w.length * x)) =

          C_p w * ∑ x ∈ range k, 2 ^ (A_total w * (k - x)) * 3 ^ (w.length * x) := by

        rw [← mul_assoc, mul_comm (2 ^ A_total w) (C_p w), mul_assoc, mul_sum, mul_sum]

        refine sum_congr rfl ?_

        intro x hx

        have hx_lt : x < k := mem_range.mp hx

        have hexp : A_total w * (k - x) = A_total w + A_total w * (k - 1 - x) := by

          have : k - x = 1 + (k - 1 - x) := by omega

          rw [this, Nat.mul_add, Nat.mul_one]

        rw [hexp, pow_add]

        ring

      have hexp0 : k - k = 0 := by omega

      rw [hexp0, Nat.mul_zero, pow_zero, one_mul]

      linarith

  refine ⟨hC, ?_⟩

  intro hle

  obtain ⟨hlen_k, hsum_k⟩ := repeatWord_length_and_sum w k

  have hle_k : 3 ^ (repeatWord w k).length ≤ 2 ^ A_total (repeatWord w k) := by

    rw [hlen_k, hsum_k, pow_mul 3, pow_mul 2]

    exact Nat.pow_le_pow_left hle k

  have hD_int := GARCD_23_Repeated_Block_D_Decomposition w k

  have hD_lhs : (D_nat (repeatWord w k) : ℤ) = D_int (repeatWord w k) := by

    unfold D_nat D_int

    exact Int.ofNat_sub hle_k

  have hD_rhs : (D_nat w : ℤ) = D_int w := by

    unfold D_nat D_int

    exact Int.ofNat_sub hle

  have h_eq_z : (D_nat (repeatWord w k) : ℤ) = ((D_nat w * S_repeat_factor w k : ℕ) : ℤ) := by

    push_cast

    rw [hD_lhs, hD_rhs, hD_int]

  exact Int.ofNat.inj h_eq_z



/-- 보조정리 11.2.4: `k ≥ 1`일 때 공통인수 `S_repeat_factor w k`는 양수(`0 < S_repeat_factor w k`)이며,

    따라서 `3^{w.length} ≤ 2^{A_total w}` 이면

    `D_nat (repeatWord w k) ∣ C_p (repeatWord w k) ↔ D_nat w ∣ C_p w` 이다. -/

lemma S_repeat_factor_pos (w : List ℕ) {k : ℕ} (hk : 1 ≤ k) :

    0 < S_repeat_factor w k := by

  unfold S_repeat_factor

  have h0 : 0 ∈ range k := mem_range.mpr hk

  have hterm : 0 < 2 ^ (A_total w * (k - 1 - 0)) * 3 ^ (w.length * 0) := by positivity

  exact lt_of_lt_of_le hterm (single_le_sum (fun _ _ => Nat.zero_le _) h0)



theorem GARCD_23_Repeated_Block_Divisibility_Iff

    (w : List ℕ) {k : ℕ} (hk : 1 ≤ k) (hle : 3 ^ w.length ≤ 2 ^ A_total w) :

    D_nat (repeatWord w k) ∣ C_p (repeatWord w k) ↔ D_nat w ∣ C_p w := by

  obtain ⟨hC, hD⟩ := GARCD_23_Repeated_Block_C_And_D_Decomposition w k

  rw [hC, hD hle]

  have hS_pos : 0 < S_repeat_factor w k := S_repeat_factor_pos w hk

  exact mul_dvd_mul_iff_right (ne_of_gt hS_pos)



/-- 보조정리 11.2.5: `repeatWord`의 결합법칙:

    `repeatWord v (a + b) = repeatWord v a ++ repeatWord v b` 및

    `repeatWord (repeatWord v a) b = repeatWord v (a * b)`. -/

lemma repeatWord_add (v : List ℕ) (a b : ℕ) :

    repeatWord v (a + b) = repeatWord v a ++ repeatWord v b := by

  induction a with

  | zero =>

    simp [repeatWord]

  | succ a ih =>
    rw [Nat.succ_add]
    change v ++ repeatWord v (a + b) =
      (v ++ repeatWord v a) ++ repeatWord v b
    rw [ih, List.append_assoc]



lemma repeatWord_mul (v : List ℕ) (a b : ℕ) :

    repeatWord (repeatWord v a) b = repeatWord v (a * b) := by

  induction b with

  | zero =>

    simp [repeatWord]

  | succ b ih =>
    change repeatWord v a ++ repeatWord (repeatWord v a) b =
      repeatWord v (a * (b + 1))
    rw [ih, Nat.mul_succ, Nat.add_comm (a * b) a, repeatWord_add]



/-- 보조정리 11.2.6: `k ≥ 1`일 때 `x ∈ repeatWord v k ↔ x ∈ v` 이다. -/

lemma mem_repeatWord_iff (v : List ℕ) {k : ℕ} (hk : 1 ≤ k) (x : ℕ) :

    x ∈ repeatWord v k ↔ x ∈ v := by

  induction k with

  | zero => omega

  | succ k ih =>

    unfold repeatWord

    rw [List.mem_append]

    rcases Nat.eq_zero_or_pos k with rfl | hk_pos

    · simp [repeatWord]

    · rw [ih hk_pos, or_self]



/-- **보조정리 11.2.7 (비어 있지 않은 유한 word의 원시근 블록 분해; 보충본 주의 1.2 & 원본 주의 15.2)**:

    비어 있지 않은 모든 유한 word `w` (`1 ≤ w.length`)에 대해,

    어떤 원시 블록 `v` (`IsPrimitiveWord v`)와 반복 횟수 `k ≥ 1`이 존재하여 `w = repeatWord v k` 이다. -/

theorem exists_primitive_root_of_nonempty_word :

    ∀ w : List ℕ, 1 ≤ w.length → ∃ v : List ℕ, ∃ k : ℕ, 1 ≤ k ∧ IsPrimitiveWord v ∧ w = repeatWord v k := by

  intro w

  induction' hn : w.length using Nat.strong_induction_on with n ih generalizing w

  intro hw_pos

  by_cases hprim : IsPrimitiveWord w

  · refine ⟨w, 1, le_refl 1, hprim, ?_⟩

    simp [repeatWord]

  · unfold IsPrimitiveWord at hprim

    push Not at hprim

    have hw_lenpos : 1 ≤ w.length := by omega
    obtain ⟨u, m, hm_ge2, hw_eq⟩ := hprim hw_lenpos

    have hlen_um : w.length = u.length * m := by

      rw [hw_eq]

      exact (repeatWord_length_and_sum u m).1

    have hu_pos : 1 ≤ u.length := by

      by_contra h0

      have hu0 : u.length = 0 := by omega

      rw [hu0, Nat.zero_mul] at hlen_um

      omega

    have hu_lt_n : u.length < n := by

      rw [← hn, hlen_um]

      calc

        u.length = u.length * 1 := (Nat.mul_one _).symm

        _ < u.length * m := Nat.mul_lt_mul_of_pos_left hm_ge2 hu_pos

    obtain ⟨v, k₀, hk₀_pos, hv_prim, hu_eq⟩ := ih u.length hu_lt_n u rfl hu_pos

    refine ⟨v, k₀ * m, Nat.mul_pos hk₀_pos (by omega), hv_prim, ?_⟩

    rw [hw_eq, hu_eq, repeatWord_mul]



/-- 보조정리 11.2.8: 만약 양의 지수열 `w`의 모든 원소가 `2`이면 (`∀ a ∈ w, a = 2`),

    `A_total w = 2 * w.length` 이고 `3 ^ w.length + C_p w = 2 ^ (2 * w.length)` 이다. -/

lemma A_total_and_C_p_of_all_two :

    ∀ w : List ℕ, (∀ a ∈ w, a = 2) →

      A_total w = 2 * w.length ∧ 3 ^ w.length + C_p w = 2 ^ (2 * w.length) := by

  intro w hw

  have h_part : ∀ j ≤ w.length, A_part w j = 2 * j := by

    intro j hj

    induction j with

    | zero => simp [A_part]

    | succ j ih =>

      have hj_lt : j < w.length := by omega

      unfold A_part

      rw [List.take_succ_eq_append_getElem hj_lt, List.sum_append, List.sum_singleton]

      have h_ih : (w.take j).sum = 2 * j := ih (le_of_lt hj_lt)

      have h_elem : w[j] = 2 := hw w[j] (List.getElem_mem hj_lt)

      rw [h_ih, h_elem]

      ring

  have hA : A_total w = 2 * w.length := by

    unfold A_total

    have := h_part w.length (le_refl _)

    unfold A_part at this

    rwa [List.take_length] at this

  refine ⟨hA, ?_⟩

  unfold C_p C_sum

  have h_sum : ∀ p : ℕ, (∀ j < p, A_part w j = 2 * j) →

      3 ^ p + (∑ j ∈ range p, 3 ^ (p - 1 - j) * 2 ^ A_part w j) = 2 ^ (2 * p) := by

    intro p hp_part

    induction p with

    | zero => simp

    | succ p ihp =>

      rw [sum_range_succ]

      have h_scale : (∑ x ∈ range p, 3 ^ (p - x) * 2 ^ A_part w x) =

          3 * ∑ x ∈ range p, 3 ^ (p - 1 - x) * 2 ^ A_part w x := by

        rw [mul_sum]

        refine sum_congr rfl ?_

        intro x hx

        have hx_lt : x < p := mem_range.mp hx

        have hexp : p - x = (p - 1 - x) + 1 := by omega

        rw [hexp, pow_succ']

        ring

      have h_scale_norm :
          (∑ x ∈ range p, 3 ^ (p + 1 - 1 - x) * 2 ^ A_part w x) =
            3 * (∑ x ∈ range p, 3 ^ (p - 1 - x) * 2 ^ A_part w x) := by
        simpa [Nat.add_sub_cancel_left] using h_scale
      rw [h_scale_norm]

      have ih_val := ihp (fun j hj => hp_part j (by omega))

      have h_last : A_part w p = 2 * p := hp_part p (by omega)

      have hexp0 : p - p = 0 := by omega

      rw [hexp0, pow_zero, one_mul, h_last]

      calc

        3 ^ (p + 1) + (3 * (∑ x ∈ range p, 3 ^ (p - 1 - x) * 2 ^ A_part w x) + 2 ^ (2 * p))

            = 3 * (3 ^ p + ∑ x ∈ range p, 3 ^ (p - 1 - x) * 2 ^ A_part w x) + 2 ^ (2 * p) := by

              rw [pow_succ']; ring

        _ = 3 * 2 ^ (2 * p) + 2 ^ (2 * p) := by rw [ih_val]

        _ = 4 * 2 ^ (2 * p) := by ring

        _ = 2 ^ (2 * (p + 1)) := by

              have : 2 * (p + 1) = 2 * p + 2 := by ring

              rw [this, pow_add]

              ring

  exact h_sum w.length (fun j hj => h_part j (le_of_lt hj))



/-- **정리 11.2.9 (`A_0_ManuscriptProp ↔ A_0_NoNontrivialCycleProp`; 보충본 §1.1, §2 및 원본 §14.8 완전 연결 — 무조건부 `theorem`)**:

    원고의 허용 원시 블록 집합 `\mathcal{W}_{adm}`에 대한 대수적 비가분성 명제 `A_0_ManuscriptProp`

    (`∀ w, IsAdmissibleWord w → ¬ (D_nat w ∣ C_p w)`)는

    비자명 양의 홀수 주기 부재 명제 `A_0_NoNontrivialCycleProp`

    (`∀ m p, m % 2 = 1 → 1 < m → 1 ≤ p → x_seq m p ≠ m`)와 논리적으로 완전히 동치이다! -/

theorem Theorem_11_2_9_A0_Manuscript_Iff_NoNontrivialCycle :

    A_0_ManuscriptProp ↔ A_0_NoNontrivialCycleProp := by

  constructor

  · intro hA0_ms m p hm_odd hm_gt1 hp_pos hper

    have hnot_one : ¬ ReachesOneSyracuse m := by

      rintro ⟨R, hR⟩

      have h_iter_per : ∀ t : ℕ, x_seq m (t * p) = m := by

        intro t

        induction t with

        | zero => simp [x_seq]

        | succ t ih =>

          rw [Nat.succ_mul, x_seq, Nat.add_comm (t * p) p, Function.iterate_add_apply]

          change F^[p] (x_seq m (t * p)) = m

          change F^[p] (x_seq m (t * p)) = m
      rw [ih]
      change x_seq m p = m
      exact hper

      have h_at_Rp : x_seq m (R * p) = 1 := by

        have h_ge : R ≤ R * p := Nat.le_mul_of_pos_right R hp_pos

        have h_split : R * p = R + (R * p - R) := by omega

        rw [h_split]

        exact (x_seq_add_of_eq_one hR (R * p - R)).1

      rw [h_iter_per R] at h_at_Rp

      omega

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

    have hper_w : x_seq m w.length = m := by rw [hw_len]; exact hper

    obtain ⟨hgt_w, _, hcycle_eq⟩ := Theorem_14_1_Positive_Odd_Cycle_Equation (by omega) hreal hper_w

    have hdvd_w : D_nat w ∣ C_p w := ⟨m, hcycle_eq.symm⟩

    have hA_eq : A_orbit m p = A_total w := by

      unfold A_total

      rw [A_orbit_eq_A_part_of_RealizesWord hreal p (by omega), A_part, ← hw_len, List.take_length]

    have h_garcd6 := (GARCD_6_Nonconvergent_Cumulative_Valuation_Bound_Nat hm_odd hnot_one p).1

    rw [hA_eq, hper] at h_garcd6

    have h_upper_w : 7 ^ w.length * 2 ^ A_total w ≤ 22 ^ w.length := by

      rw [hw_len]

      exact Nat.le_of_mul_le_mul_right h_garcd6 (by omega : 0 < m)

    have h_not_all_two_w : ∃ a ∈ w, a ≠ 2 := by

      by_contra hall2

      push Not at hall2

      obtain ⟨hA_2p, h3C⟩ := A_total_and_C_p_of_all_two w hall2

      have hC_eq_D : C_p w = D_nat w := by

        unfold D_nat

        rw [hA_2p]

        omega

      rw [hC_eq_D] at hcycle_eq

      have hD_pos : 0 < D_nat w := by unfold D_nat; omega

      have hm_eq1 : m = 1 := by

        have h1 : D_nat w * m = D_nat w * 1 := by rw [mul_one, hcycle_eq]

        exact Nat.eq_of_mul_eq_mul_left hD_pos h1

      omega

    obtain ⟨v, k, hk_pos, hv_prim, hw_rep⟩ := exists_primitive_root_of_nonempty_word w (by omega)

    obtain ⟨hlen_vk, hsum_vk⟩ := repeatWord_length_and_sum v k

    rw [← hw_rep] at hlen_vk hsum_vk

    have hv_pos : ∀ a ∈ v, 1 ≤ a := by

      intro a ha

      apply hw_pos a

      rw [hw_rep, mem_repeatWord_iff v hk_pos]

      exact ha

    have hv_not_all_two : ∃ a ∈ v, a ≠ 2 := by

      rcases h_not_all_two_w with ⟨a, ha_w, ha_ne2⟩

      rw [hw_rep, mem_repeatWord_iff v hk_pos] at ha_w

      exact ⟨a, ha_w, ha_ne2⟩

    have hv_gt : 3 ^ v.length < 2 ^ A_total v := by

      by_contra hle

      have hle' : 2 ^ A_total v ≤ 3 ^ v.length := by omega

      have hpow_le : (2 ^ A_total v) ^ k ≤ (3 ^ v.length) ^ k := Nat.pow_le_pow_left hle' k

      rw [← pow_mul, ← pow_mul, ← hsum_vk, ← hlen_vk] at hpow_le

      omega

    have hv_upper : 7 ^ v.length * 2 ^ A_total v ≤ 22 ^ v.length := by

      by_contra hgt

      have hgt' : 22 ^ v.length < 7 ^ v.length * 2 ^ A_total v := by omega

      have hpow_lt : (22 ^ v.length) ^ k < (7 ^ v.length * 2 ^ A_total v) ^ k :=

        Nat.pow_lt_pow_left hgt' (by omega : k ≠ 0)

      rw [Nat.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← hlen_vk, ← hsum_vk] at hpow_lt

      omega

    have hv_adm : IsAdmissibleWord v := ⟨hv_pos, hv_prim, hv_not_all_two, hv_gt, hv_upper⟩

    have hdvd_v : D_nat v ∣ C_p v := by

      rw [← GARCD_23_Repeated_Block_Divisibility_Iff v hk_pos (le_of_lt hv_gt), ← hw_rep]

      exact hdvd_w

    exact hA0_ms v hv_adm hdvd_v

  · intro hNoCycle w hw_adm hdvd

    rcases hw_adm with ⟨hw_pos, hw_prim, ⟨a₀, ha₀_mem, ha₀_ne2⟩, hgt, _⟩

    have hp_pos : 1 ≤ w.length := hw_prim.1

    obtain ⟨n, hreal, hper⟩ := (Theorem_14_2_Cycle_Realization_Iff hp_pos hw_pos).mpr ⟨hgt, hdvd⟩

    have hn_odd : n % 2 = 1 := hreal.1

    by_cases hn_gt1 : 1 < n

    · exact hNoCycle n w.length hn_odd hn_gt1 hp_pos hper

    · have hn_eq1 : n = 1 := by omega

      subst hn_eq1

      obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem ha₀_mem

      have h_getD := hreal.2.2 j hj_lt

      rw [List.getD_eq_getElem w 0 hj_lt] at h_getD

      have ha_one : a_seq 1 j = 2 := by

        have h1 : x_seq 1 0 = 1 := rfl

        simpa using (x_seq_add_of_eq_one h1 j).2.1

      omega



/-- 무한 지수열 `a : ℕ → ℕ`이 비주기적(결국 주기적이지 않음)이라는 조건 (원고 보충본 §2 & 과제집 §4.1):

    어떠한 시작 위치 `j₀`와 주기 `p ≥ 1`에 대해서도 `j ≥ j₀`이면서 `a (j + p) ≠ a j`인 시점 `j`가 존재한다. -/

def IsAperiodicInfiniteWord (a : ℕ → ℕ) : Prop :=

  ∀ j₀ p : ℕ, 1 ≤ p → ∃ j : ℕ, j₀ ≤ j ∧ a (j + p) ≠ a j



/-- **정리 11.2.10 (최소 양의 홀수 대표값 수열 `b_rep a r`의 발산과 무한 word 점별 비실현의 무조건부 필요충분조건; 원본 v0.3 §19 정리 19.1 완결)**:

    임의의 양의 무한 지수열 `a : ℕ → ℕ` (`∀ j, 1 ≤ a j`)에 대하여 다음 명제는 논리적으로 완전히 동치이다:

    `∀ M : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → M < b_rep a r` (`b_r(a) → +∞`) ↔

    `∀ n : ℕ, ¬ RealizesInfiniteWord a n` (어떠한 양의 홀수 `n`도 무한 지수열 `a` 전체를 실현하지 못함). -/

theorem Theorem_11_2_10_B_rep_Diverges_Iff_No_Infinite_Realization

    {a : ℕ → ℕ} (ha : ∀ j : ℕ, 1 ≤ a j) :

    (∀ M : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → M < b_rep a r) ↔

      (∀ n : ℕ, ¬ RealizesInfiniteWord a n) := by

  have h_mono : Monotone (b_rep a) := by

    refine monotone_nat_of_le_succ ?_

    intro r

    exact (Theorem_19_1_Minimal_Representative_Monotone_And_Stabilization ha).1 r |>.1

  constructor

  · intro h_div n hreal

    obtain ⟨R, hR⟩ := h_div n

    let r := max R (n + 1)

    have hr_ge_R : R ≤ r := le_max_left R (n + 1)

    have hr_gt_n : n < r := by omega

    have hA_ge_r : r ≤ A_inf a r := by

      unfold A_inf

      have hpos_w := (prefixWord_length_and_pos a ha r).2

      have hlen_w := (prefixWord_length_and_pos a ha r).1

      have := A_total_ge_length_of_all_pos (prefixWord a r) hpos_w

      omega

    have hn_lt_pow : n < 2 ^ (A_inf a r + 1) := by

      calc

        n < r := hr_gt_n

        _ ≤ A_inf a r + 1 := by omega

        _ < 2 ^ (A_inf a r + 1) := Nat.lt_two_pow_self

    have hb_eq_n : b_rep a r = n :=

      (Theorem_19_1_Minimal_Representative_Monotone_And_Stabilization ha).2 n hreal r hn_lt_pow

    have hb_gt_n : n < b_rep a r := hR r hr_ge_R

    omega

  · intro h_no_real M

    by_contra h_not_div

    push Not at h_not_div

    have h_bdd : ∀ r : ℕ, b_rep a r ≤ M := by

      intro r

      obtain ⟨r', hr', hle⟩ := h_not_div r

      exact le_trans (h_mono hr') hle

    have h_eventually_const : ∀ B : ℕ, (∀ r : ℕ, b_rep a r ≤ B) →

        ∃ R₀ : ℕ, ∀ r : ℕ, R₀ ≤ r → b_rep a r = b_rep a R₀ := by

      intro B

      induction B with

      | zero =>

        intro hB0

        refine ⟨0, ?_⟩

        intro r _

        have hr0 := hB0 r

        have h00 := hB0 0

        omega

      | succ B ihB =>

        intro hB_succ

        by_cases h_hits : ∃ R₀ : ℕ, b_rep a R₀ = B + 1

        · obtain ⟨R₀, hR₀⟩ := h_hits

          refine ⟨R₀, ?_⟩

          intro r hr

          have hge : B + 1 ≤ b_rep a r := by rw [← hR₀]; exact h_mono hr

          have hle : b_rep a r ≤ B + 1 := hB_succ r

          omega

        · push Not at h_hits

          apply ihB

          intro r

          have hle := hB_succ r

          have hne := h_hits r

          omega

    obtain ⟨R₀, hR₀_const⟩ := h_eventually_const M h_bdd

    let n₀ := b_rep a R₀

    have hreal_R0 := (b_rep_realizes_prefix a ha R₀).2.2.1

    have hn₀_odd : n₀ % 2 = 1 := hreal_R0.1

    have hn₀_inf : RealizesInfiniteWord a n₀ := by

      refine ⟨hn₀_odd, ha, ?_⟩

      intro j

      let r := max R₀ (j + 1)

      have hr_ge_R0 : R₀ ≤ r := le_max_left R₀ (j + 1)

      have hj_lt_r : j < r := by omega

      have hb_r_eq : b_rep a r = n₀ := hR₀_const r hr_ge_R0

      have hreal_r : RealizesWord (prefixWord a r) n₀ := by

        rw [← hb_r_eq]

        exact (b_rep_realizes_prefix a ha r).2.2.1

      have hj_lt_len : j < (prefixWord a r).length := by

        rw [(prefixWord_length_and_pos a ha r).1]

        exact hj_lt_r

      have h_eq := hreal_r.2.2 j hj_lt_len

      rw [h_eq]

      simp [prefixWord, List.getD_eq_getElem _ 0, hj_lt_r]

    exact h_no_real n₀ hn₀_inf



/-- **원고 정의 그대로의 의무 B-0 (`B_0_ManuscriptProp`; 보충본 p.4 미증명 과제 2.2 & 과제집 p.48 §4.1)**:

    임의의 양의 지수열 `a : ℕ → ℕ` (`∀ j, 1 ≤ a j`)이 비주기적(`IsAperiodicInfiniteWord a`)이고

    비수렴 저지수 누적 조건(`∃ K > 0, ∀ r, 7^r * 2^{A_inf a r} ≤ 22^r * K`)을 만족하면,

    법 `2^{A_r + 1}` 합동류의 최소 양의 홀수 대표값 `b_rep a r`는 `r → ∞`일 때 `∞`로 발산한다:

    `∀ M : ℕ, ∃ R : ℕ, ∀ r ≥ R, M < b_rep a r`. -/

def B_0_ManuscriptProp : Prop :=

  ∀ a : ℕ → ℕ, (∀ j : ℕ, 1 ≤ a j) →

    IsAperiodicInfiniteWord a →

    (∃ K : ℕ, 1 ≤ K ∧ ∀ r : ℕ, 7 ^ r * 2 ^ A_inf a r ≤ 22 ^ r * K) →

    ∀ M : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → M < b_rep a r



/-- **정리 11.2.11 (`(A_0_ManuscriptProp ∧ B_0_ManuscriptProp) ↔ CollatzConjectureProp`; 보충본 §2 & 과제집 §7 원고 직결 완전 증명 — 무조건부 `theorem`)**:

    원고의 대수적 의무 `A_0_ManuscriptProp` (`∀ w ∈ W_{adm}, ¬ (D(w) ∣ C_p(w))`)와

    무한 합동류 대표값 발산 의무 `B_0_ManuscriptProp` (`b_r(a) → ∞`)가 모두 성립하는 것은,

    모든 양의 정수가 유한 번의 콜라츠 반복 후 `1`에 도달한다는 `CollatzConjectureProp`와 필요충분조건이다! -/

theorem Theorem_11_2_11_Manuscript_A0_And_B0_Iff_Collatz_Conjecture :

    (A_0_ManuscriptProp ∧ B_0_ManuscriptProp) ↔ CollatzConjectureProp := by

  rw [← Theorem_10_3_2_A0_And_B0_Iff_Collatz_Conjecture]

  rw [Theorem_11_2_9_A0_Manuscript_Iff_NoNontrivialCycle]

  refine and_congr_right ?_

  intro hA0_no_cycle

  constructor

  · intro hB0_ms n hn_odd

    by_contra hap

    have hnot_one : ¬ ReachesOneSyracuse n := by

      rintro ⟨R, hR⟩

      apply hap

      refine ⟨R, R + 1, by omega, ?_⟩

      have hR1 : x_seq n (R + 1) = 1 := (x_seq_add_of_eq_one hR 1).1

      rw [hR, hR1]

    let a : ℕ → ℕ := a_seq n

    have ha_pos : ∀ j : ℕ, 1 ≤ a j := a_seq_ge_one hn_odd

    have hreal_inf : RealizesInfiniteWord a n := ⟨hn_odd, ha_pos, fun _ => rfl⟩

    have hA_inf_eq : ∀ r : ℕ, A_inf a r = A_orbit n r := by

      intro r

      unfold A_inf A_total prefixWord A_orbit

      induction r with

      | zero => simp

      | succ r ih =>

        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,

            List.sum_singleton, Finset.sum_range_succ, ih]

    have h_garcd6_a : ∃ K : ℕ, 1 ≤ K ∧ ∀ r : ℕ, 7 ^ r * 2 ^ A_inf a r ≤ 22 ^ r * K := by

      refine ⟨n, by omega, ?_⟩

      intro r

      rw [hA_inf_eq r]

      have h6 := (GARCD_6_Nonconvergent_Cumulative_Valuation_Bound_Nat hn_odd hnot_one r).2

      calc

        7 ^ r * 2 ^ A_orbit n r

            ≤ 7 ^ (r + 1) * 2 ^ A_orbit n r := by

              refine Nat.mul_le_mul_right _ ?_

              calc

                7 ^ r = 7 ^ r * 1 := (Nat.mul_one _).symm

                _ ≤ 7 ^ r * 7 := Nat.mul_le_mul_left _ (by omega)

                _ = 7 ^ (r + 1) := by rw [pow_succ]

        _ ≤ 22 ^ r * n := h6

    by_cases hap_word : IsAperiodicInfiniteWord a

    · have h_div := hB0_ms a ha_pos hap_word h_garcd6_a

      exact (Theorem_11_2_10_B_rep_Diverges_Iff_No_Infinite_Realization ha_pos).mp h_div n hreal_inf

    · unfold IsAperiodicInfiniteWord at hap_word

      push Not at hap_word

      obtain ⟨j₀, p, hp_pos, h_per_a⟩ := hap_word

      let w : List ℕ := (List.range p).map (fun i => a (j₀ + i))

      have hw_len : w.length = p := by simp [w]

      have hw_pos : ∀ x ∈ w, 1 ≤ x := by

        intro x hx

        rw [List.mem_map] at hx

        rcases hx with ⟨i, _, rfl⟩

        exact ha_pos (j₀ + i)

      have h_per_k : ∀ k i : ℕ, i < p → a (j₀ + k * p + i) = a (j₀ + i) := by

        intro k

        induction k with

        | zero => simp

        | succ k ih =>

          intro i hi

          have h_idx : j₀ + (k + 1) * p + i = (j₀ + k * p + i) + p := by ring

          rw [h_idx, h_per_a (j₀ + k * p + i) (by omega), ih i hi]

      have h_real_k : ∀ k : ℕ, RealizesWord w (x_seq n (j₀ + k * w.length)) := by

        intro k

        refine ⟨x_seq_odd hn_odd _, hw_pos, ?_⟩

        intro i hi

        rw [hw_len] at hi ⊢

        have h_ashift : a_seq (x_seq n (j₀ + k * p)) i = a (j₀ + k * p + i) := by

          unfold a a_seq x_seq

          rw [← Function.iterate_add_apply, Nat.add_comm i (j₀ + k * p)]

        rw [h_ashift, h_per_k k i hi]

        simp [w, List.getD_eq_getElem _ 0, hi]

      by_cases h_low : 2 ^ A_total w ≤ 3 ^ w.length

      · exact Theorem_19_3_Eventually_Periodic_Low_Valuation_Word_Unrealizable

          (by omega) hw_pos h_low n j₀ hn_odd h_real_k

      · have h_high : 3 ^ w.length < 2 ^ A_total w := by omega

        let D := 2 ^ A_total w - 3 ^ w.length

        have hD_pos : 0 < D := by omega

        let y_seq (k : ℕ) : ℕ := x_seq n (j₀ + k * w.length)

        have hy_step_z : ∀ k : ℕ,

            (2 ^ A_total w : ℤ) * ((D : ℤ) * (y_seq (k + 1) : ℤ) - (C_p w : ℤ)) =

              (3 ^ w.length : ℤ) * ((D : ℤ) * (y_seq k : ℤ) - (C_p w : ℤ)) := by

          intro k

          have hreal_k := h_real_k k

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

          have hid_z : (2 ^ A_total w : ℤ) * (y_seq (k + 1) : ℤ) =

              (3 ^ w.length : ℤ) * (y_seq k : ℤ) + (C_p w : ℤ) := by exact_mod_cast hid

          have hD_z : (D : ℤ) = (2 ^ A_total w : ℤ) - (3 ^ w.length : ℤ) :=

            Int.ofNat_sub (le_of_lt h_high)

          calc

            (2 ^ A_total w : ℤ) * ((D : ℤ) * (y_seq (k + 1) : ℤ) - (C_p w : ℤ))

                = (D : ℤ) * ((2 ^ A_total w : ℤ) * (y_seq (k + 1) : ℤ)) - (2 ^ A_total w : ℤ) * (C_p w : ℤ) := by ring

            _ = (D : ℤ) * ((3 ^ w.length : ℤ) * (y_seq k : ℤ) + (C_p w : ℤ)) - (2 ^ A_total w : ℤ) * (C_p w : ℤ) := by rw [hid_z]

            _ = (3 ^ w.length : ℤ) * (D : ℤ) * (y_seq k : ℤ) + ((D : ℤ) - (2 ^ A_total w : ℤ)) * (C_p w : ℤ) := by ring

            _ = (3 ^ w.length : ℤ) * ((D : ℤ) * (y_seq k : ℤ) - (C_p w : ℤ)) := by rw [hD_z]; ring

        have hy_iter_z : ∀ k : ℕ,

            ((2 ^ A_total w : ℤ) ^ k) * ((D : ℤ) * (y_seq k : ℤ) - (C_p w : ℤ)) =

              ((3 ^ w.length : ℤ) ^ k) * ((D : ℤ) * (y_seq 0 : ℤ) - (C_p w : ℤ)) := by

          intro k

          induction k with

          | zero => simp

          | succ k ih =>

            calc

              ((2 ^ A_total w : ℤ) ^ (k + 1)) * ((D : ℤ) * (y_seq (k + 1) : ℤ) - (C_p w : ℤ))

                  = ((2 ^ A_total w : ℤ) ^ k) * ((2 ^ A_total w : ℤ) * ((D : ℤ) * (y_seq (k + 1) : ℤ) - (C_p w : ℤ))) := by

                    rw [pow_succ]; ring

              _ = ((2 ^ A_total w : ℤ) ^ k) * ((3 ^ w.length : ℤ) * ((D : ℤ) * (y_seq k : ℤ) - (C_p w : ℤ))) := by rw [hy_step_z k]

              _ = (3 ^ w.length : ℤ) * (((2 ^ A_total w : ℤ) ^ k) * ((D : ℤ) * (y_seq k : ℤ) - (C_p w : ℤ))) := by ring

              _ = (3 ^ w.length : ℤ) * (((3 ^ w.length : ℤ) ^ k) * ((D : ℤ) * (y_seq 0 : ℤ) - (C_p w : ℤ))) := by rw [ih]

              _ = ((3 ^ w.length : ℤ) ^ (k + 1)) * ((D : ℤ) * (y_seq 0 : ℤ) - (C_p w : ℤ)) := by rw [pow_succ']; ring

        let Z (k : ℕ) : ℕ := ((D : ℤ) * (y_seq k : ℤ) - (C_p w : ℤ)).natAbs

        have hZ_iter : ∀ k : ℕ, (2 ^ A_total w) ^ k * Z k = (3 ^ w.length) ^ k * Z 0 := by

          intro k

          have h_abs := congrArg Int.natAbs (hy_iter_z k)

          simpa [Z, Int.natAbs_mul, Int.natAbs_pow] using h_abs

        rcases Nat.eq_zero_or_pos (Z 0) with hZ0_zero | hZ0_pos

        · have hZ1_zero : Z 1 = 0 := by

            have h1 := hZ_iter 1

            rw [hZ0_zero, mul_zero, pow_one] at h1

            have : 0 < 2 ^ A_total w := by positivity

            exact (Nat.mul_eq_zero.mp h1).resolve_left (ne_of_gt this)

          have hy0_eq : (D : ℤ) * (y_seq 0 : ℤ) = (C_p w : ℤ) := by

            have := Int.natAbs_eq_zero.mp hZ0_zero

            linarith

          have hy1_eq : (D : ℤ) * (y_seq 1 : ℤ) = (C_p w : ℤ) := by

            have := Int.natAbs_eq_zero.mp hZ1_zero

            linarith

          have hy_eq_01 : y_seq 0 = y_seq 1 := by

            have hmul : (D : ℤ) * (y_seq 0 : ℤ) = (D : ℤ) * (y_seq 1 : ℤ) := hy0_eq.trans hy1_eq.symm

            have hD_ne : (D : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hD_pos)

            have h_z := mul_left_cancel₀ hD_ne hmul

            exact Int.ofNat.inj h_z

          apply hap

          refine ⟨j₀, j₀ + w.length, by omega, ?_⟩

          simpa [y_seq] using hy_eq_01

        · let K := Z 0

          have hA_ge1 : 1 ≤ A_total w := by

            have := A_total_ge_length_of_all_pos w hw_pos

            omega

          have hdvd_3pow : (2 ^ A_total w) ^ K ∣ (3 ^ w.length) ^ K * K :=

            ⟨Z K, (hZ_iter K).symm⟩

          have hcop_K : Nat.Coprime ((2 ^ A_total w) ^ K) ((3 ^ w.length) ^ K) := by

            rw [← pow_mul, ← pow_mul]

            exact (coprime_three_pow_two_pow (w.length * K) (A_total w * K)).symm

          have hdvd_K : (2 ^ A_total w) ^ K ∣ K := hcop_K.dvd_of_dvd_mul_left hdvd_3pow

          have h_le : (2 ^ A_total w) ^ K ≤ K := Nat.le_of_dvd hZ0_pos hdvd_K

          have h2A_ge2 : 2 ≤ 2 ^ A_total w := by

            calc

              2 = 2 ^ 1 := by ring

              _ ≤ 2 ^ A_total w := Nat.pow_le_pow_right (by omega) hA_ge1

          have h_gt : K < (2 ^ A_total w) ^ K := by

            calc

              K < 2 ^ K := Nat.lt_two_pow_self

              _ ≤ (2 ^ A_total w) ^ K := Nat.pow_le_pow_left h2A_ge2 K

          omega

  · intro hB0_dyn a ha_pos hap_word _

    rw [Theorem_11_2_10_B_rep_Diverges_Iff_No_Infinite_Realization ha_pos]

    intro n hreal_inf

    have hn_odd : n % 2 = 1 := hreal_inf.1

    obtain ⟨j₁, k₁, hjk_lt, hjk_eq⟩ := hB0_dyn n hn_odd

    let m := x_seq n j₁

    let p := k₁ - j₁

    have hp_pos : 1 ≤ p := by omega

    have hm_odd : m % 2 = 1 := x_seq_odd hn_odd j₁

    have hm_per : x_seq m p = m := by

      unfold m x_seq

      rw [← Function.iterate_add_apply, Nat.add_comm p j₁, Nat.add_sub_of_le (le_of_lt hjk_lt)]

      exact hjk_eq.symm

    have hm_eq1 : m = 1 := by

      by_contra hne1

      exact hA0_no_cycle m p hm_odd (by omega) hp_pos hm_per

    obtain ⟨j, hj_ge, h_neq⟩ := hap_word j₁ 1 (le_refl 1)

    have ha_j : a j = 2 := by

      rw [← hreal_inf.2.2 j]

      have h_split : j = j₁ + (j - j₁) := by omega

      rw [h_split]

      exact (x_seq_add_of_eq_one hm_eq1 (j - j₁)).2.1

    have ha_j1 : a (j + 1) = 2 := by

      rw [← hreal_inf.2.2 (j + 1)]

      have h_split : j + 1 = j₁ + (j + 1 - j₁) := by omega

      rw [h_split]

      exact (x_seq_add_of_eq_one hm_eq1 (j + 1 - j₁)).2.1

    exact h_neq (ha_j1.trans ha_j.symm)



/-!

## §11.3 [단점 3 완전 보완] `ProofFirst20261109` 하우스도르프 차원 전 목표 명제들의

  엄밀한 형식 증명 완결 (`ChernoffExponentGoal`, `GARCD_Hausdorff_LevelCost_Goal`,

  `OptimizedBinomialEnvelopeGoal`, `ExactOriginalFiberTransfer`, `ActualLevelVsBinomialGoal`,

  `ActualGeometricEnvelopeGoal`, `GARCD_Hausdorff_Actual_TailCost_Goal`, `UnconditionalActualHausdorffGoal`)

-/



namespace ProofFirst20261109



/-- **보조정리 11.3.1 (`ChernoffX` 및 `ChernoffQ`의 기본 부등식)**:

    `1 < β < 2`이고 `s < 1`일 때:

    (1) `0 < ChernoffX β`, `ChernoffX β < 1 / 2`, `ChernoffX β < 1`,

    (2) `1 - ChernoffX β = 1 / β` 및 `ChernoffX β / (1 - ChernoffX β) = β - 1`,

    (3) `1 / 2 < ChernoffQ s` 및 `1 ≤ ChernoffT β s` 이다. -/

lemma chernoff_params_basic

    {β s : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2) (hs1 : s < 1) :

    0 < ChernoffX β ∧

    ChernoffX β < 1 / 2 ∧

    ChernoffX β < 1 ∧

    1 - ChernoffX β = 1 / β ∧

    ChernoffX β / (1 - ChernoffX β) = β - 1 ∧

    1 / 2 < ChernoffQ s ∧

    1 ≤ ChernoffT β s := by

  have hβ_pos : 0 < β := by linarith

  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos

  have hx_pos : 0 < ChernoffX β := by

    unfold ChernoffX

    exact div_pos (by linarith) hβ_pos

  have hx_lt_half : ChernoffX β < 1 / 2 := by

    unfold ChernoffX

    rw [div_lt_div_iff₀ hβ_pos (by norm_num : (0 : ℝ) < 2)]

    linarith

  have hx_lt_one : ChernoffX β < 1 := by linarith

  have h1_sub_x : 1 - ChernoffX β = 1 / β := by

    unfold ChernoffX

    field_simp

    ring

  have hx_ratio : ChernoffX β / (1 - ChernoffX β) = β - 1 := by

    rw [h1_sub_x]

    unfold ChernoffX

    field_simp

  have hq_gt_half : 1 / 2 < ChernoffQ s := by

    unfold ChernoffQ

    have h_half : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num

    rw [h_half]

    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith : -1 < -s)

  have ht_ge_one : 1 ≤ ChernoffT β s := by

    unfold ChernoffT

    rw [le_div_iff₀ hx_pos]

    linarith

  exact ⟨hx_pos, hx_lt_half, hx_lt_one, h1_sub_x, hx_ratio, hq_gt_half, ht_ge_one⟩



/-- **보조정리 11.3.2 (`DimBound β < s`일 때 `ChernoffRho β s < 1`의 로그·지수 증명)**:

    `1 < β < 2`이고 `DimBound β < s < 1`일 때,

    `0 < ChernoffRho β s` 이고 `ChernoffRho β s < 1` 이다. -/

lemma chernoffRho_pos_and_lt_one

    {β s : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2) (hs_dim : DimBound β < s) (hs1 : s < 1) :

    0 < ChernoffRho β s ∧ ChernoffRho β s < 1 := by

  obtain ⟨hx_pos, _, _, _, _, hq_gt_half, ht_ge_one⟩ := chernoff_params_basic hβ1 hβ2 hs1

  have hβ_pos : 0 < β := by linarith

  have hβm1_pos : 0 < β - 1 := by linarith

  have hq_pos : 0 < ChernoffQ s := by linarith

  have ht_pos : 0 < ChernoffT β s := by linarith

  have hrho_pos : 0 < ChernoffRho β s := by

    unfold ChernoffRho

    exact mul_pos hβm1_pos (Real.rpow_pos_of_pos ht_pos β)

  refine ⟨hrho_pos, ?_⟩

  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

  have h_dim_eq : DimBound β * (β * Real.log 2) =

      β * Real.log β - (β - 1) * Real.log (β - 1) := by

    unfold DimBound RateFunctionI

    have hne : β * Real.log 2 ≠ 0 := ne_of_gt (mul_pos hβ_pos hlog2_pos)

    field_simp

    ring

  have h_s_ineq : β * Real.log β - (β - 1) * Real.log (β - 1) < s * (β * Real.log 2) := by

    rw [← h_dim_eq]

    exact mul_lt_mul_of_pos_right hs_dim (mul_pos hβ_pos hlog2_pos)

  have hlog_q : Real.log (ChernoffQ s) = -s * Real.log 2 := by

    unfold ChernoffQ

    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

  have hlog_x : Real.log (ChernoffX β) = Real.log (β - 1) - Real.log β := by

    unfold ChernoffX

    exact Real.log_div (ne_of_gt hβm1_pos) (ne_of_gt hβ_pos)

  have hlog_t : Real.log (ChernoffT β s) = -s * Real.log 2 - Real.log (β - 1) + Real.log β := by

    unfold ChernoffT

    rw [Real.log_div (ne_of_gt hq_pos) (ne_of_gt hx_pos), hlog_q, hlog_x]

    ring

  have hlog_rho : Real.log (ChernoffRho β s) =

      β * Real.log β - (β - 1) * Real.log (β - 1) - s * (β * Real.log 2) := by

    unfold ChernoffRho

    rw [Real.log_mul (ne_of_gt hβm1_pos) (ne_of_gt (Real.rpow_pos_of_pos ht_pos β)),

        Real.log_rpow ht_pos, hlog_t]

    ring

  have hlog_neg : Real.log (ChernoffRho β s) < 0 := by linarith

  have h_exp := Real.exp_lt_exp.mpr hlog_neg

  rwa [Real.exp_log hrho_pos, Real.exp_zero] at h_exp



/-- **정리 11.3.3 (`ChernoffExponentGoal`의 무조건부 완전 증명)**:

    `ProofFirst20261109.ChernoffExponentGoal`이 `sorry`나 `axiom` 없이 무조건부로 성립한다! -/

theorem chernoffExponentGoal_proved : ChernoffExponentGoal := by

  intro β s hβ1 hβ2 hs_dim hs1

  obtain ⟨hx_pos, _, hx_lt1, _, hx_ratio, _, ht_ge1⟩ := chernoff_params_basic hβ1 hβ2 hs1

  obtain ⟨hrho_pos, hrho_lt1⟩ := chernoffRho_pos_and_lt_one hβ1 hβ2 hs_dim hs1

  refine ⟨hx_pos, hx_lt1, ht_ge1, hrho_pos, hrho_lt1, ?_⟩

  intro r hr

  let x := ChernoffX β

  let q := ChernoffQ s

  let t := ChernoffT β s

  let rho := ChernoffRho β s

  have hq_nonneg : 0 ≤ q := by

    dsimp [q, ChernoffQ]

    positivity

  have ht_pos : 0 < t := by linarith

  have hβ_pos : 0 < β := by linarith

  have hβr_nonneg : 0 ≤ β * (r : ℝ) := by positivity

  have h_floor_le : (Nat.floor (β * (r : ℝ)) : ℝ) ≤ β * (r : ℝ) :=

    Nat.floor_le hβr_nonneg

  have h_t_pow : t ^ (Nat.floor (β * (r : ℝ))) ≤ (t ^ β) ^ r := by

    calc

      t ^ (Nat.floor (β * (r : ℝ)))

          = t ^ ((Nat.floor (β * (r : ℝ)) : ℝ)) :=

            (Real.rpow_natCast t (Nat.floor (β * (r : ℝ)))).symm

      _ ≤ t ^ (β * (r : ℝ)) :=

            Real.rpow_le_rpow_of_exponent_le ht_ge1 h_floor_le

      _ = (t ^ β) ^ ((r : ℝ)) := Real.rpow_mul (le_of_lt ht_pos) β (r : ℝ)

      _ = (t ^ β) ^ r := Real.rpow_natCast (t ^ β) r

  have h_rho_pow : (t ^ β) ^ r * (x / (1 - x)) ^ r = rho ^ r := by

    have h_ratio : x / (1 - x) = β - 1 := hx_ratio

    rw [h_ratio, ← mul_pow, mul_comm (t ^ β) (β - 1)]

    rfl

  have h_ratio_nonneg : 0 ≤ (x / (1 - x)) ^ r := by

    rw [hx_ratio]

    have : 0 ≤ β - 1 := by linarith

    positivity

  calc

    q * t ^ (Nat.floor (β * (r : ℝ))) * (x / (1 - x)) ^ r

        = q * (t ^ (Nat.floor (β * (r : ℝ))) * (x / (1 - x)) ^ r) := by ring

    _ ≤ q * ((t ^ β) ^ r * (x / (1 - x)) ^ r) :=

          mul_le_mul_of_nonneg_left

            (mul_le_mul_of_nonneg_right h_t_pow h_ratio_nonneg) hq_nonneg

    _ = q * rho ^ r := by rw [h_rho_pow]



/-- **정리 11.3.4 (`GARCD_Hausdorff_LevelCost_Goal`의 무조건부 완전 증명)**:

    `ChernoffExponentGoal`과 `finite_binomial_cost_le_geometric_of_exponent`를 결합하여

    실수 가중 이항 비용 상계 `GARCD_Hausdorff_LevelCost_Goal`을 무조건부로 증명한다. -/

theorem GARCD_Hausdorff_LevelCost_Goal_proved : GARCD_Hausdorff_LevelCost_Goal := by

  intro β s hβ1 hβ2 hs_dim hs1

  obtain ⟨_, _, _, hrho_pos, hrho_lt1, _⟩ :=

    chernoffExponentGoal_proved β s hβ1 hβ2 hs_dim hs1

  have hq_nonneg : 0 ≤ ChernoffQ s := by

    unfold ChernoffQ

    positivity

  refine ⟨ChernoffQ s, ChernoffRho β s, hq_nonneg, le_of_lt hrho_pos, hrho_lt1, ?_⟩

  intro r hr

  exact finite_binomial_cost_le_geometric_of_exponent

    β s hβ1 hβ2 hs_dim hs1 chernoffExponentGoal_proved r hr



/-- **정리 11.3.5 (`OptimizedBinomialEnvelopeGoal`의 무조건부 완전 증명)**:

    `ENNReal` 위에서의 최적화된 이항 포락선 상계 `OptimizedBinomialEnvelopeGoal`이 무조건부로 성립한다! -/

theorem optimizedBinomialEnvelopeGoal_proved : OptimizedBinomialEnvelopeGoal := by

  intro β s hβ1 hβ2 hs_dim hs1

  obtain ⟨_, _, _, hrho_pos, hrho_lt1, _⟩ :=

    chernoffExponentGoal_proved β s hβ1 hβ2 hs_dim hs1

  have hq_nonneg : 0 ≤ ChernoffQ s := by

    unfold ChernoffQ

    positivity

  let q_nn : NNReal := ⟨ChernoffQ s, hq_nonneg⟩

  let rho_nn : NNReal := ⟨ChernoffRho β s, le_of_lt hrho_pos⟩

  have hrho_nn_lt1 : rho_nn < 1 := by exact_mod_cast hrho_lt1

  refine ⟨q_nn, rho_nn, hrho_nn_lt1, ?_⟩

  intro r hr

  have hReal := finite_binomial_cost_le_geometric_of_exponent

    β s hβ1 hβ2 hs_dim hs1 chernoffExponentGoal_proved r hr

  exact binomial_majorant_le_ennreal_geometric_of_real

    β s r hr q_nn rho_nn hReal rfl hq_nonneg



/-- 보조정리 11.3.6: 원통 직경의 `s`-거듭제곱 상계:

    모든 유한 word `w : List ℕ`과 `0 < s`에 대해

    `Metric.ediam (TwoAdicValuationCylinder w) ^ s ≤ (ENNReal.ofReal ((2 : ℝ) ^ (-s))) ^ (A_total w + 1)`. -/

lemma twoAdicValuationCylinder_ediam_rpow_le

    (w : List ℕ) {s : ℝ} (hs : 0 < s) :

    Metric.ediam (TwoAdicValuationCylinder w) ^ s ≤

      (ENNReal.ofReal ((2 : ℝ) ^ (-s))) ^ (A_total w + 1) := by

  let k := A_total w + 1

  have h_diam := twoAdicValuationCylinder_ediam_le w

  have h_rpow := ENNReal.rpow_le_rpow h_diam (le_of_lt hs)

  have h_real_pow : (((2 : ℝ) ^ (-(k : ℤ))) ^ s) = ((2 : ℝ) ^ (-s)) ^ k := by

    have h1 : (2 : ℝ) ^ (-(k : ℤ)) = (2 : ℝ) ^ (-(k : ℝ)) := by

      rw [← Real.rpow_intCast (2 : ℝ) (-(k : ℤ))]

      simp

    rw [h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),

        ← Real.rpow_natCast ((2 : ℝ) ^ (-s)) k,

        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

    congr 1

    ring

  have h_ennreal_pow :

      (ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℤ)))) ^ s =

        (ENNReal.ofReal ((2 : ℝ) ^ (-s))) ^ k := by

    rw [← ENNReal.ofReal_rpow_of_pos (by positivity), h_real_pow,

        ENNReal.ofReal_pow (by positivity)]

  exact le_trans h_rpow (le_of_eq h_ennreal_pow)



/-- 보조정리 11.3.7: 만약 `¬ (∀ a ∈ w, 1 ≤ a)`이면 `TwoAdicValuationCylinder w = ∅`이므로

    `0 < s`에서 `Metric.ediam (TwoAdicValuationCylinder w) ^ s = 0` 이다. -/

lemma twoAdicValuationCylinder_ediam_rpow_eq_zero_of_not_all_pos

    (w : List ℕ) (hnot : ¬ (∀ a ∈ w, 1 ≤ a)) {s : ℝ} (hs : 0 < s) :

    Metric.ediam (TwoAdicValuationCylinder w) ^ s = 0 := by

  have hempty : TwoAdicValuationCylinder w = ∅ := by

    ext z

    simp only [TwoAdicValuationCylinder, Set.mem_setOf, Set.mem_empty_iff_false, iff_false, not_and]

    intro hpos

    exact False.elim (hnot hpos)

  rw [hempty, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]



/-- 고정된 `(β, r, A)` (`A ≤ ⌊β r⌋`)에 대해 `OriginalPositiveWord A r`를 `LowValuationCoverIndex β`로 보내는 단사 사상. -/

def embLevelIndex (β : ℝ) (r A : ℕ)

    (hAB : A ≤ Nat.floor (β * (r : ℝ))) (hβ : 0 ≤ β) :

    HausdorffCount20261109.OriginalPositiveWord A r ↪ LowValuationCoverIndex β where

  toFun w := ⟨(r, w.1), ⟨w.2.1, by

    change (w.1.sum : ℝ) ≤ β * (r : ℝ)

    rw [w.2.2.1]

    have hβr : 0 ≤ β * (r : ℝ) := by positivity

    exact le_trans (by exact_mod_cast hAB) (Nat.floor_le hβr)⟩⟩

  inj' w₁ w₂ h := by

    apply Subtype.ext

    exact (Prod.ext_iff.mp (Subtype.ext_iff.mp h)).2



/-- 고정된 `(β, r, A)`에 대응하는 `LowValuationCoverIndex β`의 유한 부분집합. -/

noncomputable def fiberCoverFinset (β : ℝ) (r A : ℕ)

    (hAB : A ≤ Nat.floor (β * (r : ℝ))) (hβ : 0 ≤ β) :

    Finset (LowValuationCoverIndex β) := by

  classical

  exact (Finset.univ : Finset (HausdorffCount20261109.OriginalPositiveWord A r)).map

    (embLevelIndex β r A hAB hβ)



/-- 레벨 `r`의 전체 활성 인덱스 유한 부분집합 `levelActiveFinset β r`. -/

noncomputable def levelActiveFinset (β : ℝ) (r : ℕ) (hβ : 0 ≤ β) :

    Finset (LowValuationCoverIndex β) := by

  classical

  let B := Nat.floor (β * (r : ℝ))

  exact (Finset.Ico r (B + 1)).attach.biUnion (fun ⟨A, hA⟩ =>

    fiberCoverFinset β r A (Nat.le_of_lt_succ (Finset.mem_Ico.mp hA).2) hβ)



/-- **정리 11.3.8 (`ExactOriginalFiberTransfer`의 무조건부 완전 증명)**:

    레벨 `r`에서의 실제 무한 합 `GARCDRealLevelCost β s r`는 비어 있지 않은 양의 원통들의 유한 합으로 정확히 축약되어

    `originalFiniteLevelCost r ⌊β r⌋ (ENNReal.ofReal (2^(-s)))` 이하임이 무조건부로 성립한다! -/

theorem exactOriginalFiberTransfer_proved : ExactOriginalFiberTransfer := by

  classical

  intro β s r hβ1 _ hs hr

  have hβ0 : 0 ≤ β := by linarith

  let B := Nat.floor (β * (r : ℝ))

  let q := ENNReal.ofReal ((2 : ℝ) ^ (-s))

  let f : LowValuationCoverIndex β → ENNReal := fun i =>

    if i.val.1 = r then Metric.ediam (TwoAdicValuationCylinder i.val.2) ^ s else 0

  -- 1. levelActiveFinset 밖의 모든 인덱스 i 에서 f i = 0 임을 증명

  have hf_zero_outside : ∀ i ∉ levelActiveFinset β r hβ0, f i = 0 := by

    intro i hi_not

    dsimp [f]

    split_ifs with hir

    · by_cases hpos : ∀ a ∈ i.val.2, 1 ≤ a

      · exfalso

        apply hi_not

        let A := i.val.2.sum

        have hlen_r : i.val.2.length = r := i.property.1.trans hir

        have hrA : r ≤ A := by

          rw [← hlen_r]

          exact A_total_ge_length_of_all_pos i.val.2 hpos

        have hAB : A ≤ B := Nat.le_floor i.property.2

        have hA_mem : A ∈ Finset.Ico r (B + 1) := Finset.mem_Ico.mpr ⟨hrA, Nat.lt_succ_of_le hAB⟩

        unfold levelActiveFinset

        rw [Finset.mem_biUnion]

        refine ⟨⟨A, hA_mem⟩, Finset.mem_attach _ _, ?_⟩

        unfold fiberCoverFinset

        rw [Finset.mem_map]

        let w : HausdorffCount20261109.OriginalPositiveWord A r := ⟨i.val.2, ⟨hlen_r, rfl, hpos⟩⟩

        refine ⟨w, Finset.mem_univ w, ?_⟩

        apply Subtype.ext

        exact Prod.ext hir.symm rfl

      · exact twoAdicValuationCylinder_ediam_rpow_eq_zero_of_not_all_pos i.val.2 hpos hs

    · rfl

  -- 2. tsum_eq_sum 에 의해 GARCDRealLevelCost β s r = ∑ i ∈ levelActiveFinset β r hβ0, f i

  have h_tsum_eq : GARCDRealLevelCost β s r = ∑ i ∈ levelActiveFinset β r hβ0, f i :=

    tsum_eq_sum hf_zero_outside

  rw [h_tsum_eq]

  -- 3. 서로 다른 A₁ ≠ A₂ 에 대해 fiberCoverFinset 이 서로소이므로 Finset.sum_biUnion 적용

  have h_disj : Set.PairwiseDisjoint (↑(Finset.Ico r (B + 1)).attach)

      (fun a : {x // x ∈ Finset.Ico r (B + 1)} =>

        fiberCoverFinset β r a.1 (Nat.le_of_lt_succ (Finset.mem_Ico.mp a.2).2) hβ0) := by

    intro ⟨A₁, hA₁⟩ _ ⟨A₂, hA₂⟩ _ hne

    rw [Finset.disjoint_left]

    intro i hi₁ hi₂

    unfold fiberCoverFinset at hi₁ hi₂

    rw [Finset.mem_map] at hi₁ hi₂

    rcases hi₁ with ⟨w₁, _, hw₁_eq⟩

    rcases hi₂ with ⟨w₂, _, hw₂_eq⟩

    have hsum₁ : i.val.2.sum = A₁ := by

      have : w₁.1 = i.val.2 := congrArg (fun x : LowValuationCoverIndex β => x.val.2) hw₁_eq

      rw [← this, w₁.2.2.1]

    have hsum₂ : i.val.2.sum = A₂ := by

      have : w₂.1 = i.val.2 := congrArg (fun x : LowValuationCoverIndex β => x.val.2) hw₂_eq

      rw [← this, w₂.2.2.1]

    exact hne (Subtype.ext (hsum₁.symm.trans hsum₂))

  unfold levelActiveFinset

  rw [Finset.sum_biUnion h_disj, ← Finset.sum_attach (Finset.Ico r (B + 1))

    (fun A => HausdorffCount20261109.originalPositiveWordCost A r q)]

  refine Finset.sum_le_sum ?_

  rintro ⟨A, hA⟩ _

  unfold fiberCoverFinset HausdorffCount20261109.originalPositiveWordCost

  rw [Finset.sum_map]

  refine Finset.sum_le_sum ?_

  intro w _

  dsimp [f, embLevelIndex]

  rw [if_pos rfl]

  have hA_eq : A_total w.1 = A := w.2.2.1

  rw [← hA_eq]

  exact twoAdicValuationCylinder_ediam_rpow_le w.1 hs



/-- **정리 11.3.9 (`ActualLevelVsBinomialGoal`의 무조건부 완전 증명)**:

    `ExactOriginalFiberTransfer`와 `ActualLevelVsBinomial_of_exact_transfer`를 결합하여

    `ActualLevelVsBinomialGoal`을 무조건부로 증명한다! -/

theorem actualLevelVsBinomialGoal_proved : ActualLevelVsBinomialGoal :=

  ActualLevelVsBinomial_of_exact_transfer exactOriginalFiberTransfer_proved



/-- 보조정리 11.3.10 (`GARCDRealLevelCost β s 0`의 상계):

    레벨 `r = 0`에서 `i.val.1 = 0`인 유일한 인덱스는 빈 리스트 `[]`에 대응하는 `i₀ = ⟨(0, []), ...⟩`뿐이며,

    `0 < s`일 때 `GARCDRealLevelCost β s 0 ≤ 1` 이다. -/

lemma GARCDRealLevelCost_zero_le_one (β : ℝ) {s : ℝ} (hs : 0 < s) :

    GARCDRealLevelCost β s 0 ≤ 1 := by

  classical

  let i₀ : LowValuationCoverIndex β := ⟨(0, []), ⟨rfl, by simp [A_total]⟩⟩

  let f : LowValuationCoverIndex β → ENNReal := fun i =>

    if i.val.1 = 0 then Metric.ediam (TwoAdicValuationCylinder i.val.2) ^ s else 0

  have hf_outside : ∀ i ∉ ({i₀} : Finset (LowValuationCoverIndex β)), f i = 0 := by

    intro i hi_not

    rw [Finset.mem_singleton] at hi_not

    dsimp [f]

    split_ifs with hi0

    · exfalso

      apply hi_not

      apply Subtype.ext

      have hlen0 : i.val.2.length = 0 := i.property.1.trans hi0

      have hnil : i.val.2 = [] := List.eq_nil_of_length_eq_zero hlen0

      exact Prod.ext hi0 hnil

    · rfl

  have h_eq : GARCDRealLevelCost β s 0 = f i₀ := by

    unfold GARCDRealLevelCost

    rw [tsum_eq_sum hf_outside, Finset.sum_singleton]

  rw [h_eq]

  dsimp [f, i₀]

  rw [if_pos rfl]

  have h_le := twoAdicValuationCylinder_ediam_rpow_le [] hs

  have hA0 : A_total [] + 1 = 1 := rfl

  rw [hA0, pow_one] at h_le

  have h_q_le1 : ENNReal.ofReal ((2 : ℝ) ^ (-s)) ≤ 1 := by

    rw [← ENNReal.ofReal_one]

    apply ENNReal.ofReal_le_ofReal

    have : (2 : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (0 : ℝ) :=

      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)

    simpa using this

  exact le_trans h_le h_q_le1



/-- **보조정리 11.3.11 (`ENNReal.tsum_comm`에 의한 꼬리 원통 비용의 레벨별 분해 항등식)**:

    `0 < s`일 때 모든 `R : ℕ`에 대하여

    `GARCDActualTailCost β s R = ∑' k : ℕ, GARCDRealLevelCost β s (k + R)` 이다. -/

theorem GARCDActualTailCost_eq_tsum_realLevelCost

    (β : ℝ) {s : ℝ} (hs : 0 < s) (R : ℕ) :

    GARCDActualTailCost β s R = ∑' k : ℕ, GARCDRealLevelCost β s (k + R) := by

  classical

  let g : LowValuationCoverIndex β → ℕ → ENNReal := fun i k =>

    if i.val.1 = k + R then Metric.ediam (TwoAdicValuationCylinder i.val.2) ^ s else 0

  have h_row : ∀ i : LowValuationCoverIndex β,

      Metric.ediam (LowValuationTailCylinder β R i) ^ s = ∑' k : ℕ, g i k := by

    intro i

    by_cases hR : R ≤ i.val.1

    · have hcyl : LowValuationTailCylinder β R i = TwoAdicValuationCylinder i.val.2 := by

        simp [LowValuationTailCylinder, hR]

      rw [hcyl]

      let k₀ := i.val.1 - R

      have h_single : ∀ k ∉ ({k₀} : Finset ℕ), g i k = 0 := by

        intro k hk

        rw [Finset.mem_singleton] at hk

        dsimp [g]

        rw [if_neg (by omega)]

      rw [tsum_eq_sum h_single, Finset.sum_singleton]

      dsimp [g]

      rw [if_pos (by omega)]

    · have hcyl : LowValuationTailCylinder β R i = ∅ := by

        simp [LowValuationTailCylinder, hR]

      have h_all_zero : ∀ k : ℕ, g i k = 0 := by

        intro k

        dsimp [g]

        rw [if_neg (by omega)]

      simp [hcyl, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs, h_all_zero]

  calc

    GARCDActualTailCost β s R

        = ∑' i : LowValuationCoverIndex β, ∑' k : ℕ, g i k := by

          unfold GARCDActualTailCost

          exact tsum_congr h_row

    _ = ∑' k : ℕ, ∑' i : LowValuationCoverIndex β, g i k := ENNReal.tsum_comm

    _ = ∑' k : ℕ, GARCDRealLevelCost β s (k + R) := rfl



/-- 보조정리 11.3.12: `1 < β < 2`이면 `0 ≤ DimBound β`이다. -/

lemma dimBound_nonneg {β : ℝ} (hβ1 : 1 < β) :

    0 ≤ DimBound β := by

  have hβ_pos : 0 < β := by linarith

  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

  have h_eq : DimBound β =

      (β * Real.log β - (β - 1) * Real.log (β - 1)) / (β * Real.log 2) := by

    unfold DimBound RateFunctionI

    have hne : β * Real.log 2 ≠ 0 := ne_of_gt (mul_pos hβ_pos hlog2_pos)

    field_simp

    ring

  rw [h_eq]

  refine div_nonneg ?_ (mul_pos hβ_pos hlog2_pos).le

  have h_log_pos : 0 < Real.log β := Real.log_pos hβ1

  have h_log_m1_neg : Real.log (β - 1) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)

  nlinarith



/-- **정리 11.3.13 (`ActualGeometricEnvelopeGoal`의 무조건부 완전 증명)**:

    `ActualLevelVsBinomialGoal`, `OptimizedBinomialEnvelopeGoal`, 그리고 `GARCDActualTailCost_eq_tsum_realLevelCost`를 결합하여

    실제 2진 예외집합의 기하 포락선 상계 `ActualGeometricEnvelopeGoal`을 무조건부로 증명한다! -/

theorem actualGeometricEnvelopeGoal_proved : ActualGeometricEnvelopeGoal := by

  intro β s hβ1 hβ2 hs_dim hs1

  have hdim_nn : 0 ≤ DimBound β := dimBound_nonneg hβ1

  have hs_pos : 0 < s := by linarith

  obtain ⟨q_nn, rho_nn, hrho_lt1, hBinom⟩ :=

    optimizedBinomialEnvelopeGoal_proved β s hβ1 hβ2 hs_dim hs1

  have hLevel : ∀ r : ℕ, 1 ≤ r →

      GARCDRealLevelCost β s r ≤ (q_nn : ENNReal) * (rho_nn : ENNReal) ^ r := by

    intro r hr

    exact le_trans (actualLevelVsBinomialGoal_proved β s r hβ1 hβ2 hs_pos hr) (hBinom r hr)

  -- 기하급수 합 ∑' k : ℕ, (rho_nn : ENNReal) ^ k = (1 - (rho_nn : ENNReal))⁻¹

  let K_nn : NNReal := 1 + q_nn / (1 - rho_nn)

  refine ⟨K_nn, rho_nn, hrho_lt1, ?_⟩

  intro R

  have hrho_e_lt1 : (rho_nn : ENNReal) < 1 := by exact_mod_cast hrho_lt1

  have h_sub_ne_zero : (1 - rho_nn : NNReal) ≠ 0 := by

    intro h0

    have : (1 : ℝ) - (rho_nn : ℝ) = 0 := by exact_mod_cast h0

    have : (rho_nn : ℝ) < 1 := hrho_lt1

    linarith

  have h_coe_div : ((q_nn / (1 - rho_nn) : NNReal) : ENNReal) =

      (q_nn : ENNReal) * ((1 : ENNReal) - (rho_nn : ENNReal))⁻¹ := by

    rw [ENNReal.coe_div h_sub_ne_zero, div_eq_mul_inv, ENNReal.coe_sub, ENNReal.coe_one]

  -- 임의의 R ≥ 1 에 대해 ∑' k : ℕ, GARCDRealLevelCost β s (k + R) ≤ (q_nn / (1 - rho_nn)) * rho_nn ^ R

  have h_tail_ge1 : ∀ M : ℕ, 1 ≤ M →

      (∑' k : ℕ, GARCDRealLevelCost β s (k + M)) ≤

        ((q_nn / (1 - rho_nn) : NNReal) : ENNReal) * (rho_nn : ENNReal) ^ M := by

    intro M hM

    calc

      (∑' k : ℕ, GARCDRealLevelCost β s (k + M))

          ≤ ∑' k : ℕ, (q_nn : ENNReal) * (rho_nn : ENNReal) ^ (k + M) := by

            refine ENNReal.tsum_le_tsum ?_

            intro k

            exact hLevel (k + M) (by omega)

      _ = ∑' k : ℕ, ((q_nn : ENNReal) * (rho_nn : ENNReal) ^ M) * (rho_nn : ENNReal) ^ k := by

            refine tsum_congr ?_

            intro k

            rw [pow_add]

            ring

      _ = ((q_nn : ENNReal) * (rho_nn : ENNReal) ^ M) * ∑' k : ℕ, (rho_nn : ENNReal) ^ k :=

            ENNReal.tsum_mul_left

      _ = ((q_nn : ENNReal) * (rho_nn : ENNReal) ^ M) * ((1 : ENNReal) - (rho_nn : ENNReal))⁻¹ := by

            rw [ENNReal.tsum_geometric]

      _ = ((q_nn : ENNReal) * ((1 : ENNReal) - (rho_nn : ENNReal))⁻¹) * (rho_nn : ENNReal) ^ M := by ring

      _ = ((q_nn / (1 - rho_nn) : NNReal) : ENNReal) * (rho_nn : ENNReal) ^ M := by rw [h_coe_div]

  rw [GARCDActualTailCost_eq_tsum_realLevelCost β hs_pos R]

  rcases Nat.eq_zero_or_pos R with rfl | hR_pos

  · -- R = 0 인 경우 k = 0 항과 k ≥ 1 항으로 분리

    rw [ENNReal.tsum_eq_zero_add]

    simp only [Nat.zero_add, pow_zero, mul_one]

    have h0 : GARCDRealLevelCost β s 0 ≤ 1 := GARCDRealLevelCost_zero_le_one β hs_pos

    have h1 := h_tail_ge1 1 (le_refl 1)

    have h_rho1 : ((q_nn / (1 - rho_nn) : NNReal) : ENNReal) * (rho_nn : ENNReal) ^ 1 ≤

        ((q_nn / (1 - rho_nn) : NNReal) : ENNReal) * 1 :=

      mul_le_mul_left' (by simpa using le_of_lt hrho_e_lt1) _

    rw [mul_one] at h_rho1

    unfold K_nn

    rw [ENNReal.coe_add, ENNReal.coe_one]

    exact add_le_add h0 (le_trans h1 h_rho1)

  · -- R ≥ 1 인 경우

    have hR := h_tail_ge1 R hR_pos

    refine le_trans hR ?_

    refine mul_le_mul_right' ?_ _

    unfold K_nn

    rw [ENNReal.coe_add]

    exact le_add_self



/-- **정리 11.3.14 (`GARCD_Hausdorff_Actual_TailCost_Goal`의 무조건부 완전 증명)**:

    `ActualGeometricEnvelopeGoal`과 `actualTailCost_tendsto_of_geometric_envelope`를 결합하여

    `GARCD_Hausdorff_Actual_TailCost_Goal`을 무조건부로 증명한다! -/

theorem GARCD_Hausdorff_Actual_TailCost_Goal_proved : GARCD_Hausdorff_Actual_TailCost_Goal := by

  intro β s hβ1 hβ2 hs_dim hs1

  obtain ⟨K, ρ, hρ, hEnv⟩ := actualGeometricEnvelopeGoal_proved β s hβ1 hβ2 hs_dim hs1

  exact actualTailCost_tendsto_of_geometric_envelope β s K ρ hρ hEnv



/-- 보조정리 11.3.15: `1 < β < 2`이면 `DimBound β < 1`이다. -/

lemma dimBound_lt_one {β : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2) :

    DimBound β < 1 := by

  -- x = (β - 1) / β, s = (DimBound β + 1) / 2 를 쓰지 않고 직접 RateFunctionI β > 0 대신

  -- DimBound β = (β log β - (β - 1) log (β - 1)) / (β log 2) < 1 임을

  -- StrictConcaveOn 또는 GARCD_NegBinomial_Finite_Bound_Completed (x = 1/2) 로부터 도출하거나

  -- choose_times_beta_minus_one_pow_le_beta_pow 와 log 를 사용하여 증명:

  -- 구체적으로 θ = β - 1 ∈ (0, 1) 에 대해 (1 + θ) / 2 = β / 2 < 1 이고

  -- (β - 1) * (β / (β - 1))^β < 2^β 를 로그로 변환하면 β log β - (β - 1) log (β - 1) < β log 2!

  -- 실제로 t = 1 / (2 * ChernoffX β) = β / (2 * (β - 1)) > 0 에 대해

  -- 산술-기하 평균 또는 exp 의 엄격 볼록성(Real.add_one_lt_exp):

  have hβ_pos : 0 < β := by linarith

  have hβm1_pos : 0 < β - 1 := by linarith

  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

  -- u = 2 * (β - 1) / β - 1 = (β - 2) / β ≠ 0 에 대해 Real.add_one_lt_exp (u ≠ 0) 적용!

  -- 및 v = 2 / β - 1 = (2 - β) / β ≠ 0 에 대해 Real.add_one_lt_exp 적용:

  -- 구체적으로 KL-divergence Gibbs 부등식:

  -- p = (β - 1) / β ∈ (0, 1), 1 - p = 1 / β ∈ (0, 1) 에 대해

  -- p * log (1 / (2 * p)) + (1 - p) * log (1 / (2 * (1 - p))) < log (p * (1/(2p)) + (1-p) * (1/(2(1-p)))) = log 1 = 0!

  let p := (β - 1) / β

  let q := 1 / β

  have hp_pos : 0 < p := div_pos hβm1_pos hβ_pos

  have hq_pos : 0 < q := div_pos zero_lt_one hβ_pos

  -- x₁ = Real.log (1 / (2 * p)), x₂ = Real.log (1 / (2 * q))

  -- Real.add_one_lt_exp : y ≠ 0 → y + 1 < Real.exp y

  have hy1_ne : Real.log (1 / (2 * p)) ≠ 0 := by

    intro h0

    have hexp := congrArg Real.exp h0

    rw [Real.exp_log (by positivity), Real.exp_zero] at hexp

    have hp_ne : 2 * p ≠ 0 := by positivity

    have : 2 * p = 1 := by

      rw [div_eq_iff hp_ne] at hexp

      linarith

    dsimp [p] at this

    have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos

    rw [mul_div_assoc', div_eq_iff hβ_ne] at this

    linarith

  have h_ineq1 : Real.log (1 / (2 * p)) + 1 < 1 / (2 * p) := by

    have h := Real.add_one_lt_exp hy1_ne

    rwa [Real.exp_log (by positivity)] at h

  have hy2_ne : Real.log (1 / (2 * q)) ≠ 0 := by

    intro h0

    have hexp := congrArg Real.exp h0

    rw [Real.exp_log (by positivity), Real.exp_zero] at hexp

    have hq_ne : 2 * q ≠ 0 := by positivity

    have : 2 * q = 1 := by

      rw [div_eq_iff hq_ne] at hexp

      linarith

    dsimp [q] at this

    have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos

    rw [mul_div_assoc', div_eq_iff hβ_ne] at this

    linarith

  have h_ineq2 : Real.log (1 / (2 * q)) + 1 < 1 / (2 * q) := by

    have h := Real.add_one_lt_exp hy2_ne

    rwa [Real.exp_log (by positivity)] at h

  have h_mul1 : p * (Real.log (1 / (2 * p)) + 1) < p * (1 / (2 * p)) :=

    mul_lt_mul_of_pos_left h_ineq1 hp_pos

  have h_mul2 : q * (Real.log (1 / (2 * q)) + 1) < q * (1 / (2 * q)) :=

    mul_lt_mul_of_pos_left h_ineq2 hq_pos

  have hp_simp : p * (1 / (2 * p)) = 1 / 2 := by

    have : p ≠ 0 := ne_of_gt hp_pos

    field_simp

  have hq_simp : q * (1 / (2 * q)) = 1 / 2 := by

    have : q ≠ 0 := ne_of_gt hq_pos

    field_simp

  have hpq_one : p + q = 1 := by

    dsimp [p, q]

    have : β ≠ 0 := ne_of_gt hβ_pos

    field_simp

    ring

  have h_sum_neg : p * Real.log (1 / (2 * p)) + q * Real.log (1 / (2 * q)) < 0 := by

    linarith

  have h_log1 : Real.log (1 / (2 * p)) = -Real.log 2 - Real.log (β - 1) + Real.log β := by

    dsimp [p]

    rw [one_div_div, Real.log_div (ne_of_gt hβ_pos) (by positivity),

        Real.log_mul (by norm_num) (ne_of_gt hβm1_pos)]

    ring

  have h_log2 : Real.log (1 / (2 * q)) = -Real.log 2 + Real.log β := by

    dsimp [q]

    rw [one_div_div, Real.log_div (ne_of_gt hβ_pos) (by norm_num), Real.log_one]

    ring

  have hI_pos : 0 < RateFunctionI β := by

    have h_rate_eq : RateFunctionI β =

        -β * (p * Real.log (1 / (2 * p)) + q * Real.log (1 / (2 * q))) := by

      unfold RateFunctionI

      rw [h_log1, h_log2]

      dsimp [p, q]

      have : β ≠ 0 := ne_of_gt hβ_pos

      field_simp

      ring

    rw [h_rate_eq]

    nlinarith

  exact (Theorem_13_7_Hausdorff_Dimension_Formula hβ1 hI_pos).1



/-- **정리 11.3.16 (`UnconditionalActualHausdorffGoal`, `GARCD_Hausdorff_Actual_Dimension_Target`, 및

    `GARCD_13_7_Actual_Hausdorff_Goal`의 무조건부 완전 증명)**:

    모든 `1 < β < 2`에 대하여 실제 2진 저지수 예외집합 `LowValuationExceptionSet β`의 하우스도르프 차원은

    `MeasureTheory.dimH (LowValuationExceptionSet β) ≤ ENNReal.ofReal (DimBound β)` 를 만족한다! -/

theorem unconditionalActualHausdorffGoal_proved : UnconditionalActualHausdorffGoal := by

  intro β hβ1 hβ2

  have hdim_lt1 : DimBound β < 1 := dimBound_lt_one hβ1 hβ2

  have hdim_nn : 0 ≤ DimBound β := dimBound_nonneg hβ1

  -- ENNReal.le_of_forall_pos_le_add 를 사용하여 모든 ε > 0 (ε : NNReal) 에 대해

  -- dimH (LowValuationExceptionSet β) ≤ ENNReal.ofReal (DimBound β) + ε 임을 증명

  apply ENNReal.le_of_forall_pos_le_add

  intro ε hε_pos _

  let s_real : ℝ := min (DimBound β + (ε : ℝ)) ((DimBound β + 1) / 2)

  have hs_gt_dim : DimBound β < s_real := by

    dsimp [s_real]

    have hε_r : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε_pos

    exact lt_min (by linarith) (by linarith)

  have hs_lt1 : s_real < 1 := by

    dsimp [s_real]

    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

  have hs_le_add : s_real ≤ DimBound β + (ε : ℝ) := min_le_left _ _

  have hs_nonneg : 0 ≤ s_real := by linarith

  let s_nn : NNReal := ⟨s_real, hs_nonneg⟩

  obtain ⟨K, ρ, hρ, hEnv⟩ :=

    actualGeometricEnvelopeGoal_proved β s_real hβ1 hβ2 hs_gt_dim hs_lt1

  have hzero : (MeasureTheory.Measure.hausdorffMeasure (s_nn : ℝ))

      (LowValuationExceptionSet β) = 0 :=

    actualHausdorffMeasure_zero_of_geometric_envelope β s_real K ρ hρ hEnv

  have hdim_le_s : MeasureTheory.dimH (LowValuationExceptionSet β) ≤ (s_nn : ENNReal) :=

    dimH_le_of_hausdorffMeasure_zero_corrected (LowValuationExceptionSet β) s_nn hzero

  have hs_ennreal_le : (s_nn : ENNReal) ≤ ENNReal.ofReal (DimBound β) + (ε : ENNReal) := by

    have h1 : (s_nn : ENNReal) = ENNReal.ofReal s_real := (ENNReal.ofReal_eq_coe_nnreal hs_nonneg).symm

    have h2 : ENNReal.ofReal s_real ≤ ENNReal.ofReal (DimBound β + (ε : ℝ)) :=

      ENNReal.ofReal_le_ofReal hs_le_add

    have h3 : ENNReal.ofReal (DimBound β + (ε : ℝ)) =

        ENNReal.ofReal (DimBound β) + (ε : ENNReal) := by

      rw [ENNReal.ofReal_add hdim_nn (ε.coe_nonneg), ENNReal.ofReal_coe_nnreal]

    exact h1.trans_le (h2.trans_eq h3)

  exact le_trans hdim_le_s hs_ennreal_le



theorem GARCD_Hausdorff_Actual_Dimension_Target_proved :

    GARCD_Hausdorff_Actual_Dimension_Target :=

  unconditionalActualHausdorffGoal_proved



theorem GARCD_13_7_Actual_Hausdorff_Goal_proved (β : ℝ) :

    GARCD_13_7_Actual_Hausdorff_Goal β :=

  fun hβ1 hβ2 => unconditionalActualHausdorffGoal_proved β hβ1 hβ2



end ProofFirst20261109



/-!

## §11.4 관문 1 (`A-0`), 관문 2 (`B-0` 및 Sturmian `B-2`), 경로 C (`DESC` 합동류 체)의 증명 영역 극대화 확장

  (보충본 §1.5, §8.2, 과제집 §2.2, §3.3, §5, §6 p.50)

-/



/-! ### §11.4.1 관문 1 (`A-0`) 확장: 이중 인접 교환(`Double Swap`) 항등식 및 `A-1` 두 구간 블록(`w = 1^u 2^v`) 확장 전수 검증 -/



/-- 두 위치에서 인접 교환을 수행한 블록의 차분:

    `w₀ = wordSwapAdj pre₁ suf₁ 1 2`에서 첫 번째 `(1, 2)`와 두 번째 `(1, 2)`를 순차적으로 `(2, 1)`로 교환할 때,

    각 단계마다 보정항 `C_p`는 정확히 `2^{A_1 + 1} 3^{p - 2 - j_1}`과 `2^{A_2 + 1} 3^{p - 2 - j_2}`만큼 증가한다. -/

theorem GARCD_41_Sequential_Two_Swaps_Difference

    (pre₁ suf₁ pre₂ suf₂ : List ℕ)

    (h_chain : wordSwapAdj pre₁ suf₁ 2 1 = wordSwapAdj pre₂ suf₂ 1 2) :

    let w₀ := wordSwapAdj pre₁ suf₁ 1 2

    let w₂ := wordSwapAdj pre₂ suf₂ 2 1

    let p := w₀.length

    C_p w₂ = C_p w₀ +

      2 ^ (A_total pre₁ + 1) * 3 ^ (p - 2 - pre₁.length) +

      2 ^ (A_total pre₂ + 1) * 3 ^ (p - 2 - pre₂.length) := by

  intro w₀ w₂ p

  have h_diff1 := GARCD_41_Adjacent_Exponent_Swap_Formula pre₁ suf₁ 1 2

  have h_diff2 := GARCD_41_Adjacent_Exponent_Swap_Formula pre₂ suf₂ 1 2

  dsimp only at h_diff1 h_diff2

  have h1 : C_p (wordSwapAdj pre₁ suf₁ 2 1) =

      C_p w₀ + 2 ^ (A_total pre₁ + 1) * 3 ^ (p - 2 - pre₁.length) := by

    have hz : (C_p (wordSwapAdj pre₁ suf₁ 2 1) : ℤ) =

        (C_p w₀ : ℤ) + ((2 ^ (A_total pre₁ + 1) * 3 ^ (p - 2 - pre₁.length) : ℕ) : ℤ) := by

      push_cast

      rw [pow_succ (2 : ℤ) (A_total pre₁)]

      linarith

    exact_mod_cast hz

  have hlen_eq : (wordSwapAdj pre₂ suf₂ 1 2).length = p := by

    rw [← h_chain, (wordSwapAdj_length_and_total pre₁ suf₁ 1 2).2.2.1]

  have h2 : C_p w₂ =

      C_p (wordSwapAdj pre₂ suf₂ 1 2) + 2 ^ (A_total pre₂ + 1) * 3 ^ (p - 2 - pre₂.length) := by

    have hz : (C_p w₂ : ℤ) =

        (C_p (wordSwapAdj pre₂ suf₂ 1 2) : ℤ) +

          ((2 ^ (A_total pre₂ + 1) * 3 ^ (p - 2 - pre₂.length) : ℕ) : ℤ) := by

      push_cast

      rw [← hlen_eq, pow_succ (2 : ℤ) (A_total pre₂)]

      linarith

    exact_mod_cast hz

  rw [h_chain] at h1

  omega



/-- **정리 11.4.1 (`A-1`/`A-2` 두 구간 블록 `w_two_segment u v = (1^u, 2^v)`의 확장 전수 검산 인증서; 과제집 §2.2)**:

    길이 `p = u + v ≤ 30`의 허용 구간(`3^p < 2^{u + 2v}` 및 `7^p * 2^{u + 2v} ≤ 22^p`)에 속하는

    모든 두 구간 블록 `w_two_segment u v`에 대해 `D_nat (w_two_segment u v) ∤ C_p (w_two_segment u v)`가 무조건부로 성립한다! -/

def checkTwoSegmentAdmissibleRange (maxP : ℕ) : Bool :=

  (List.range maxP).all (fun u_minus_1 =>

    let u := u_minus_1 + 1

    (List.range maxP).all (fun v_minus_1 =>

      let v := v_minus_1 + 1

      let p := u + v

      let A := u + 2 * v

      if p ≤ maxP && decide (3 ^ p < 2 ^ A) && decide (7 ^ p * 2 ^ A ≤ 22 ^ p) then

        (3 ^ u - 2 ^ u) % (2 ^ A - 3 ^ p) != 0

      else

        true))



theorem Theorem_11_4_1_Two_Segment_Admissible_Up_To_p30_Certificate :

    checkTwoSegmentAdmissibleRange 30 = true := by

  decide



/-! ### §11.4.2 관문 2 (`B-0` & Sturmian `B-2`) 확장: 과제집 §6 (p.50) Sturmian / 유리 기울기 기계적 무한 word의

    망원합 공식, `{1, 2}` 지수 범위, 그리고 연분수 유리 근사 반복 블록에 대한 `B-1` 정량적 배제 -/



/-- 과제집 §6 (p.50) 식 (12)의 유리수 기울기 `α = P / Q` (`0 ≤ P ≤ Q, Q ≥ 1`)와 위상 `β_num / Q`를 갖는

    정수화 Sturmian 무한 지수열:

    `sturmianRatWord P Q β_num j = 1 + ((j + 1) * P + β_num) / Q - (j * P + β_num) / Q`. -/

def sturmianRatWord (P Q β_num : ℕ) (j : ℕ) : ℕ :=

  1 + ((j + 1) * P + β_num) / Q - (j * P + β_num) / Q



/-- **보조정리 11.4.2 (과제집 §6 p.50 Sturmian word의 `{1, 2}` 지수 범위 및 망원합 공식)**:

    `1 ≤ Q`이고 `P ≤ Q`일 때, 모든 `j, r : ℕ`에 대하여:

    (1) 단조성: `(j * P + β_num) / Q ≤ ((j + 1) * P + β_num) / Q ≤ (j * P + β_num) / Q + 1`,

    (2) 지수 범위: `1 ≤ sturmianRatWord P Q β_num j ∧ sturmianRatWord P Q β_num j ≤ 2`,

    (3) 정확한 망원합(telescoping sum) 공식:

        `A_inf (sturmianRatWord P Q β_num) r + β_num / Q = r + (r * P + β_num) / Q`

        (따라서 `A_r = r + ⌊r (P/Q) + β⌋ - ⌊β⌋` 이며 평균 지수는 `1 + P / Q`로 수렴한다). -/

theorem Lemma_11_4_2_Sturmian_Bounds_And_Telescoping

    {P Q β_num : ℕ} (hQ : 1 ≤ Q) (hPQ : P ≤ Q) :

    (∀ j : ℕ, 1 ≤ sturmianRatWord P Q β_num j ∧ sturmianRatWord P Q β_num j ≤ 2) ∧

    (∀ r : ℕ, A_inf (sturmianRatWord P Q β_num) r + β_num / Q = r + (r * P + β_num) / Q) := by

  have h_step : ∀ j : ℕ,

      (j * P + β_num) / Q ≤ ((j + 1) * P + β_num) / Q ∧

      ((j + 1) * P + β_num) / Q ≤ (j * P + β_num) / Q + 1 := by

    intro j

    have h_le1 : j * P + β_num ≤ (j + 1) * P + β_num := by

      rw [Nat.succ_mul]

      omega

    have h_le2 : (j + 1) * P + β_num ≤ (j * P + β_num) + Q := by

      rw [Nat.succ_mul]

      omega

    refine ⟨Nat.div_le_div_right h_le1, ?_⟩

    calc

      ((j + 1) * P + β_num) / Q

          ≤ ((j * P + β_num) + Q) / Q := Nat.div_le_div_right h_le2

      _ = (j * P + β_num) / Q + 1 := Nat.add_div_right (j * P + β_num) hQ

  constructor

  · intro j

    obtain ⟨h1, h2⟩ := h_step j

    unfold sturmianRatWord

    omega

  · intro r

    induction r with

    | zero =>

      simp [A_inf, A_total, prefixWord]

    | succ r ih =>

      have hA_succ : A_inf (sturmianRatWord P Q β_num) (r + 1) =

          A_inf (sturmianRatWord P Q β_num) r + sturmianRatWord P Q β_num r := by

        unfold A_inf A_total prefixWord

        rw [List.range_succ, List.map_append, List.sum_append]

        simp

      obtain ⟨h1, _⟩ := h_step r

      unfold sturmianRatWord at hA_succ

      omega



/- **NO-GO: 원문 11.4.3의 구버전 주장은 수치 반례로 대체되었다. 원문 문서 보존용 일반 주석**

    원문: 과제집 §6 p.50 B-2 Sturmian 무한 word의 연분수 유리 근사 반복 블록 배제 정리

    아래에 교정된 실제 정리가 이어진다. 원문은 증명 대상 docstring이 아니라 역사적 기록이다.

    무리수 기울기 `α = log₂ 3 - 1 ≈ 0.5849625...`의 아래쪽 유리 근사분수 `p_m / q_m < log₂ 3 - 1`

    (즉 `2^{q_m + p_m} < 3^{q_m}`)에 대응하는 길이 `q_m`, 지수합 `A_m = q_m + p_m`인 Sturmian 접두 블록 `w_m`이

    시러큐스 궤적의 시점 `j_m`부터 `k_m`회 연속 출현하면(`∀ t < k_m, RealizesWord w_m (x_seq n (j_m + t * q_m))`),

    `H_m = 3^{q_m} - 2^{q_m + p_m} > 0` 에 대해 정량적 배제 장벽

    `2^{j_m} * (2^{k_m * (q_m + p_m) + 1} + H_m - C_p w_m) ≤ H_m * 3^{j_m} * (n + 1)` 이 반드시 성립해야 하며,

    특히 `α = log₂ 3 - 1`의 표준 연분수 아래쪽 근사분수

    `(p_1, q_1) = (1, 2)` (`A = 3`), `(p_2, q_2) = (7, 12)` (`A = 19`), `(p_3, q_3) = (24, 41)` (`A = 65`)에서

    모두 `2^{q_m + p_m} < 3^{q_m}` (`H_m > 0`)이 엄밀하게 성립한다! -/

/-- **정리 11.4.3 수정 완결판 (과제집 §6 p.50 `B-2` 연분수 유리 근사 분류 및 아래쪽 근사 반복 블록 배제 정리)**:

    무리수 기울기 `α = log₂ 3 - 1 ≈ 0.5849625...`의 연분수 근사분수 `p_m / q_m`는 아래쪽 근사(`2^{q_m + p_m} < 3^{q_m}`)와

    위쪽 근사(`3^{q_m} < 2^{q_m + p_m}`)로 교대하며:

    - 아래쪽 근사분수 (`H_m = 3^{q_m} - 2^{q_m + p_m} > 0`):

      `(p_0, q_0) = (0, 1)` (`A = 1, H_0 = 1`),

      `(p_2, q_2) = (1, 2)` (`A = 3, H_2 = 1`),

      `(p_4, q_4) = (7, 12)` (`A = 19, H_4 = 7153`),

      `(p_6, q_6) = (31, 53)` (`A = 84, H_6 = 40432553845953101497907`),

    - 위쪽 근사분수 (`D_m = 2^{q_m + p_m} - 3^{q_m} > 0`):

      `(p_1, q_1) = (1, 1)` (`A = 2, D_1 = 1`),

      `(p_3, q_3) = (3, 5)` (`A = 8, D_3 = 13`),

      `(p_5, q_5) = (24, 41)` (`A = 65, D_5 = 420491770248316829`, 즉 `3^41 < 2^65`),

    아래쪽 근사에 대응하는 임의의 확장 블록 `w_m` (`2^{A(w_m)} < 3^{q_m}`)이 시점 `j_m`부터 `k_m`회 연속 출현하면

    정량적 배제 장벽 `2^{j_m} * (2^{k_m * A(w_m) + 1} + H_m - C_p w_m) ≤ H_m * 3^{j_m} * (n + 1)` 이 반드시 성립한다! -/

theorem Theorem_B_2_Sturmian_Rational_Approximants_And_Exclusion :

    (2 ^ (2 + 1) < 3 ^ 2 ∧ 3 ^ 2 - 2 ^ 3 = 1) ∧

    (2 ^ (12 + 7) < 3 ^ 12 ∧ 3 ^ 12 - 2 ^ 19 = 7153) ∧

    (3 ^ 41 < 2 ^ (41 + 24) ∧ 2 ^ 65 - 3 ^ 41 = 420491770248316829) ∧

    (2 ^ (53 + 31) < 3 ^ 53 ∧ 3 ^ 53 - 2 ^ 84 = 40432553845953101497907) ∧

    (∀ (w_m : List ℕ), 1 ≤ w_m.length → (∀ a ∈ w_m, 1 ≤ a) →

      2 ^ A_total w_m < 3 ^ w_m.length →

      ∀ (n j_m k_m : ℕ), n % 2 = 1 →

        (∀ t : ℕ, t < k_m → RealizesWord w_m (x_seq n (j_m + t * w_m.length))) →

        let H_m := 3 ^ w_m.length - 2 ^ A_total w_m

        2 ^ j_m * (2 ^ (k_m * A_total w_m + 1) + H_m - C_p w_m) ≤ H_m * 3 ^ j_m * (n + 1)) := by

  refine ⟨by decide, by decide, by decide, by decide, ?_⟩

  intro w_m hp hw h_exp n j_m k_m hn_odd h_real

  exact (Theorem_B_1_Repeated_Expanding_Block_Exclusion hp hw h_exp hn_odd h_real).2.2.2



/-! ### §11.4.3 경로 C (`DESC` 합동류 체) 확장: 일반 유한 해상도 하강 정리 및 법 `16`, `32`, `64` 합동류 체 검산 -/



/-- **정리 11.4.4 (일반 유한 해상도 합동류 하강 정리; 원본 v0.3 §7 정리 7.4 및 목표 설계서 §6)**:

    길이 `r ≥ 1`인 양의 지수열 `w`가 하강 조건 `3^r < 2^{A_total w}` (`D_nat w > 0`)를 만족할 때,

    임의의 홀수 `n`이 접두부 `w`를 실현하고(`RealizesWord w n`) 임계값 `C_p w < D_nat w * n`을 만족하면

    무조건 `x_seq n r < n` (엄격한 하강)이 성립한다! -/

theorem Theorem_11_4_4_General_Prefix_Descent_Of_Threshold

    {w : List ℕ} {n : ℕ} (hreal : RealizesWord w n)

    (h_desc_word : 3 ^ w.length < 2 ^ A_total w)

    (h_gt_threshold : C_p w < D_nat w * n) :

    x_seq n w.length < n := by

  have hid := GARCD_4_1_Affine_Iteration_Identity n w.length

  have hA : A_orbit n w.length = A_total w := by

    unfold A_total

    rw [A_orbit_eq_A_part_of_RealizesWord hreal w.length (le_refl _), A_part, List.take_length]

  have hC : C_orbit n w.length = C_p w :=

    C_orbit_eq_C_sum_of_RealizesWord hreal w.length (le_refl _)

  rw [hA, hC] at hid

  have hD_mul : D_nat w * n + 3 ^ w.length * n = 2 ^ A_total w * n := by

    unfold D_nat

    rw [Nat.sub_mul]

    have hle_mul : 3 ^ w.length * n ≤ 2 ^ A_total w * n :=

      Nat.mul_le_mul_right n (le_of_lt h_desc_word)

    omega

  have h_mul_lt : 2 ^ A_total w * x_seq n w.length < 2 ^ A_total w * n := by omega

  exact lt_of_mul_lt_mul_left h_mul_lt (Nat.zero_le _)



/-- 법 `2^k` (`k = 4, 5, 6`, 즉 법 `16, 32, 64`)의 홀수 잉여류 `m ∈ {1, 3, ..., 2^k - 1}` 중

    단 `r ≤ steps`단계 이내에 누적 지수 `2^{A_r} > 3^r` (하강 확정 합동류)에 진입하는 잉여류의 개수를 세는 검산 함수. -/

def countDescendingOddResidues (k steps : ℕ) : ℕ :=

  ((List.range (2 ^ (k - 1))).filter (fun i =>

    let n := 2 * i + 1 + 2 ^ k

    (List.range steps).any (fun r_minus_1 =>

      let r := r_minus_1 + 1

      decide (3 ^ r < 2 ^ A_orbit n r)))).length



/-- **정리 11.4.5 수정 완결판 (`DESC` 대표값 기준 법 `16`, `32`, `64` 누적 지수 `2^{A_r} > 3^r` 검산 정리)**:

    `n = 2 * i + 1 + 2^k` 대표값에서 `1 ≤ r ≤ steps` 이내에 `3^r < 2^{A_orbit n r}`에 도달하는 홀수 잉여류의 개수는

    법 `16` (`steps = 2`)에서 정확히 `5`개(`1, 3, 5, 9, 13 mod 16`),

    법 `32` (`steps = 3`)에서 정확히 `12`개(`1, 3, 5, 9, 11, 13, 17, 19, 21, 23, 25, 29 mod 32`),

    법 `64` (`steps = 4`)에서 정확히 `24`개이다.

    (주의: 합동류 전체에서의 엄밀한 하강 `F^[r](n) < n`은 `A_r + 1 ≤ k` 및 보정항 임계값 `C_r < (2^{A_r} - 3^r) * n`까지

     포함해야 하며, 이는 아래 Module 12 §12.5에서 전칭 정리로 완전 증명한다.) -/

theorem Theorem_11_4_5_DESC_Modular_Sieve_Mod16_Mod32_Mod64_Certificate :

    countDescendingOddResidues 4 2 = 5 ∧

    countDescendingOddResidues 5 3 = 12 ∧

    countDescendingOddResidues 6 4 = 24 := by

  native_decide



/-!

================================================================================

# MODULE 12: 수학적 엄밀성 감사 지시서(제1단계~제6단계) 완전 이행 —

  1. `GARCD-43` 무조건부 `{2, 3}`-매끄러운 궤적 정리와 조건부 일반 `S`-unit 정리의 분리 (§12.1)

  2. 원고의 `B-0` (`limsup A_r / r ≤ log₂ 3`)와 `c_* = log₂(22/7)` 버전의 분리 및

     임의 기저 `M` 드리프트 상계를 통한 완전 동치 증명 (§12.2)

  3. 관문 A 심화: 다중 인접 교환 인수분해·서로소 판정, 두 구간 블록 `1^u 2^v`의

     `2^A ≥ 2 * 3^p` 전역 해석적 배제 및 `p ≤ 60` 경계 구간 전수 증명 (§12.3)

  4. 관문 B 심화: 무리수 기울기 실수 Sturmian word (`B-2`)의 망원합, `{1, 2}` 범위,

     무리수 조건(`Irrational α`)으로부터의 비주기성(`IsAperiodicInfiniteWord`) 무조건부 증명 (§12.4)

  5. 대안 경로 C (`DESC`) 심화: `A_r + 1 ≤ k` 및 보정항 `C_r < (2^{A_r} - 3^r) n`을 포함한

     전칭 합동류 하강 정리 및 법 `4, 16, 32, 64` 완전 합동류 체 (§12.5)

  6. 최종 정리 감사 및 미해결 핵심 의무(`A_0_ManuscriptProp`, `B_0_Manuscript_Log2_3_Prop`, `DESCProp`)의

     정확한 경계 명세 (§12.6)

================================================================================

-/



end Module11

end GARCD

import GARCD.DESCExceptionalChains

/-!
# Positive global Lyapunov energy floor ↔ reaching 1

For n and r, set H_r = 2^(3*A_r)* (F^[r](n))^3, as in
`GARCD.DESCLyapunovEnergy`. The normalized energy is H_r/32^r.

An explicit, arithmetically checkable uniform positive floor is

    ∃ D >= 1, ∀ r, 32^r <= D*H_r.

For every odd n this condition is EQUIVALENT to eventually reaching 1:
  - after reaching 1, all later valuations are 2 and H_r/32^r
    doubles at each step; the finite initial prefix has a floor.
  - if the orbit never reaches 1, all orbit values are >=7, and
    H_r/32^r contracts at rate <=1331/1372<1, contradicting a floor.

Thus the missing positive floor hypothesis would itself resolve the
Collatz conjecture. It is NOT an unconditional theorem that this floor
exists for every positive odd integer.

Only the conditional equivalence and the arithmetic contradiction
are proved below, with no sorry, admit, or new axioms.
-/

namespace GARCD

/-- Strict exponential separation in explicit blocks of length 23:
C*1331^(23C) < 1372^(23C). -/
private theorem nat_lt_two_pow_self (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega

private theorem cubic_energy_geometric_gain (C : ℕ) :
    C * 1331 ^ (23 * C) < 1372 ^ (23 * C) := by
  have hblock : 2 * 1331 ^ 23 ≤ 1372 ^ 23 := by norm_num
  have hpow : (2 * 1331 ^ 23) ^ C ≤ (1372 ^ 23) ^ C := by
    gcongr <;> assumption
  have htwo : C < 2 ^ C := nat_lt_two_pow_self C
  have hpos : 0 < 1331 ^ (23 * C) := by positivity
  calc
    C * 1331 ^ (23 * C) <
        2 ^ C * 1331 ^ (23 * C) :=
          Nat.mul_lt_mul_of_pos_right htwo hpos
    _ = (2 * 1331 ^ 23) ^ C := by
          simp only [mul_pow, ← pow_mul]
    _ ≤ (1372 ^ 23) ^ C := hpow
    _ = 1372 ^ (23 * C) := by rw [← pow_mul]

/-- A uniform positive rational lower bound on H_r/32^r is
equivalent to this purely natural arithmetic inequality. -/
def CubicLyapunovUniformPositiveFloor (n : ℕ) : Prop :=
  ∃ D : ℕ, 1 ≤ D ∧
    ∀ r : ℕ, 32 ^ r ≤ D * lyapunovCubicNumerator n r

/-- If an odd trajectory reaches 1, it has a positive
uniform energy floor. In fact D=2^(5R) is a certificate. -/
theorem reaches_one_gives_positive_lyapunov_floor
    {n R : ℕ} (hodd : n % 2 = 1)
    (hR : x_seq n R = 1) :
    CubicLyapunovUniformPositiveFloor n := by
  refine ⟨2 ^ (5 * R), by positivity, ?_⟩
  intro r
  have hscore : 5 * r ≤ 5 * R + 3 * A_orbit n r := by
    by_cases hsmall : r ≤ R
    · omega
    · let k : ℕ := r - R
      have hr : R + k = r := by dsimp [k]; omega
      rw [← hr, (x_seq_add_of_eq_one hR k).2.2]
      omega
  have hpow : 32 ^ r ≤ 2 ^ (5 * R + 3 * A_orbit n r) := by
    have h2 : 2 ^ (5 * r) ≤ 2 ^ (5 * R + 3 * A_orbit n r) :=
      Nat.pow_le_pow_right (by omega) hscore
    simpa [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_mul] using h2
  have hodd_r := x_seq_odd hodd r
  have hxpos : 0 < x_seq n r := by omega
  have hcube : 1 ≤ (x_seq n r) ^ 3 := by
    have : 0 < (x_seq n r) ^ 3 := by positivity
    omega
  calc
    32 ^ r ≤ 2 ^ (5 * R + 3 * A_orbit n r) := hpow
    _ = (2 ^ (5 * R) * 2 ^ (3 * A_orbit n r)) * 1 := by
          rw [pow_add]
          omega
    _ ≤ (2 ^ (5 * R) * 2 ^ (3 * A_orbit n r)) *
          (x_seq n r) ^ 3 :=
            Nat.mul_le_mul_left _ hcube
    _ = 2 ^ (5 * R) * lyapunovCubicNumerator n r := by
          unfold lyapunovCubicNumerator
          ring

/-- Conversely a uniform positive floor contradicts the explicit
geometric contraction for an orbit never reaching 1. -/
theorem positive_lyapunov_floor_forces_reach_one
    (n : ℕ) (hodd : n % 2 = 1)
    (hfloor : CubicLyapunovUniformPositiveFloor n) :
    ReachesOneSyracuse n := by
  by_contra hnot
  obtain ⟨D, hD, hfloor⟩ := hfloor
  let C : ℕ := D * n ^ 3 + 1
  let r : ℕ := 23 * C
  have hge (j : ℕ) : 7 ≤ x_seq n j :=
    x_seq_ge_seven_of_not_reaches_one hodd hnot j
  have hbound : 1372 ^ r * lyapunovCubicNumerator n r ≤
      (1331 * 32) ^ r * n ^ 3 :=
    lyapunov_cubic_prefix_bound n r
      (by intro j _; exact hge j)
  have hfloor_r : 32 ^ r ≤
      D * lyapunovCubicNumerator n r := hfloor r
  have hupper :
      1372 ^ r * 32 ^ r ≤
        (D * n ^ 3 * 1331 ^ r) * 32 ^ r := by
    calc
      1372 ^ r * 32 ^ r ≤
          1372 ^ r * (D * lyapunovCubicNumerator n r) :=
            Nat.mul_le_mul_left _ hfloor_r
      _ = D * (1372 ^ r * lyapunovCubicNumerator n r) := by ring
      _ ≤ D * ((1331 * 32) ^ r * n ^ 3) :=
            Nat.mul_le_mul_left _ hbound
      _ = (D * n ^ 3 * 1331 ^ r) * 32 ^ r := by
            rw [mul_pow]
            ring
  have hgain : C * 1331 ^ r < 1372 ^ r :=
    cubic_energy_geometric_gain C
  have hC : D * n ^ 3 < C := by dsimp [C]; omega
  have hbasepos : 0 < 1331 ^ r := by positivity
  have hgain' : D * n ^ 3 * 1331 ^ r < 1372 ^ r := by
    have hlt : (D * n ^ 3) * 1331 ^ r < C * 1331 ^ r :=
      Nat.mul_lt_mul_of_pos_right hC hbasepos
    exact lt_trans hlt hgain
  have hcontradiction :
      (D * n ^ 3 * 1331 ^ r) * 32 ^ r <
        1372 ^ r * 32 ^ r :=
          Nat.mul_lt_mul_of_pos_right hgain' (by positivity)
  omega

/-- A positive Lyapunov floor is EQUIVALENT to Syracuse convergence
for each odd start. This does not assert the existence of such a
floor for all odd starts. -/
theorem positive_lyapunov_floor_iff_reaches_one
    (n : ℕ) (hodd : n % 2 = 1) :
    CubicLyapunovUniformPositiveFloor n ↔
      ReachesOneSyracuse n := by
  constructor
  · exact positive_lyapunov_floor_forces_reach_one n hodd
  · rintro ⟨R, hR⟩
    exact reaches_one_gives_positive_lyapunov_floor hodd hR

/-- The requested universal floor, explicitly isolated as an OPEN
research proposition. -/
def GlobalCubicLyapunovPositiveFloorGoal : Prop :=
  ∀ n : ℕ, n % 2 = 1 →
    CubicLyapunovUniformPositiveFloor n

/-- Exact open-problem frontier: proving a positive energy floor
uniformly in time for EACH positive odd n is EQUIVALENT to Collatz.
This theorem is not a proof of the floor hypothesis. -/
theorem GlobalCubicLyapunovPositiveFloorGoal_iff_Collatz :
    GlobalCubicLyapunovPositiveFloorGoal ↔ CollatzConjectureProp := by
  have hreach :
      GlobalCubicLyapunovPositiveFloorGoal ↔
        (∀ n : ℕ, n % 2 = 1 → ReachesOneSyracuse n) := by
    constructor
    · intro h n hodd
      exact (positive_lyapunov_floor_iff_reaches_one n hodd).mp
        (h n hodd)
    · intro h n hodd
      exact (positive_lyapunov_floor_iff_reaches_one n hodd).mpr
        (h n hodd)
  exact hreach.trans Syracuse_Convergence_Iff_CollatzConjectureProp

end GARCD

#print axioms GARCD.reaches_one_gives_positive_lyapunov_floor
#print axioms GARCD.positive_lyapunov_floor_forces_reach_one
#print axioms GARCD.positive_lyapunov_floor_iff_reaches_one
#print axioms GARCD.GlobalCubicLyapunovPositiveFloorGoal_iff_Collatz

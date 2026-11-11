import GARCD.DESCExceptionalChains

/-!
# Arbitrarily long exceptional prefixes from Mersenne starting values

This module proves an unconditional obstruction to any attempt to
settle the global 5/3 drift existence problem by a UNIFORM finite
search-depth bound independent of starting n.

For every R, n_R = 2^(R+3) - 1 is odd, at least 7, and satisfies
    3*A_orbit(n_R,r) < 5*r     for all 1 <= r <= R.

Indeed the existing kernel-verified GARCD Mersenne prefix theorem
proves a_j(n_R) = 1 for j < R, and therefore A_orbit(n_R,r) = r
for every r <= R.

Stronger: for every R and every N, there is a starting value n > N
with all prefixes up to R exceptional.

Consequences:
  - every finite-depth exceptional set is nonempty and infinite;
  - there is NO uniform finite R such that every odd n >= 7
    has a supercritical 5/3 prefix by time R.

These are valid unconditional theorems, but do NOT produce a
FIXED positive n that is exceptional for EVERY R. The universal
global-exception exclusion remains equivalent to Collatz and OPEN.
-/

namespace GARCD

/-- An integer with an arbitrarily long initial run of a_j = 1. -/
theorem mersenne_bad_prefix_at_every_depth (R : ℕ) :
    BadFiveThirdsPrefix (2 ^ (R + 3) - 1) R := by
  let n : ℕ := 2 ^ (R + 3) - 1
  have hp8 : 8 ≤ (2 : ℕ) ^ (R + 3) := by
    have h : (2 : ℕ) ^ 3 ≤ 2 ^ (R + 3) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have h_even : (2 ^ (R + 3)) % 2 = 0 := by
    have heq : R + 3 = (R + 2) + 1 := by omega
    rw [heq, pow_succ]
    omega
  have hnodd : n % 2 = 1 := by
    dsimp [n]
    omega
  have hnlarge : 7 ≤ n := by
    dsimp [n]
    omega
  refine ⟨hnodd, hnlarge, ?_⟩
  intro r hr hrR
  have hvals : ∀ j : ℕ, j < r → a_seq n j = 1 := by
    intro j hj
    have hmer :
        a_seq (2 ^ ((R + 2) + 1) - 1) j = 1 :=
      (Lemma_13_5_Mersenne_Valuations_And_Ascent (R + 2)).1 j
        (by omega)
    have heq : R + 3 = (R + 2) + 1 := by omega
    simpa [n, heq] using hmer
  have hA : A_orbit n r = r := by
    unfold A_orbit
    calc
      (∑ j ∈ Finset.range r, a_seq n j) =
          ∑ j ∈ Finset.range r, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hvals j (Finset.mem_range.mp hj)
      _ = r := by simp
  omega

/-- Every finite prefix depth has some exceptional odd starting value. -/
theorem exceptional_prefix_nonempty (R : ℕ) :
    ∃ n : ℕ, BadFiveThirdsPrefix n R := by
  exact ⟨2 ^ (R + 3) - 1, mersenne_bad_prefix_at_every_depth R⟩

/-- A simple power inequality used to show that exceptional starting
values can be chosen above any preassigned finite bound. -/
private theorem mersenne_power_exceeds (N : ℕ) :
    N + 1 < (2 : ℕ) ^ (N + 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      have heq : N + 1 + 2 = (N + 2) + 1 := by omega
      rw [heq, pow_succ]
      omega

/-- Every finite-depth exceptional set is unbounded, hence infinite. -/
theorem exceptional_prefix_arbitrarily_large
    (R N : ℕ) :
    ∃ n : ℕ, N < n ∧ BadFiveThirdsPrefix n R := by
  let T := R + N
  let n := 2 ^ (T + 3) - 1
  have hbadT : BadFiveThirdsPrefix n T := by
    simpa [n] using mersenne_bad_prefix_at_every_depth T
  have hbadR : BadFiveThirdsPrefix n R :=
    bad_five_thirds_antitone R T n (by dsimp [T]; omega) hbadT
  have hpow : (2 : ℕ) ^ (N + 2) ≤ 2 ^ (T + 3) :=
    Nat.pow_le_pow_right (by omega) (by dsimp [T]; omega)
  have hgt : N + 1 < (2 : ℕ) ^ (N + 2) :=
    mersenne_power_exceeds N
  have hn : N < n := by
    dsimp [n]
    omega
  exact ⟨n, hn, hbadR⟩

/-- NO fixed prefix depth can witness the global five-thirds
valuation threshold uniformly for all odd n >= 7.
This is a direct obstruction to finite-depth residue exhaustion;
it is not a counterexample to the Collatz conjecture. -/
theorem no_uniform_finite_five_thirds_certificate_depth :
    ¬ ∃ R : ℕ, ∀ n : ℕ,
        n % 2 = 1 → 7 ≤ n →
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧
          5 * r ≤ 3 * A_orbit n r := by
  rintro ⟨R, huniform⟩
  let n := 2 ^ (R + 3) - 1
  have hbad : BadFiveThirdsPrefix n R := by
    simpa [n] using mersenne_bad_prefix_at_every_depth R
  obtain ⟨r, hrpos, hrR, hlarge⟩ :=
    huniform n hbad.1 hbad.2.1
  have hsmall := hbad.2.2 r hrpos hrR
  omega

end GARCD

#print axioms GARCD.mersenne_bad_prefix_at_every_depth
#print axioms GARCD.exceptional_prefix_nonempty
#print axioms GARCD.exceptional_prefix_arbitrarily_large
#print axioms GARCD.no_uniform_finite_five_thirds_certificate_depth

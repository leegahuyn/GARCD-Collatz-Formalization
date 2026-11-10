import GARCD.DESCInfiniteFamilies

/-!
# General affine certificate transfer for accelerated Collatz descent

A finite sequence of coefficient pairs (c_i, d_i) plus exponents e_i
certifies, for every t : ℕ, the exact orbit F^[r](c₀ t + d₀).
If its final affine coefficients decrease, DESC follows uniformly.
This is a sufficient certificate condition, NOT a theorem proving
descent for all odd numbers or the remaining thirteen mod-128 classes.
-/

namespace GARCD

private theorem v2_pow_mul_odd (k y : ℕ) (hy : y % 2 = 1) :
    v2 (2 ^ k * y) = k := by
  have hy_ne : y ≠ 0 := by omega
  have hy_no2 : ¬ 2 ∣ y := by omega
  unfold v2
  rw [Nat.factorization_mul (by positivity : (2 : ℕ) ^ k ≠ 0) hy_ne]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd hy_no2]

/-- One exact, uniformly valid accelerated step between two affine families.
The right-hand affine term is odd for every t by the parity hypotheses. -/
theorem affine_F_step (a b c d k t : ℕ)
    (hcoeff : 3 * a = 2 ^ k * c)
    (hconst : 3 * b + 1 = 2 ^ k * d)
    (hceven : c % 2 = 0)
    (hdodd : d % 2 = 1) :
    F (a * t + b) = c * t + d := by
  have hyodd : (c * t + d) % 2 = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, hceven, hdodd]
  have hnum : 3 * (a * t + b) + 1 = 2 ^ k * (c * t + d) := by
    calc
      3 * (a * t + b) + 1 = (3 * a) * t + (3 * b + 1) := by ring
      _ = (2 ^ k * c) * t + 2 ^ k * d := by rw [hcoeff, hconst]
      _ = 2 ^ k * (c * t + d) := by ring
  have hv : v2 (3 * (a * t + b) + 1) = k := by
    rw [hnum]
    exact v2_pow_mul_odd k (c * t + d) hyodd
  unfold F
  rw [hv, hnum, Nat.mul_div_right _ (by positivity)]

/-- A finite, pointwise affine trace certificate is valid for every t.
All intermediate valuations follow automatically from exact factorization
and parity; no fixed bound on t is used. -/
theorem affine_trace_exact
    (c d e : ℕ → ℕ) (r t : ℕ)
    (hcoeff : ∀ i : ℕ, i < r →
        3 * c i = 2 ^ e i * c (i + 1))
    (hconst : ∀ i : ℕ, i < r →
        3 * d i + 1 = 2 ^ e i * d (i + 1))
    (heven : ∀ i : ℕ, i < r → c (i + 1) % 2 = 0)
    (hodd : ∀ i : ℕ, i < r → d (i + 1) % 2 = 1) :
    x_seq (c 0 * t + d 0) r = c r * t + d r := by
  have hs : ∀ j : ℕ, j ≤ r →
      x_seq (c 0 * t + d 0) j = c j * t + d j := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [x_seq]
    | succ j ih =>
      intro hle
      have hjr : j < r := by omega
      change (F^[j + 1]) (c 0 * t + d 0) =
        c (j + 1) * t + d (j + 1)
      rw [Function.iterate_succ_apply']
      change F (x_seq (c 0 * t + d 0) j) =
        c (j + 1) * t + d (j + 1)
      rw [ih (by omega)]
      exact affine_F_step (c j) (d j)
        (c (j + 1)) (d (j + 1)) (e j) t
        (hcoeff j hjr) (hconst j hjr)
        (heven j hjr) (hodd j hjr)
  exact hs r le_rfl

/-- An affine certificate with final coefficient no greater and
final offset strictly smaller proves uniform accelerated descent. -/
theorem affine_trace_descent
    (c d e : ℕ → ℕ) (r t : ℕ)
    (hcoeff : ∀ i : ℕ, i < r →
        3 * c i = 2 ^ e i * c (i + 1))
    (hconst : ∀ i : ℕ, i < r →
        3 * d i + 1 = 2 ^ e i * d (i + 1))
    (heven : ∀ i : ℕ, i < r → c (i + 1) % 2 = 0)
    (hodd : ∀ i : ℕ, i < r → d (i + 1) % 2 = 1)
    (hcoef_le : c r ≤ c 0)
    (hoff_lt : d r < d 0) :
    x_seq (c 0 * t + d 0) r < c 0 * t + d 0 := by
  rw [affine_trace_exact c d e r t hcoeff hconst heven hodd]
  have hmul : c r * t ≤ c 0 * t :=
    Nat.mul_le_mul_right t hcoef_le
  omega

/-- Convert ANY certified contracting affine trace into the exact
GARCD arithmetic DESC inequality, reusing GARCD-4.2. -/
theorem affine_trace_DESC
    (c d e : ℕ → ℕ) (r t : ℕ)
    (hcoeff : ∀ i : ℕ, i < r →
        3 * c i = 2 ^ e i * c (i + 1))
    (hconst : ∀ i : ℕ, i < r →
        3 * d i + 1 = 2 ^ e i * d (i + 1))
    (heven : ∀ i : ℕ, i < r → c (i + 1) % 2 = 0)
    (hodd : ∀ i : ℕ, i < r → d (i + 1) % 2 = 1)
    (hr : 1 ≤ r)
    (hcoef_le : c r ≤ c 0)
    (hoff_lt : d r < d 0) :
    ∃ r' : ℕ, 1 ≤ r' ∧
      (C_orbit (c 0 * t + d 0) r' : ℤ) <
        ((2 : ℤ) ^ A_orbit (c 0 * t + d 0) r' -
          (3 : ℤ) ^ r') * ((c 0 * t + d 0) : ℤ) := by
  refine ⟨r, hr, ?_⟩
  exact (GARCD_4_2_Exact_Descent_Iff (c 0 * t + d 0) r).mp
    (affine_trace_descent c d e r t hcoeff hconst heven hodd
      hcoef_le hoff_lt)

end GARCD

#print axioms GARCD.affine_F_step
#print axioms GARCD.affine_trace_exact
#print axioms GARCD.affine_trace_descent
#print axioms GARCD.affine_trace_DESC

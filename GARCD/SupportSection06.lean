import GARCD.SupportSection05

open scoped BigOperators
open Finset Real Filter



/-!

# GARCD: strengthened Hausdorff tail-cost estimates (research candidate)



Intended placement: append this file AFTER the final `end GARCD` in

`GARCD_Modules_1_6_Hausdorff_Bridge_Expanded.lean`, or import that module

in a configured Mathlib Lake project.



The underlying finite negative-binomial lemma `sum_choose_mul_pow_le` is

provided by the preceding module. This file adds a *new, stronger* finite

exponential-moment comparison, and an infinite geometric-tail lemma.



STATUS: NOT COMPILED; the authors have not run a Lean kernel on this source.

The final unconditional theorem on the actual 2-adic exceptional set is

NOT declared here; the length/count and ENNReal-conversion arguments still

need verified proof terms. No `sorry`, new `axiom`, or artificial `True`

substitution is used.

-/



namespace GARCD



open Finset Filter



/-- The coefficient count of compositions of `A` into `r` positive parts,

weighted by the cost `q ^ (A+1)`. The coefficient is zero when `A < r`.

This is a purely finite sum and is not silently identified with the

original `LowValuationTailCylinder` total cost. -/

noncomputable def finiteLevelBinomialCost (r B : ℕ) (q : ℝ) : ℝ :=

  ∑ A ∈ Finset.Ico r (B + 1),

    (Nat.choose (A - 1) (r - 1) : ℝ) * q ^ (A + 1)



/-- Each term of the finite level sum is bounded by the corresponding

exponentially tilted term when `A ≤ B` and `t ≥ 1`.



  choose(A-1,r-1) * (t*x)^(A+1)

       ≤ (t*x) * t^B * choose(A-1,r-1) * x^A.

-/

theorem chernoff_binomial_term_bound

    (A B r : ℕ) (hAB : A ≤ B)

    {x t : ℝ} (hx : 0 ≤ x) (ht : 1 ≤ t) :

    (Nat.choose (A - 1) (r - 1) : ℝ) * (t * x) ^ (A + 1)

      ≤ (t * x) * t ^ B *

          ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

  have hpow : t ^ A ≤ t ^ B := pow_le_pow_right₀ ht hAB

  have htx : 0 ≤ t * x := mul_nonneg (by linarith) hx

  have hc : 0 ≤ (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A := by

    positivity

  calc

    (Nat.choose (A - 1) (r - 1) : ℝ) * (t * x) ^ (A + 1)

        = (t * x) * t ^ A *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

          rw [pow_succ, mul_pow]

          ring

    _ ≤ (t * x) * t ^ B *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

      exact mul_le_mul_of_nonneg_right

        (mul_le_mul_of_nonneg_left hpow htx) hc



/-- Finite negative-binomial Chernoff bound.



  Σ_{r≤A≤B} choose(A-1,r-1) (t*x)^(A+1)

  ≤ (t*x) t^B (x/(1-x))^r.



The underlying finite negative-binomial bound is precisely the

`sum_choose_mul_pow_le` theorem from GARCD Modules 1–6.

-/

theorem finiteLevelBinomialCost_chernoff

    {r B : ℕ} (hr : 1 ≤ r)

    {x t : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (ht : 1 ≤ t) :

    finiteLevelBinomialCost r B (t * x)

      ≤ (t * x) * t ^ B * (x / (1 - x)) ^ r := by

  let S : Finset ℕ := Finset.Ico r (B + 1)

  have hTerm :

      ∑ A ∈ S,

          (Nat.choose (A - 1) (r - 1) : ℝ) * (t * x) ^ (A + 1)

      ≤ ∑ A ∈ S,

          (t * x) * t ^ B *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

    apply Finset.sum_le_sum

    intro A hA

    have hA_le : A ≤ B := Nat.le_of_lt_succ (Finset.mem_Ico.mp hA).2

    exact chernoff_binomial_term_bound A B r hA_le hx ht

  have hpart := sum_choose_mul_pow_le (r := r) (bound := B) hr hx hx1

  have hden : 0 < (1 - x) ^ r := pow_pos (by linarith) r

  have hpart_le :

      (∑ A ∈ S, (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A)

        ≤ (x / (1 - x)) ^ r := by

    have hbase :

        (∑ A ∈ S, (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A)

          ≤ x ^ r / (1 - x) ^ r := (le_div_iff₀ hden).2 hpart

    calc

      _ ≤ x ^ r / (1 - x) ^ r := hbase

      _ = (x / (1 - x)) ^ r := by rw [div_pow]

  have hconst : 0 ≤ (t * x) * t ^ B := by positivity

  calc

    finiteLevelBinomialCost r B (t * x)

        ≤ ∑ A ∈ S, (t * x) * t ^ B *

            ((Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := hTerm

    _ = ((t * x) * t ^ B) *

          (∑ A ∈ S, (Nat.choose (A - 1) (r - 1) : ℝ) * x ^ A) := by

      rw [Finset.mul_sum]

    _ ≤ ((t * x) * t ^ B) * (x / (1 - x)) ^ r :=

      mul_le_mul_of_nonneg_left hpart_le hconst

    _ = (t * x) * t ^ B * (x / (1 - x)) ^ r := by ring



/-- A reusable *actual convergence* theorem: any nonnegative real

sequence with a geometric upper bound has a vanishing sum over the

moving tails. Unlike the original project this is unconditional given

the explicitly stated, checkable per-level estimates. -/

theorem real_geometric_majorant_tail_tendsto

    (f : ℕ → ℝ) (K ρ : ℝ)

    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)

    (hf0 : ∀ r, 0 ≤ f r)

    (hf : ∀ r, f r ≤ K * ρ ^ r) :

    Filter.Tendsto (fun R : ℕ => ∑' k : ℕ, f (k + R))

      Filter.atTop (nhds 0) := by

  have hgeom : Summable (fun r : ℕ => ρ ^ r) :=

    summable_geometric_of_lt_one hρ0 hρ1

  have hmajor : Summable (fun r : ℕ => K * ρ ^ r) :=

    hgeom.mul_left K

  have hsum : Summable f := by

    apply Summable.of_nonneg_of_le hf0 hf hmajor

  exact tendsto_sum_nat_add f



/-- For clarity: this is the precise *missing* theorem on the real

weighted binomial level costs. Its original mathematical content is

retained, but this is a statement alone, not a certificate of proof.



For 1 < β < 2 and DimBound β < s < 1, put q = 2^(-s),

  x = (β-1)/β, t = q/x, rho = (β-1)*t^β.

One must derive `finiteLevelBinomialCost r ⌊β*r⌋ q ≤ q*rho^r`

from `finiteLevelBinomialCost_chernoff` and real-power monotonicity.

Then connect the actual indexed `tsum` to the binomial coefficient count.

-/

noncomputable def GARCD_Hausdorff_LevelCost_Goal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    ∃ (q ρ : ℝ), 0 ≤ q ∧ 0 ≤ ρ ∧ ρ < 1 ∧

      ∀ (r : ℕ), 1 ≤ r →

        finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) q

          ≤ q * ρ ^ r



/-- The genuine remaining theorem, on the actual GARCD 2-adic

exceptional set, is NOT replaced by a weaker claim. Its proof still

needs the finite-level combinatorial enumeration, real/ENNReal power

conversion and the final limit. -/

noncomputable def GARCD_Hausdorff_Actual_TailCost_Goal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    Filter.Tendsto

      (fun R : ℕ => ∑' i : LowValuationCoverIndex β,

        Metric.ediam (LowValuationTailCylinder β R i) ^ s)

      Filter.atTop (nhds 0)









end GARCD

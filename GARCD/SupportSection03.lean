import GARCD.SupportSection02

open scoped BigOperators
open Finset Real Filter







/-! ### 2026-11-09 exact specification audit (NOT theorem claims)



The full natural-language proofs of both propositions are in

GARCD_Analytic_Completion_2026-11-09.md.



Neither definition below proves the proposition. These are immutable,

source-faithful targets for subsequent Lean formalization.

In particular they are NOT redefined as `True`, and neither sorry nor

an unproved axiom is introduced.

-/



namespace GARCD



/-- Exact original finite negative-binomial inequality to formalize. -/

def GARCD_NegBinomial_Finite_Bound_Target : Prop :=

  ∀ (r bound : ℕ) (x : ℝ),

    1 ≤ r → 0 ≤ x → x < 1 →

    (∑ s ∈ Finset.Ico r (bound + 1),

      (Nat.choose (s - 1) (r - 1) : ℝ) * x ^ s) * (1 - x) ^ r ≤ x ^ r



/-- Actual 2-adic exceptional-set dimension bound, not just a formula

for `DimBound`. The project still needs a formal proof term of this type. -/

def GARCD_Hausdorff_Actual_Dimension_Target : Prop :=

  ∀ β : ℝ, 1 < β → β < 2 →

    MeasureTheory.dimH (LowValuationExceptionSet β) ≤

      ENNReal.ofReal (DimBound β)







end GARCD

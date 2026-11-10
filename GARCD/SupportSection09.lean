import GARCD.SupportSection08

open scoped BigOperators
open Finset Real Filter





/-!

GARCD actual-cover accounting / explicit remaining kernel obligations.



Append to the PREVIOUS monolithic source (where namespace GARCD is closed),

not to this cut-code-only standalone source. This is a research artifact,

NOT a successful Lean build certification. No `sorry`, `axiom`, or weakenings.



The exact original target is retained. The abstract implications stated

below are all mathematically valid conditional implications, but the

original-index transfer and optimized exponent estimate are *not* declared

as completed theorems.

-/



namespace GARCD



/-- Stage A: the original set's true level-`r` weighted diameter cost. -/

noncomputable def GARCDRealLevelCost (β s : ℝ) (r : ℕ) : ENNReal :=

  ∑' i : LowValuationCoverIndex β,

    if i.val.1 = r then

      Metric.ediam (TwoAdicValuationCylinder i.val.2) ^ s

    else 0



/-- Stage B: the intended explicit combinatorial majorant, in `ENNReal`.

    This is the actual finite binomial expression, not an artificial

    replacement by `True`. -/

noncomputable def GARCDBinomialMajorant (β s : ℝ) (r : ℕ) : ENNReal :=

  ∑ A ∈ Finset.Ico r (Nat.floor (β * (r : ℝ)) + 1),

    (Nat.choose (A - 1) (r - 1) : ENNReal) *

      (ENNReal.ofReal ((2 : ℝ) ^ (-s))) ^ (A + 1)



/-- Exact remaining original-index bookkeeping statement.  An unconditional

    theorem `∀ β s r, ...` is NOT yet kernel-proved; the statement is kept

    as a Prop to be proved using `Composition` and finite subtype sums. -/

def ActualLevelVsBinomialGoal : Prop :=

  ∀ (β s : ℝ) (r : ℕ),

    1 < β → β < 2 → 0 < s → 1 ≤ r →

    GARCDRealLevelCost β s r ≤ GARCDBinomialMajorant β s r



/-- Optimized weighted binomial estimate, again kept as a real target.

  rho(beta,s) = (beta-1) * ((beta/(beta-1))*2^(-s))^beta.

  For DimBound beta < s < 1 this is strictly below 1.

  The real-to-ENNReal cast is an important part of this target. -/

def OptimizedBinomialEnvelopeGoal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    ∃ (q ρ : NNReal), ρ < 1 ∧

      ∀ r : ℕ, 1 ≤ r →

        GARCDBinomialMajorant β s r ≤

          (q : ENNReal) * (ρ : ENNReal) ^ r



/-- The final goal must have NO new hypotheses in the declaration.

    This declaration is a proposition and is not misrepresented as a proof. -/

def UnconditionalActualHausdorffGoal : Prop :=

  ∀ β : ℝ, 1 < β → β < 2 →

    MeasureTheory.dimH (LowValuationExceptionSet β) ≤

      ENNReal.ofReal (DimBound β)



/-- An already established conditional bridge from the previous source,

    applied *without modifying the original exceptional set*. -/

theorem actualMeasure_zero_from_checked_envelope

    (β s : ℝ) (K ρ : NNReal) (hρ : ρ < 1)

    (hOriginal : ∀ R : ℕ,

       GARCDActualTailCost β s R ≤

         (K : ENNReal) * (ρ : ENNReal) ^ R) :

    (MeasureTheory.Measure.hausdorffMeasure s)

       (LowValuationExceptionSet β) = 0 := by

  exact actualHausdorffMeasure_zero_of_geometric_envelope

    β s K ρ hρ hOriginal









end GARCD

import GARCD.SupportSection06

open scoped BigOperators
open Finset Real Filter







/-!

GARCD extension: one-parameter geometric envelope -> ACTUAL 2-adic

Hausdorff measure zero.



INTEGRATION: append this source AFTER the preceding monolithic

GARCD_Modules_1_6_TailCost_Research_All_In_One.lean.



IMPORTANT: `hEnvelope` is an explicit mathematical hypothesis; it is NOT

obtained from the finite binomial inequality in this file.  This bridge

is NOT the unconditional Hausdorff-dimension theorem.



This source is an uncompiled formalization candidate. No `sorry` or `axiom`.

-/



namespace GARCD



open Filter



/-- A convenient name for the true sum of diameter powers of GARCD's

    *actual* countable tail cylinders. -/

noncomputable def GARCDActualTailCost (β s : ℝ) (R : ℕ) : ENNReal :=

  ∑' i : LowValuationCoverIndex β,

    Metric.ediam (LowValuationTailCylinder β R i) ^ s



/-- Once a geometric envelope with `rho < 1` is available, the ACTUAL

    cover cost tends to zero.  The finite positive constant is required:

    multiplication by `∞` at zero is not continuous in `ENNReal`. -/

theorem actualTailCost_tendsto_of_geometric_envelope

    (β s : ℝ) (K ρ : NNReal) (hρ : ρ < 1)

    (hEnvelope : ∀ R : ℕ,

      GARCDActualTailCost β s R ≤ (K : ENNReal) * (ρ : ENNReal) ^ R) :

    Filter.Tendsto (GARCDActualTailCost β s)

      Filter.atTop (nhds 0) := by

  have hρe : (ρ : ENNReal) < 1 := by exact_mod_cast hρ

  have hp : Filter.Tendsto

      (fun R : ℕ => (ρ : ENNReal) ^ R)

      Filter.atTop (nhds 0) :=

    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρe

  have hK : (K : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top

  have hMaj : Filter.Tendsto

      (fun R : ℕ => (K : ENNReal) * (ρ : ENNReal) ^ R)

      Filter.atTop (nhds 0) := by

    simpa using (ENNReal.Tendsto.const_mul hp (Or.inr hK))

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le

    tendsto_const_nhds hMaj

    (fun R => bot_le)

    hEnvelope



/-- A proof-bearing consequence about the original exceptional set.

    No weakened definition of the set is introduced. -/

theorem actualHausdorffMeasure_zero_of_geometric_envelope

    (β s : ℝ) (K ρ : NNReal) (hρ : ρ < 1)

    (hEnvelope : ∀ R : ℕ,

      GARCDActualTailCost β s R ≤ (K : ENNReal) * (ρ : ENNReal) ^ R) :

    (MeasureTheory.Measure.hausdorffMeasure s)

      (LowValuationExceptionSet β) = 0 := by

  apply lowValuation_hausdorffMeasure_zero_of_exact_tail_cost

  simpa [GARCDActualTailCost] using

    actualTailCost_tendsto_of_geometric_envelope

      β s K ρ hρ hEnvelope



/-- The target is explicitly retained as a PROPOSITION and no proof is

    claimed.  At the analytic optimum, one expects constants K and rho

    to be obtained using the finite Chernoff bound, exact composition

    counts and the 2-adic diameter inequality. -/

def ActualGeometricEnvelopeGoal : Prop :=

  ∀ (β s : ℝ), 1 < β → β < 2 → DimBound β < s → s < 1 →

    ∃ (K ρ : NNReal), ρ < 1 ∧

      ∀ R : ℕ,

        GARCDActualTailCost β s R ≤

          (K : ENNReal) * (ρ : ENNReal) ^ R








end GARCD

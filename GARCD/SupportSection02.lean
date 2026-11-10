import GARCD.SupportSection01

open scoped BigOperators
open Finset Real Filter







/-! ===== Source: GARCD_Hausdorff_Set_And_Bridge.lean ===== -/

/-!

Module 3 / §13.1 enhancement: THIS FILE DEFINES THE ACTUAL

2-adic exceptional set and gives the final Mathlib Hausdorff-measure-to-

dimension bridge. The missing analytical covering lemma is NOT proved here.



No sorry, axiom, or placeholder theorem is introduced. A definition of an

open conjectural proposition is not a proof of that proposition.

Status: proof development draft, not compiled in this environment.

-/



namespace GARCD



/-- Exact cylinder for a finite *positive* Syracuse valuation word,

    expressed via the residue map ℤ₂ → ZMod 2^(A+1).



The congruence is the full exact valuation congruence

    x ≡ 3^(-p) (2^A - C(w))   (mod 2^(A+1)),

not the weaker congruence modulo 2^A. -/

noncomputable def TwoAdicValuationCylinder (w : List ℕ) : Set ℤ_[2] :=

  {z : ℤ_[2] |

    (∀ a ∈ w, 1 ≤ a) ∧

    (PadicInt.toZModPow (A_total w + 1) z : ZMod (2 ^ (A_total w + 1))) =

      ((3 : ZMod (2 ^ (A_total w + 1))) ^ w.length)⁻¹ *

        ((2 : ZMod (2 ^ (A_total w + 1))) ^ A_total w -

          (C_p w : ZMod (2 ^ (A_total w + 1))))}



/-- Exact exceptional set from §13.1: odd 2-adic integers with

    A_r(z) <= β r along infinitely many prefix lengths r.



No natural-number orbit is inferred from membership here: z is 2-adic.

-/

noncomputable def LowValuationExceptionSet (β : ℝ) : Set ℤ_[2] :=

  {z : ℤ_[2] |

    PadicInt.toZMod z = (1 : ZMod 2) ∧

    ∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧

      ∃ w : List ℕ, w.length = r ∧

        (A_total w : ℝ) ≤ β * (r : ℝ) ∧

        z ∈ TwoAdicValuationCylinder w}



/-- The actual target of §13.1, NOT the numerical simplification of DimBound.

    This is a Prop definition, and asserts no theorem at this stage. -/

noncomputable def GARCD_13_7_Actual_Hausdorff_Goal (β : ℝ) : Prop :=

  1 < β → β < 2 →

    MeasureTheory.dimH (LowValuationExceptionSet β) ≤

      ENNReal.ofReal (DimBound β)



/-- The established generic Mathlib bridge from zero s-dimensional

    Hausdorff measure to dimension at most s. The essential open step is

    proving the hypothesis for the actual exceptional set. -/

theorem GARCD_13_7_Hausdorff_measure_suffices

    (E : Set ℤ_[2]) (s : NNReal)

    (hzero : (MeasureTheory.Measure.hausdorffMeasure (s : ℝ)) E = 0) :

    MeasureTheory.dimH E ≤ (s : ENNReal) := by

  apply MeasureTheory.dimH_le_of_hausdorffMeasure_ne_top

  rw [hzero]

  exact zero_ne_top



-- MISSING, INTENTIONALLY NOT CLAIMED AS A THEOREM:

--   β in (1,2), every s > DimBound(β) has

--   (hausdorffMeasure s) (LowValuationExceptionSet β) = 0.

-- This requires proving the cylinder diameter and a UNIFORM

-- exponential cover estimate, then the Hausdorff-Cantelli limsup argument.

-- Neither Theorem_13_7_Hausdorff_Dimension_Formula in the original

-- integrated file nor the bridge above proves this key estimate.



end GARCD

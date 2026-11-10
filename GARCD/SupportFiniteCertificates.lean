import GARCD.Module06

/-! ===== Source: GARCD_Extra_Finite_Certificates.lean ===== -/

/-!

GARCD Module 5 enhancement: exhaustive p <= 16 certificates.



STATUS: SOURCE CANDIDATE, NOT LEAN-BUILD-VERIFIED in this environment.

These are genuine unbounded-formula finite DECISION claims in kernel mode,

not axioms, sorry placeholders, or mere counting identities.



WARNING: The 3,268,760-word case can exceed practical elaboration/kernel

budgets. Run each theorem separately; do not replace `decide +kernel` with

`native_decide` without explicitly accepting a larger trust base.

-/



namespace GARCD



set_option maxHeartbeats 0



/-! The two smallest certificates exist in the original file. -/



/-- All 5,005 compositions of length 10, sum 16. -/

theorem GARCD_31_p10_A16_complete :

    (compositionsPos 10 16).length = 5005 ∧

    checkNoCycleHits 10 16 = true := by

  decide +kernel



/-- All 19,448 compositions of length 11, sum 18. -/

theorem GARCD_31_p11_A18_complete :

    (compositionsPos 11 18).length = 19448 ∧

    checkNoCycleHits 11 18 = true := by

  decide +kernel



/-- All 125,970 compositions of length 13, sum 21. -/

theorem GARCD_31_p13_A21_complete :

    (compositionsPos 13 21).length = 125970 ∧

    checkNoCycleHits 13 21 = true := by

  decide +kernel



/-- All 497,420 compositions of length 14, sum 23. -/

theorem GARCD_31_p14_A23_complete :

    (compositionsPos 14 23).length = 497420 ∧

    checkNoCycleHits 14 23 = true := by

  decide +kernel



/-- All 817,190 compositions of length 15, sum 24. -/

theorem GARCD_31_p15_A24_complete :

    (compositionsPos 15 24).length = 817190 ∧

    checkNoCycleHits 15 24 = true := by

  decide +kernel



/-- All 3,268,760 compositions of length 16, sum 26. -/

theorem GARCD_31_p16_A26_complete :

    (compositionsPos 16 26).length = 3268760 ∧

    checkNoCycleHits 16 26 = true := by

  decide +kernel



/-- A conjunction covering all 4,734,620 candidates.  Pending kernel builds

    of the six new per-p certificates. -/

theorem GARCD_31_all_eight_pairs_complete :

    checkNoCycleHits 5 8 = true ∧

    checkNoCycleHits 8 13 = true ∧

    checkNoCycleHits 10 16 = true ∧

    checkNoCycleHits 11 18 = true ∧

    checkNoCycleHits 13 21 = true ∧

    checkNoCycleHits 14 23 = true ∧

    checkNoCycleHits 15 24 = true ∧

    checkNoCycleHits 16 26 = true := by

  have h₀ := GARCD_31_Exhaustive_Certificate_p5_p8

  exact ⟨h₀.2.1, h₀.2.2.2,

    GARCD_31_p10_A16_complete.2, GARCD_31_p11_A18_complete.2,

    GARCD_31_p13_A21_complete.2, GARCD_31_p14_A23_complete.2,

    GARCD_31_p15_A24_complete.2, GARCD_31_p16_A26_complete.2⟩



end GARCD






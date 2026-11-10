import GARCD.SupportCert10
import GARCD.SupportCert11
import GARCD.SupportCert13
import GARCD.SupportCert14
import GARCD.SupportCert15
import GARCD.SupportCert16

namespace GARCD

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

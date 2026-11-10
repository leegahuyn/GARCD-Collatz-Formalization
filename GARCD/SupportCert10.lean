import GARCD.Module06

namespace GARCD

set_option maxHeartbeats 0

/-- All 5,005 compositions of length 10, sum 16. -/

theorem GARCD_31_p10_A16_complete :

    (compositionsPos 10 16).length = 5005 ∧

    checkNoCycleHits 10 16 = true := by

  decide +kernel

end GARCD

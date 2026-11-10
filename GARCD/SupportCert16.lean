import GARCD.Module06

namespace GARCD

set_option maxHeartbeats 0

/-- All 3,268,760 compositions of length 16, sum 26. -/

theorem GARCD_31_p16_A26_complete :

    (compositionsPos 16 26).length = 3268760 ∧

    checkNoCycleHits 16 26 = true := by

  decide +kernel

end GARCD

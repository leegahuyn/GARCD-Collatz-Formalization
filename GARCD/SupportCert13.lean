import GARCD.Module06

namespace GARCD

set_option maxHeartbeats 0

/-- All 125,970 compositions of length 13, sum 21. -/

theorem GARCD_31_p13_A21_complete :

    (compositionsPos 13 21).length = 125970 ∧

    checkNoCycleHits 13 21 = true := by

  decide +kernel

end GARCD

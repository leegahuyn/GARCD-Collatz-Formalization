import GARCD.Module06

namespace GARCD

set_option maxHeartbeats 0

/-- All 497,420 compositions of length 14, sum 23. -/

theorem GARCD_31_p14_A23_complete :

    (compositionsPos 14 23).length = 497420 ∧

    checkNoCycleHits 14 23 = true := by

  decide +kernel

end GARCD

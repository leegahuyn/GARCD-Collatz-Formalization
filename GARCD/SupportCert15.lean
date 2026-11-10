import GARCD.Module06

namespace GARCD

set_option maxHeartbeats 0

/-- All 817,190 compositions of length 15, sum 24. -/

theorem GARCD_31_p15_A24_complete :

    (compositionsPos 15 24).length = 817190 ∧

    checkNoCycleHits 15 24 = true := by

  decide +kernel

end GARCD

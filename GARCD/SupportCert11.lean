import GARCD.Module06

namespace GARCD

set_option maxHeartbeats 0

/-- All 19,448 compositions of length 11, sum 18. -/

theorem GARCD_31_p11_A18_complete :

    (compositionsPos 11 18).length = 19448 ∧

    checkNoCycleHits 11 18 = true := by

  decide +kernel

end GARCD

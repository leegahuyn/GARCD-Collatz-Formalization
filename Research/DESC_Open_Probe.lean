/-! RESEARCH ONLY: intentionally expected to fail until DESC is proved. -/
import GARCD

namespace GARCD

theorem GARCD_DESC_Unconditional_Probe : DESCArithmeticProp := by
  first
  | exact?
  | aesop

-- Only valid if the preceding theorem was genuinely proven.
theorem GARCD_Collatz_Unconditional_Probe : CollatzConjectureProp := by
  exact (Theorem_10_2_1_DESC_Iff_Arithmetic_Inequality.symm.trans
    Theorem_10_2_2_DESC_Iff_Collatz_Conjecture).mp
      GARCD_DESC_Unconditional_Probe

end GARCD

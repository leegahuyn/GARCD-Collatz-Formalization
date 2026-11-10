import GARCD.Module05
import Mathlib.Data.Nat.Choose.Sum

namespace GARCD

private theorem compositionsPos_len_rec (p A : ℕ) (h : p + 1 ≤ A) :
    (compositionsPos (p + 1) A).length =
      ∑ d ∈ Finset.range (A - p),
        (compositionsPos p (A - (d + 1))).length := by
  change (if A < p + 1 then ([] : List (List ℕ)) else
    (List.range (A - p)).flatMap (fun d =>
      (compositionsPos p (A - (d + 1))).map (fun tl => (d + 1) :: tl))).length = _
  simp only [if_neg (show ¬ A < p + 1 by omega),
    List.length_flatMap, List.length_map]
  rw [← List.sum_toFinset _ (List.nodup_range)]
  simp

/-- An exact polynomial-size binomial expression for the count of all
positive exponent words, avoiding construction of millions of list values. -/
theorem compositionsPos_length_eq_choose (p A : ℕ)
    (hp : 1 ≤ p) (hpa : p ≤ A) :
    (compositionsPos p A).length = (A - 1).choose (p - 1) := by
  induction p generalizing A with
  | zero => omega
  | succ p ih =>
      by_cases hp0 : p = 0
      · subst p
        have hsum : (compositionsPos 1 A).length =
            ∑ d ∈ Finset.range A, (if A - (d + 1) = 0 then 1 else 0) := by
          rw [compositionsPos_len_rec 0 A (by omega)]
          simp only [Nat.sub_zero]
          apply Finset.sum_congr rfl
          intro d hd
          cases h : A - (d + 1) with
          | zero => simp [compositionsPos, h]
          | succ n => simp [compositionsPos, h]
        rw [hsum]
        have heq : A = (A - 1) + 1 := by omega
        rw [heq, Finset.sum_range_succ]
        have hzero : (∑ d ∈ Finset.range (A - 1),
            if A - 1 + 1 - (d + 1) = 0 then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          have hd_lt : d < A - 1 := Finset.mem_range.mp hd
          have hne : A - 1 + 1 - (d + 1) ≠ 0 := by omega
          simp only [if_neg hne]
        rw [hzero]
        simp [show A - ((A - 1) + 1) = 0 by omega]
      · have hp1 : 1 ≤ p := by omega
        rw [compositionsPos_len_rec p A (by omega)]
        have hsum :
            (∑ d ∈ Finset.range (A - p),
              (compositionsPos p (A - (d + 1))).length) =
            ∑ d ∈ Finset.range (A - p),
              (A - (d + 1) - 1).choose (p - 1) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd_lt : d < A - p := Finset.mem_range.mp hd
          exact ih (A - (d + 1)) hp1 (by omega)
        rw [hsum]
        have hreflect :
            (∑ d ∈ Finset.range (A - p),
              (A - (d + 1) - 1).choose (p - 1)) =
            ∑ d ∈ Finset.range (A - p), (d + (p - 1)).choose (p - 1) := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro d hd
          have hd_lt : d < A - p := Finset.mem_range.mp hd
          congr 1
          omega
        rw [hreflect]
        have hn : A - p = (A - p - 1) + 1 := by omega
        rw [hn, Nat.sum_range_add_choose]
        congr 1 <;> omega

#print axioms GARCD.compositionsPos_length_eq_choose

end GARCD

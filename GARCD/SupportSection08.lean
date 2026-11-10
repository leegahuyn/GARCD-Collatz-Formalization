import GARCD.SupportSection07

open scoped BigOperators
open Finset Real Filter







/-! ===== 2026-11-09 ENHANCEMENT: verified target types, uncompiled count bridge candidates ===== -/

/-!

GARCD / positive valuation words as compositions / stars and bars

2026-11-09: self-contained Lean4 + Mathlib4 FORMALIZATION CANDIDATE.



STATUS: The environment where this was authored has no Lean/lake binary.

This file is not a claim of kernel verification. All theorem goals in this

file retain their intended mathematical type, and no axiom or sorry is used.



Counting source: Mathlib.Combinatorics.Enumerative.Composition, where

`compositionEquiv` and `compositionAsSetEquiv` supply the correspondence

between positive compositions and the inner cut points. This independent

cut-point model counts the appropriate codes exactly. An explicit proposed equivalence to the ORIGINAL GARCD `List ℕ` subtype

is included below; this has NOT been compiled or kernel-checked.

-/



open Finset

open scoped BigOperators



namespace GARCD

namespace HausdorffCount20261109



/-- An `r`-block positive composition of `A` is encoded by exactly `r-1`

    internal cut points in `Fin (A-1)`.  This definition is an exact finite

    *code model*, not a replacement for GARCD's original word type. -/

def CutCode (A r : ℕ) :=
  {s : Finset (Fin (A - 1)) // s.card = r - 1}

noncomputable instance (A r : ℕ) : Fintype (CutCode A r) := Fintype.ofFinite _



/-- The code model has the correct binomial cardinality. -/

theorem cutCode_card (A r : ℕ) :

    Fintype.card (CutCode A r) = Nat.choose (A - 1) (r - 1) := by

  classical

  let s : Finset (Finset (Fin (A - 1))) :=

    Finset.powersetCard (r - 1) (Finset.univ : Finset (Fin (A - 1)))

  let e : CutCode A r ≃ s :=

    { toFun := fun c =>

        ⟨c.1, (Finset.mem_powersetCard).2

          ⟨Finset.subset_univ c.1, c.2⟩⟩

      invFun := fun c =>

        ⟨c.1, ((Finset.mem_powersetCard).1 c.2).2⟩

      left_inv := by

        intro c

        cases c

        rfl

      right_inv := by

        intro c

        cases c

        rfl }

  calc

    Fintype.card (CutCode A r) = Fintype.card s := Fintype.card_congr e

    _ = s.card := Fintype.card_coe s

    _ = Nat.choose (A - 1) (r - 1) := by

      dsimp [s]

      simpa using

        (Finset.card_powersetCard (r - 1)

          (Finset.univ : Finset (Fin (A - 1))))



/-- Weighted cost for the cut-code model.  Every word with total exponent

    `A` contributes exactly `q^(A+1)` to the *upper bound* for its cylinder

    diameter to power `s` once `q=2^(-s)` is substituted. -/

noncomputable def cutCodeCost (A r : ℕ) (q : ENNReal) : ENNReal :=

  ∑ _ : CutCode A r, q ^ (A + 1)



/-- Exact finite binomial cost identity, not merely an inequality. -/

theorem cutCodeCost_eq_choose (A r : ℕ) (q : ENNReal) :

    cutCodeCost A r q =

      (Nat.choose (A - 1) (r - 1) : ENNReal) * q ^ (A + 1) := by

  classical

  unfold cutCodeCost

  simp [cutCode_card, nsmul_eq_mul]



/-- The exact binomial *finite* upper bound for a level with exponent

    cutoff `B` is now a finite sum over already-counted cut codes. -/

noncomputable def cutLevelCost (r B : ℕ) (q : ENNReal) : ENNReal :=

  ∑ A ∈ Finset.Ico r (B + 1), cutCodeCost A r q



theorem cutLevelCost_eq_binomial (r B : ℕ) (q : ENNReal) :

    cutLevelCost r B q =

      ∑ A ∈ Finset.Ico r (B + 1),

        (Nat.choose (A - 1) (r - 1) : ENNReal) * q ^ (A + 1) := by

  classical

  simp only [cutLevelCost, cutCodeCost_eq_choose]



/-! ### Genuine finite-fiber aggregation, reusable for the ORIGINAL words ### -/



/-- This is not a special property of the cut-code model: for ANY finite

    collection of words with exponent sums bounded by `B`, the weighted sum

    can be regrouped by exponent sum.  The `Finset` fiberwise-sum theorem

    is supplied by Mathlib. The only input is `∀ i ∈ S, g i ≤ B`. -/

theorem finite_weighted_sum_by_exponent_fiber

    {ι : Type*} (S : Finset ι) (g : ι → ℕ)

    (weight : ℕ → ENNReal) (B : ℕ)

    (hB : ∀ i ∈ S, g i ≤ B) :

    (∑ i ∈ S, weight (g i)) =

      ∑ A ∈ Finset.Icc 0 B,

        (↑(Finset.filter (fun i => g i = A) S).card : ENNReal) *

          weight A := by

  classical

  have hmap : ∀ i ∈ S, g i ∈ Finset.Icc 0 B := by

    intro i hi

    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hB i hi⟩

  have hfiber :=

    Finset.sum_fiberwise_of_maps_to'

      S (Finset.Icc 0 B) g hmap weight

  rw [← hfiber]

  apply Finset.sum_congr rfl

  intro A hA

  simp [Finset.sum_const, nsmul_eq_mul]



/-- The ORIGINAL GARCD positive-word subtype. A map between this type and

    `CutCode A r` is the still-required original-index transfer. -/

def OriginalPositiveWord (A r : ℕ) :=

  {w : List ℕ // w.length = r ∧ w.sum = A ∧ ∀ a ∈ w, 1 ≤ a}



/-! ### Bridge to the REAL `List ℕ` valuation words ### -/



/-- A positive list word of length `r` and sum `A` is definitionally a

    Mathlib `Composition A` with the same number of blocks. This bridge

    leaves the original GARCD `A_total`, `C_p`, `LowValuationCoverIndex`

    untouched. -/

noncomputable def originalWordEquivComposition (A r : ℕ) :

    OriginalPositiveWord A r ≃ {c : Composition A // c.length = r} := by

  classical

  refine

    { toFun := ?_

      invFun := ?_

      left_inv := ?_

      right_inv := ?_ }

  · intro w

    refine ⟨{ blocks := w.1, blocks_pos := ?_, blocks_sum := w.2.2.1 }, w.2.1⟩

    intro i hi

    have h := w.2.2.2 i hi

    omega

  · intro c

    refine ⟨c.1.blocks, ⟨c.2, c.1.blocks_sum, ?_⟩⟩

    intro i hi

    exact c.1.one_le_blocks hi

  · intro w

    apply Subtype.ext

    rfl

  · intro c

    apply Subtype.ext

    apply Composition.ext

    rfl



/-- Original positive valuation words have a finite `Fintype` since they

    correspond to a filtered subtype of the finite `Composition A` type. -/

noncomputable instance originalPositiveWordFintype (A r : ℕ) :

    Fintype (OriginalPositiveWord A r) := by

  classical

  exact Fintype.ofEquiv

    {c : Composition A // c.length = r}

    (originalWordEquivComposition A r).symm



theorem originalPositiveWord_card_eq_filteredComposition (A r : ℕ) :

    Fintype.card (OriginalPositiveWord A r) =

      Fintype.card {c : Composition A // c.length = r} := by

  classical

  exact Fintype.card_congr (originalWordEquivComposition A r)



/-! ### Weighted cost for the actual original GARCD list subtype ### -/



/-- Weighted finite cost of the ORIGINAL positive `List ℕ` words, not

    the auxiliary `Finset` cut-code model. -/

noncomputable def originalPositiveWordCost (A r : ℕ) (q : ENNReal) : ENNReal :=

  ∑ _ : OriginalPositiveWord A r, q ^ (A + 1)



/-- The actual list-subtype cost is the cardinality times the constant

    cylinder-diameter envelope. This is finite arithmetic, not a `tsum`

    rearrangement of the complete GARCD index. -/

theorem originalPositiveWordCost_eq_card (A r : ℕ) (q : ENNReal) :

    originalPositiveWordCost A r q =

      (Fintype.card (OriginalPositiveWord A r) : ENNReal) * q ^ (A + 1) := by

  classical

  unfold originalPositiveWordCost

  simp [Finset.sum_const, nsmul_eq_mul]



/-- The sharp binomial weighted formula, with its exact still-needed

    fixed-length enumeration explicitly passed as a hypothesis. -/

theorem originalPositiveWordCost_eq_choose_of_count

    (A r : ℕ) (q : ENNReal)

    (hcount : Fintype.card (OriginalPositiveWord A r) =

      Nat.choose (A - 1) (r - 1)) :

    originalPositiveWordCost A r q =

      (Nat.choose (A - 1) (r - 1) : ENNReal) * q ^ (A + 1) := by

  rw [originalPositiveWordCost_eq_card, hcount]



/-- Finite original-list level-cost: aggregation over the exponent sums

    uses the genuine `OriginalPositiveWord` and never counts nonexistent

    words with zero valuations. -/

noncomputable def originalFiniteLevelCost (r B : ℕ) (q : ENNReal) : ENNReal :=

  ∑ A ∈ Finset.Ico r (B + 1), originalPositiveWordCost A r q



/-- The direct finite cost-to-binomial comparison: the only hypothesis

    is the count identity on exactly the required finite range. -/

theorem originalFiniteLevelCost_eq_binomial_of_counts

    (r B : ℕ) (q : ENNReal)

    (hcounts : ∀ A ∈ Finset.Ico r (B + 1),

      Fintype.card (OriginalPositiveWord A r) =

        Nat.choose (A - 1) (r - 1)) :

    originalFiniteLevelCost r B q = cutLevelCost r B q := by

  unfold originalFiniteLevelCost cutLevelCost

  apply Finset.sum_congr rfl

  intro A hA

  rw [originalPositiveWordCost_eq_choose_of_count A r q (hcounts A hA),

      cutCodeCost_eq_choose]



/-- Original-index/cardinality statement, kept as an explicit Prop target.

    No fake proof or `True` substitution is introduced. -/

def OriginalPositiveWordCountGoal : Prop :=

  ∀ A r : ℕ, 1 ≤ A → 1 ≤ r →

    Fintype.card (OriginalPositiveWord A r) =

      Nat.choose (A - 1) (r - 1)









end HausdorffCount20261109

end GARCD

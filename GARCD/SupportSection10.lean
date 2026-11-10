import GARCD.SupportSection09

open scoped BigOperators
open Finset Real Filter



/-!

GARCD / MODULES 1--6 : THREE REMAINING HAUSDORFF GOALS

Source-first formalization draft; Lean kernel verification NOT YET performed.



This file is intended to be appended AFTER the existing GARCD 1--6 monolithic

file (it uses OriginalPositiveWord, GARCDBinomialMajorant, and other declarations).

It contains NO sorry, admit, axiom or custom shortcut proposition.



The sections marked 'CERTIFIED ONLY AFTER BUILD' contain tactic proofs that must

be checked against the user's frozen Mathlib version. The 'Frontier' declarations

are OPEN EXACT GOALS; a `def` of the goal is never treated as its theorem.

-/



namespace GARCD

namespace ProofFirst20261109



open Finset Filter

open scoped BigOperators



/-! ## Part I : Actual positive List words and finite compositions -/



/-- The original GARCD word type (not a model word) is isomorphic to the

    Mathlib positive-composition type at the same length. -/

noncomputable def originalWordAsComposition (A r : ℕ) :

    HausdorffCount20261109.OriginalPositiveWord A r ≃

       {c : Composition A // c.length = r} :=

  HausdorffCount20261109.originalWordEquivComposition A r



/-- Mathlib's composition-as-set models each possible inner cut point in

    `Fin (A-1)`.  Positivity of A is needed when counting r blocks. -/

noncomputable def allCuts (A : ℕ) :

    Composition A ≃ Finset (Fin (A - 1)) :=

  (compositionEquiv A).trans (compositionAsSetEquiv A)




/-- Exact finite boundary-to-interior cut-cardinality bridge for positive totals.
    This is a cardinality argument independent of any Collatz dynamics. -/
private theorem compositionAsSet_cut_card_add_one
    (n : ℕ) (hn : 0 < n) (c : CompositionAsSet n) :
    (compositionAsSetEquiv n c).card + 1 = c.length := by
  classical
  unfold compositionAsSetEquiv
  simp only [Equiv.coe_fn_mk]
  have hcard : c.boundaries.card = c.length + 1 :=
    c.card_boundaries_eq_succ_length
  let inner : Finset (Fin n.succ) :=
    c.boundaries.filter (fun x => x ≠ 0 ∧ x ≠ Fin.last n)
  have hcardinner : inner.card = c.boundaries.card - 2 := by
    have h0 : (0 : Fin n.succ) ∈ c.boundaries := c.zero_mem
    have hnmem : Fin.last n ∈ c.boundaries := c.getLast_mem
    have hneq : (0 : Fin n.succ) ≠ Fin.last n := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
      omega
    have hset : inner = c.boundaries \ {0, Fin.last n} := by
      ext x
      simp only [inner, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
    rw [hset]
    have hsub : {0, Fin.last n} ⊆ c.boundaries := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact hnmem
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hneq]
  have hbij :
      ({i : Fin (n - 1) |
        (⟨1 + (i : ℕ), by omega⟩ : Fin n.succ) ∈ c.boundaries}.toFinset).card =
        inner.card := by
    apply Finset.card_bij
      (fun (i : Fin (n - 1)) _ =>
        (⟨1 + (i : ℕ), by have hi := i.isLt; omega⟩ : Fin n.succ))
    · intro i hi
      simp at hi
      simp only [inner, Finset.mem_filter]
      refine ⟨hi, ?_, ?_⟩
      · simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
        omega
      · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
        have hh := i.isLt
        omega
    · intro i₁ _ i₂ _ hval
      simp only [Fin.ext_iff] at hval ⊢
      omega
    · intro x hx
      simp only [inner, Finset.mem_filter] at hx
      obtain ⟨hm, hnz, hnl⟩ := hx
      have hxp : 0 < x.val := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at hnz
        omega
      have hxlt : x.val < n := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_last] at hnl
        have haux : x.val ≤ n := Nat.lt_succ_iff.mp x.isLt
        omega
      have hv : x.val - 1 < n - 1 := by omega
      refine ⟨⟨x.val - 1, hv⟩, ?_, ?_⟩
      · simp only [Set.mem_toFinset, Set.mem_setOf_eq]
        convert hm using 2
        omega
      · simp only [Fin.ext_iff]
        omega
  rw [hbij, hcardinner, hcard]
  have hlen : 1 ≤ c.length := by
    have h0 : (0 : Fin n.succ) ∈ c.boundaries := c.zero_mem
    have hnmem : Fin.last n ∈ c.boundaries := c.getLast_mem
    have hneq : (0 : Fin n.succ) ≠ Fin.last n := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
      omega
    have hsub : {0, Fin.last n} ⊆ c.boundaries := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact hnmem
    have hge : 2 ≤ c.boundaries.card := by
      calc
        2 = ({0, Fin.last n} : Finset (Fin n.succ)).card :=
          (Finset.card_pair hneq).symm
        _ ≤ c.boundaries.card := Finset.card_le_card hsub
    omega
  omega

/-- Exact combinatorial LENGTH identity for the cut set.

    This is the critical helper for the fixed-length count.  The proof

    expands the boundaries of a composition (including 0 and A) and removes

    these two endpoints.  It is a source-level candidate, not a built proof. -/

theorem allCuts_card_add_one (A : ℕ) (hA : 0 < A) (c : Composition A) :

    (allCuts A c).card + 1 = c.length := by
  classical
  simpa [allCuts, compositionEquiv] using
    (compositionAsSet_cut_card_add_one A hA (compositionEquiv A c))


/- Length-filtered compositions and cut-point sets of the same cardinality.

    The equivalence is constructive and has an explicit inverse. -/

/-- CORRECTED. The unrestricted r=0 bijection is false when A>0;
    see Diagnostics/NO_GO_SupportSection10_2026-11-10.md. -/
noncomputable def wordsAsFixedCuts_pos (A r : ℕ) (hA : 0 < A) (hr : 0 < r) :

    HausdorffCount20261109.OriginalPositiveWord A r ≃

       HausdorffCount20261109.CutCode A r := by

  classical

  let e := (originalWordAsComposition A r).trans

    { toFun := fun c =>

        (⟨allCuts A c.1, by

          have h := allCuts_card_add_one A hA c.1

          rw [c.2] at h

          omega⟩ : HausdorffCount20261109.CutCode A r)

      invFun := fun s =>

        (⟨(allCuts A).symm s.1, by

          have h := allCuts_card_add_one A hA ((allCuts A).symm s.1)

          rw [Equiv.apply_symm_apply] at h

          have hcard := s.2

          omega⟩ : {c : Composition A // c.length = r})

      left_inv := by

        intro c

        apply Subtype.ext

        exact Equiv.symm_apply_apply (allCuts A) c.1

      right_inv := by

        intro s

        apply Subtype.ext

        exact Equiv.apply_symm_apply (allCuts A) s.1 }

  exact e



/-- Exact count of the ORIGINAL List-valued GARCD positive valuation words.

    All lengths `r ≥ 1` and all total exponents `A ≥ 1`; no finite bound. -/

theorem originalPositiveWord_card_choose (A r : ℕ)

    (hA : 1 ≤ A) (hr : 1 ≤ r) :

    Fintype.card (HausdorffCount20261109.OriginalPositiveWord A r) =

      Nat.choose (A - 1) (r - 1) := by

  classical

  calc

    Fintype.card (HausdorffCount20261109.OriginalPositiveWord A r)

        = Fintype.card (HausdorffCount20261109.CutCode A r) :=

            Fintype.card_congr (wordsAsFixedCuts_pos A r hA hr)

    _ = Nat.choose (A - 1) (r - 1) :=

          HausdorffCount20261109.cutCode_card A r



/-- This is the EXACT original first target, not merely a counting model. -/

theorem originalPositiveWordCountGoal_proposed :

    HausdorffCount20261109.OriginalPositiveWordCountGoal := by

  intro A r hA hr

  exact originalPositiveWord_card_choose A r hA hr



/-- Consequently the existing original-list FINITE cost equals the sharp

    binomial-cost sum, without an added count hypothesis. -/

theorem originalFiniteLevelCost_eq_binomial_proposed

    (r B : ℕ) (hr : 1 ≤ r) (q : ENNReal) :

    HausdorffCount20261109.originalFiniteLevelCost r B q =

      HausdorffCount20261109.cutLevelCost r B q := by

  apply HausdorffCount20261109.originalFiniteLevelCost_eq_binomial_of_counts

  intro A hA

  have hApos : 1 ≤ A := le_trans hr (Finset.mem_Ico.mp hA).1

  exact originalPositiveWord_card_choose A r hApos hr



/-! ## Part II : Actual index to finite levels: what has been proved and

    what is still necessary to prove in Lean -/



/-- The true level-cost is the original `tsum` over the original subtype.

    Its reduction to a finite sum requires proving finite support of its

    nonempty positive cylinders; counting the cut-code model alone does

    NOT imply this. -/

noncomputable def trueLevel (β s : ℝ) (r : ℕ) : ENNReal :=

  GARCDRealLevelCost β s r



/-- This is a verified-in-principle implication, not an unconditional proof

    of the `tsum` rearrangement. A precise equality of original-index

    sums and finite-list costs remains the only hypothesis. -/

theorem original_level_le_binomial_of_exact_fibers

    (β s : ℝ) (r : ℕ) (hr : 1 ≤ r)

    (hβ : 1 < β) (hs : 0 < s)

    (hFibers : GARCDRealLevelCost β s r ≤

      HausdorffCount20261109.originalFiniteLevelCost r

        (Nat.floor (β * (r : ℝ)))

        (ENNReal.ofReal ((2 : ℝ) ^ (-s)))) :

    GARCDRealLevelCost β s r ≤ GARCDBinomialMajorant β s r := by

  calc

    GARCDRealLevelCost β s r ≤

      HausdorffCount20261109.originalFiniteLevelCost r

        (Nat.floor (β * (r : ℝ)))

        (ENNReal.ofReal ((2 : ℝ) ^ (-s))) := hFibers

    _ = HausdorffCount20261109.cutLevelCost r

          (Nat.floor (β * (r : ℝ)))

          (ENNReal.ofReal ((2 : ℝ) ^ (-s))) :=

          originalFiniteLevelCost_eq_binomial_proposed

            r (Nat.floor (β * (r : ℝ))) hr _

    _ = GARCDBinomialMajorant β s r := by

      simp [GARCDBinomialMajorant,

        HausdorffCount20261109.cutLevelCost_eq_binomial]



/-- The exact remaining actual-index statement. Its mathematical meaning

    is not weakened or replaced by True. -/

def ExactOriginalFiberTransfer : Prop :=

  ∀ (β s : ℝ) (r : ℕ), 1 < β → β < 2 → 0 < s → 1 ≤ r →

    GARCDRealLevelCost β s r ≤

      HausdorffCount20261109.originalFiniteLevelCost r

        (Nat.floor (β * (r : ℝ)))

        (ENNReal.ofReal ((2 : ℝ) ^ (-s)))



/-- Having the actual fiber transfer proves the exact second TARGET.

    The conclusion is stated without a hidden assumption; the theorem

    parameter is explicitly the still-open transfer proof. -/

theorem ActualLevelVsBinomial_of_exact_transfer

    (h : ExactOriginalFiberTransfer) : ActualLevelVsBinomialGoal := by

  intro β s r hβ hβ2 hs hr

  exact original_level_le_binomial_of_exact_fibers β s r hr hβ hs

    (h β s r hβ hβ2 hs hr)



/-! ## Part III : Optimized finite-binomial Chernoff bound -/



/-- These parameters are chosen so that

      x/(1-x) = β-1,  q = t*x, and 1 < t.

    The corresponding real geometric ratio equals

      rho = (β-1) * t^β.

    Showing rho < 1 from `DimBound β < s` requires the logarithmic

    identity and monotonicity of real exponentiation. -/

noncomputable def ChernoffX (β : ℝ) : ℝ := (β - 1) / β

noncomputable def ChernoffQ (s : ℝ) : ℝ := (2 : ℝ) ^ (-s)

noncomputable def ChernoffT (β s : ℝ) : ℝ := ChernoffQ s / ChernoffX β

noncomputable def ChernoffRho (β s : ℝ) : ℝ :=

  (β - 1) * (ChernoffT β s) ^ β



/-- Exact inequality needed to turn `finiteLevelBinomialCost_chernoff`

    into a geometric bound. It is made explicit for independent testing.

    The exponent bound uses floor(βr) ≤ βr and t≥1. -/

def ChernoffExponentGoal : Prop :=

  ∀ β s : ℝ, 1 < β → β < 2 → DimBound β < s → s < 1 →

    let x := ChernoffX β

    let q := ChernoffQ s

    let t := q / x

    let rho := ChernoffRho β s

    0 < x ∧ x < 1 ∧ 1 ≤ t ∧ 0 < rho ∧ rho < 1 ∧

    ∀ r : ℕ, 1 ≤ r →

      q * t ^ (Nat.floor (β * (r : ℝ))) * (x / (1 - x)) ^ r

        ≤ q * rho ^ r



/-- The existing proof already obtains the *finite* Chernoff inequality;

    this lemma performs its final substitution under the exact required

    numerical/exponent estimate. -/

theorem finite_binomial_cost_le_geometric_of_exponent

    (β s : ℝ) (hβ : 1 < β) (hβ2 : β < 2)

    (hs : DimBound β < s) (hs1 : s < 1)

    (hExponent : ChernoffExponentGoal)

    (r : ℕ) (hr : 1 ≤ r) :

    finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) (ChernoffQ s)

      ≤ (ChernoffQ s) * (ChernoffRho β s) ^ r := by

  obtain ⟨hx, hx1, ht, _, _, hpow⟩ :=

    hExponent β s hβ hβ2 hs hs1

  let x := ChernoffX β

  let t := ChernoffT β s

  have htx : t * x = ChernoffQ s := by

    dsimp [t, x, ChernoffT]

    have hxne : ChernoffX β ≠ 0 := ne_of_gt hx

    field_simp [hxne]

  conv_lhs => rw [← htx]

  calc

    finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) (t * x)

       ≤ (t * x) * t ^ (Nat.floor (β * (r : ℝ))) *

            (x / (1 - x)) ^ r :=

          finiteLevelBinomialCost_chernoff hr (le_of_lt hx) hx1 ht

    _ ≤ (ChernoffQ s) * (ChernoffRho β s) ^ r := by

      rw [htx]
      simpa [t, x, ChernoffT] using (hpow r hr)



/-- Real/ENNReal bridge. Here the exact cast/finite-ness assumptions are

    explicit because `ENNReal` contains `⊤` and multiplication by 0 has

    special behavior. This theorem does NOT prove the logarithmic exponent

    goal; that goal is independent and visible. -/

theorem binomial_majorant_le_ennreal_geometric_of_real

    (β s : ℝ) (r : ℕ) (hr : 1 ≤ r)

    (q ρ : NNReal)

    (hReal : finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ)))

        (ChernoffQ s) ≤ (q : ℝ) * (ρ : ℝ) ^ r)

    (hq : (q : ℝ) = ChernoffQ s)

    (hqnonneg : 0 ≤ ChernoffQ s) :

    GARCDBinomialMajorant β s r ≤ (q : ENNReal) * (ρ : ENNReal) ^ r := by

  -- Push `ENNReal.ofReal` through each nonnegative finite sum and power.

  -- `ENNReal.ofReal_sum_of_nonneg`, `ENNReal.ofReal_mul`, and

  -- `ENNReal.ofReal_pow` are the relevant Mathlib bridge lemmas.

  have hfin : GARCDBinomialMajorant β s r =

    ENNReal.ofReal (finiteLevelBinomialCost r

      (Nat.floor (β * (r : ℝ))) (ChernoffQ s)) := by

    unfold GARCDBinomialMajorant finiteLevelBinomialCost

    rw [ENNReal.ofReal_sum_of_nonneg]

    · apply Finset.sum_congr rfl

      intro A _

      have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (-s) :=
         Real.rpow_nonneg (by norm_num) (-s)
       simp [ChernoffQ, ENNReal.ofReal_pow hbase]

    · intro A _

      positivity

  rw [hfin]

  have h₁ : ENNReal.ofReal

       (finiteLevelBinomialCost r (Nat.floor (β * (r : ℝ))) (ChernoffQ s))

       ≤ ENNReal.ofReal ((q : ℝ) * (ρ : ℝ) ^ r) :=

    ENNReal.ofReal_le_ofReal hReal

  refine le_trans h₁ ?_

  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow]
  all_goals first | positivity | simp



/-! The exact three named goal declarations are unchanged in the base

    source. No theorem closing goals 2 or 3 is asserted here until their

    original-index reindexing and real-power lemmas are kernel checked. -/













end ProofFirst20261109

end GARCD

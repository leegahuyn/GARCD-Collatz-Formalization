import GARCD.DESCLyapunovEnergy

/-!
# Nested finite-prefix exceptional sets, representative divergence,
# and the precise remaining Collatz obstruction.

An exceptional prefix at depth R is an odd n >= 7 satisfying
  3*A_orbit(n,r) < 5*r for all 1 <= r <= R.

We prove a purely finite-combinatorial compactness principle:
if all these prefix sets are nested, then
"every sequence of representatives eventually exceeds every bound"
iff "the intersection of ALL the prefix sets is empty."

We then establish the precise logical equivalence
  all exceptional representative sequences escape to infinity
      ↔ GlobalFiveThirdsDriftGoal
      ↔ CollatzConjectureProp.

These are UNCONDITIONAL *equivalence* theorems; neither side is asserted.
No proof of Collatz, empty exceptional intersection, or universal
representative divergence is claimed.
-/

namespace GARCD

/-- Finite-depth failure of all 5/3 mean-valuation tests.
For R = 0 only the parity and size conditions are imposed. -/
def BadFiveThirdsPrefix (n R : ℕ) : Prop :=
  n % 2 = 1 ∧ 7 ≤ n ∧
    ∀ r : ℕ, 1 ≤ r → r ≤ R → 3 * A_orbit n r < 5 * r

/-- Prefix conditions are nested as depth grows. -/
theorem bad_five_thirds_antitone
    (R S n : ℕ) (hRS : R ≤ S) :
    BadFiveThirdsPrefix n S → BadFiveThirdsPrefix n R := by
  rintro ⟨hodd, hn, hprefix⟩
  exact ⟨hodd, hn, by
    intro r hr hrR
    exact hprefix r hr (by omega)⟩

/-- Elementary finite compactness on the discrete natural numbers:
nested nonempty prefix sets admit a bounded representative sequence
only if their full intersection contains a natural number.

It follows that the absence of any globally exceptional integer
is *equivalent* to escape of ALL possible representative sequences.
It is NOT proved that the intersection is empty. -/
theorem nested_representatives_escape_iff_empty
    (P : ℕ → ℕ → Prop)
    (hmono : ∀ (R S n : ℕ), R ≤ S → P S n → P R n) :
    (∀ b : ℕ → ℕ, (∀ R : ℕ, P R (b R)) →
      ∀ N : ℕ, ∃ R : ℕ, ∀ S : ℕ, R ≤ S → N < b S)
        ↔ ¬ ∃ n : ℕ, ∀ R : ℕ, P R n := by
  constructor
  · intro hescape hnonempty
    obtain ⟨n, hn⟩ := hnonempty
    obtain ⟨R, hR⟩ :=
      hescape (fun _ => n) (by intro S; exact hn S) n
    have hcontradiction := hR R le_rfl
    omega
  · intro hempty b hb N
    have h_each : ∀ n : ℕ, ∃ R : ℕ, ¬ P R n := by
      intro n
      by_contra hne
      apply hempty
      refine ⟨n, ?_⟩
      intro R
      by_contra hnot
      exact hne ⟨R, hnot⟩
    have h_finite : ∀ m : ℕ,
        ∃ R : ℕ, ∀ n : ℕ, n ≤ m → ¬ P R n := by
      intro m
      induction m with
      | zero =>
          obtain ⟨R, hR⟩ := h_each 0
          refine ⟨R, ?_⟩
          intro n hn
          have hn0 : n = 0 := by omega
          subst n
          exact hR
      | succ m ih =>
          obtain ⟨R0, hR0⟩ := ih
          obtain ⟨R1, hR1⟩ := h_each (m + 1)
          refine ⟨max R0 R1, ?_⟩
          intro n hle
          by_cases hprev : n ≤ m
          · intro hp
            exact hR0 n hprev
              (hmono R0 (max R0 R1) n (by omega) hp)
          · have heq : n = m + 1 := by omega
            subst n
            intro hp
            exact hR1
              (hmono R1 (max R0 R1) (m + 1)
                (by omega) hp)
    obtain ⟨R, hR⟩ := h_finite N
    refine ⟨R, ?_⟩
    intro S hRS
    by_contra hnot
    have hle : b S ≤ N := by omega
    exact hR (b S) hle
      (hmono R S (b S) hRS (hb S))

/-- There is no globally exceptional positive odd n if and only if
the OPEN GlobalFiveThirdsDriftGoal holds. -/
theorem no_eternal_bad_five_thirds_prefix_iff_drift :
    (¬ ∃ n : ℕ, ∀ R : ℕ, BadFiveThirdsPrefix n R)
      ↔ GlobalFiveThirdsDriftGoal := by
  constructor
  · intro h n hodd hn
    by_contra hne
    have hbad : ∀ r : ℕ, 1 ≤ r →
        3 * A_orbit n r < 5 * r := by
      intro r hr
      by_contra hnot
      have hlarge : 5 * r ≤ 3 * A_orbit n r := by omega
      exact hne ⟨r, hr, hlarge⟩
    apply h
    refine ⟨n, ?_⟩
    intro R
    exact ⟨hodd, hn, by intro r hr _; exact hbad r hr⟩
  · intro hlarge
    rintro ⟨n, hbad⟩
    have h0 := hbad 0
    obtain ⟨r, hr, hge⟩ :=
      hlarge n h0.1 h0.2.1
    have hsmall := (hbad r).2.2 r hr le_rfl
    omega

/-- Exact statement requested about all positive odd representatives.
It remains an OPEN proposition, and the following theorem identifies
it exactly with the Collatz conjecture. -/
def AllExceptionalRepresentativeChainsEscape : Prop :=
  ∀ b : ℕ → ℕ,
    (∀ R : ℕ, BadFiveThirdsPrefix (b R) R) →
    ∀ N : ℕ, ∃ R : ℕ,
      ∀ S : ℕ, R ≤ S → N < b S

/-- Kernel-verified EQUIVALENCE, not a proof of escape or Collatz.
It also covers coherent nested residue chains, since their positive
representatives satisfy the finite prefix predicate. -/
theorem AllExceptionalRepresentativeChainsEscape_iff_Collatz :
    AllExceptionalRepresentativeChainsEscape ↔
      CollatzConjectureProp := by
  unfold AllExceptionalRepresentativeChainsEscape
  exact
    (nested_representatives_escape_iff_empty
      (fun R n => BadFiveThirdsPrefix n R)
      (fun R S n hRS hP =>
        bad_five_thirds_antitone R S n hRS hP)).trans
      (no_eternal_bad_five_thirds_prefix_iff_drift.trans
        GlobalFiveThirdsDriftGoal_iff_Collatz)

end GARCD

#print axioms GARCD.bad_five_thirds_antitone
#print axioms GARCD.nested_representatives_escape_iff_empty
#print axioms GARCD.no_eternal_bad_five_thirds_prefix_iff_drift
#print axioms GARCD.AllExceptionalRepresentativeChainsEscape_iff_Collatz

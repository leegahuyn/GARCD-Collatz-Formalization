import GARCD.DESCAffineTransfer

/-!
# Global existence of exact affine orbit traces (NOT global descent)

The exact accelerated Collatz/Syracuse trajectory of every natural n,
at every finite depth r, extends to a full infinite arithmetic progression.
The trace certificate always exists. A *contracting* trace certificate
for every odd n > 1 would imply the full Collatz conjecture; we only
prove its logical equivalence here, not its universal truth.

All theorems in this file are unconditional except the explicitly
named equivalence, which does not assert either proposition.
-/

namespace GARCD

private theorem seq_next (x r : ℕ) :
    x_seq x (r + 1) = F (x_seq x r) := by
  unfold x_seq
  rw [Function.iterate_succ_apply']

/-- Every finite Syracuse orbit can be lifted to an infinite affine
arithmetic progression with exact slope 2 * 3^r.
No descent assumption is made or obtained. -/
theorem global_affine_trace_exists (n r : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      ∀ t : ℕ, x_seq (n + M * t) r =
        x_seq n r + (2 * 3 ^ r) * t := by
  induction r with
  | zero =>
      refine ⟨2, by norm_num, ?_⟩
      intro t
      simp [x_seq]
  | succ r ih =>
      obtain ⟨M, hM, htrace⟩ := ih
      let e : ℕ := v2 (3 * x_seq n r + 1)
      refine ⟨M * 2 ^ e, by positivity, ?_⟩
      intro t
      have harg : n + (M * 2 ^ e) * t =
          n + M * (2 ^ e * t) := by ring
      have hmid : x_seq (n + (M * 2 ^ e) * t) r =
          (2 ^ e * (2 * 3 ^ r)) * t + x_seq n r := by
        rw [harg, htrace (2 ^ e * t)]
        ring
      have hcoeff : 3 * (2 ^ e * (2 * 3 ^ r)) =
          2 ^ e * (2 * 3 ^ (r + 1)) := by
        rw [pow_succ]
        ring
      have hconst : 3 * x_seq n r + 1 =
          2 ^ e * F (x_seq n r) := by
        dsimp [e]
        exact (two_pow_v2_mul_F (x_seq n r)).symm
      have heven : (2 * 3 ^ (r + 1)) % 2 = 0 := by omega
      have hstep : F ((2 ^ e * (2 * 3 ^ r)) * t + x_seq n r) =
          (2 * 3 ^ (r + 1)) * t + F (x_seq n r) :=
        affine_F_step _ _ _ _ _ _ hcoeff hconst heven (F_odd _)
      calc
        x_seq (n + (M * 2 ^ e) * t) (r + 1)
            = F (x_seq (n + (M * 2 ^ e) * t) r) :=
                seq_next _ _
        _ = F ((2 ^ e * (2 * 3 ^ r)) * t + x_seq n r) := by
              rw [hmid]
        _ = (2 * 3 ^ (r + 1)) * t + F (x_seq n r) := hstep
        _ = x_seq n (r + 1) + (2 * 3 ^ (r + 1)) * t := by
              rw [seq_next]
              omega

/-- The universal existence of a *descending* trace certificate.
Unlike global_affine_trace_exists, this is an OPEN proposition. -/
def GlobalDescendingTraceGoal : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
    ∃ r M : ℕ, 1 ≤ r ∧ 0 < M ∧
      (∀ t : ℕ, x_seq (n + M * t) r =
        x_seq n r + (2 * 3 ^ r) * t) ∧
      x_seq n r < n

/-- Exact logical boundary: universally descending traces would be
equivalent to the full Collatz conjecture. This does NOT prove either. -/
theorem GlobalDescendingTraceGoal_iff_Collatz :
    GlobalDescendingTraceGoal ↔ CollatzConjectureProp := by
  have hbridge :
      GlobalDescendingTraceGoal ↔ DESCArithmeticProp := by
    constructor
    · intro h n hodd hn
      obtain ⟨r, M, hr, hM, htrace, hdrop⟩ := h n hodd hn
      refine ⟨r, hr, ?_⟩
      exact (GARCD_4_2_Exact_Descent_Iff n r).mp hdrop
    · intro h n hodd hn
      obtain ⟨r, hr, hineq⟩ := h n hodd hn
      obtain ⟨M, hM, htrace⟩ := global_affine_trace_exists n r
      refine ⟨r, M, hr, hM, htrace, ?_⟩
      exact (GARCD_4_2_Exact_Descent_Iff n r).mpr hineq
  exact hbridge.trans
    (DESCArithmeticProp_iff_remaining_thirteen_mod128.trans
      RemainingDESC13Mod128Goal_iff_Collatz)

end GARCD

#print axioms GARCD.global_affine_trace_exists
#print axioms GARCD.GlobalDescendingTraceGoal_iff_Collatz

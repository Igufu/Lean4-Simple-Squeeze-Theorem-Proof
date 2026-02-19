import Theoremprover.Basic
import Mathlib

open Real
set_option linter.style.emptyLine false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false

def seq_converges_to (a : ℕ → ℝ) (L : ℝ) :=
    ∀ε > 0, ∃N, ∀n > N, |a n - L| < ε

theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
    (a_le_b : a ≤ b) (b_le_c : b ≤ c)
    (a_to_L : seq_converges_to a L)
    (c_to_L : seq_converges_to c L) :
    seq_converges_to b L := by
    unfold seq_converges_to
    unfold seq_converges_to at a_to_L
    unfold seq_converges_to at c_to_L
    intro ε ε_pos

    obtain ⟨N₁, hN₁⟩  := a_to_L ε ε_pos
    obtain ⟨N₂, hN₂⟩  := c_to_L ε ε_pos

    let N : ℕ := max N₁ N₂

    have N₂_le_N : N₂ ≤ N := by
        exact Nat.le_max_right N₁ N₂

    have N₁_le_N : N₁ ≤ N := by
        exact Nat.le_max_left N₁ N₂

    use N
    intro n n_gt_N
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    have an_le_bn : a n ≤ b n := a_le_b n
    have n_gt_N₁ : n > N₁ := by
        exact Nat.lt_of_le_of_lt N₁_le_N n_gt_N

    have h_abs : |a n - L| < ε := hN₁ n n_gt_N₁
    rw [abs_lt] at h_abs
    obtain ⟨left_bound, right_bound⟩ := h_abs

    apply lt_of_lt_of_le left_bound (sub_le_sub_right an_le_bn L)

    have bn_le_cn : b n ≤ c n := b_le_c n
    have n_gt_N₂ : n > N₂ := by
        exact Nat.lt_of_le_of_lt N₂_le_N n_gt_N

    have h_abs : |c n - L| < ε := hN₂ n n_gt_N₂
    rw [abs_lt] at h_abs
    obtain ⟨left_bound, right_bound⟩ := h_abs

    apply lt_of_le_of_lt (sub_le_sub_right bn_le_cn L) right_bound

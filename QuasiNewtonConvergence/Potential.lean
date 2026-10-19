module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Scalar potential bounds shared by the convergence proofs. -/

namespace QuasiNewtonConvergence

/-- A decreasing error paid for by a potential drop satisfies a weighted
potential bound. No sign assumption on the error is needed. -/
theorem potential_weighted_bound (error potential : ℕ → ℝ)
    (hmono : ∀ k, error (k + 1) ≤ error k)
    (hdrop : ∀ k, error (k + 1) ≤ potential k - potential (k + 1))
    (k : ℕ) :
    (k : ℝ) * error k + potential k ≤ potential 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := mul_le_mul_of_nonneg_left (hmono k) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hd := hdrop k
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Dropping a nonnegative potential gives the usual last-iterate `O(1/k)`
bound. The scalar statement applies to norm and Bregman potentials alike. -/
theorem potential_last_iterate_bound (error potential : ℕ → ℝ)
    (hmono : ∀ k, error (k + 1) ≤ error k)
    (hdrop : ∀ k, error (k + 1) ≤ potential k - potential (k + 1))
    (hnonneg : ∀ k, 0 ≤ potential k) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * error (k + 1) ≤ potential 0 := by
  have h := potential_weighted_bound error potential hmono hdrop (k + 1)
  linarith [hnonneg (k + 1)]

end QuasiNewtonConvergence

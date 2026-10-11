import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# The scalar trace–determinant potential argument for BFGS

Nocedal–Wright's potential `trace B - log det B` satisfies the recurrence
below after the finite-dimensional trace and determinant identities are
established. This lemma proves that such a recurrence prevents every
search angle from tending to zero. The matrix identities themselves remain
to be formalized.
-/

namespace QuasiNewtonConvergence

/-- The scalar potential inequality obtained from the BFGS trace and
determinant update identities. The matrix identities are supplied as
`htrace` and `hdet`. -/
theorem bfgs_scalar_potential_step
    (T Tnext D Dnext a b q cosine m M C : ℝ)
    (hD : 0 < D) (ha : 0 < a) (hq : 0 < q) (hc : 0 < cosine)
    (hm : 0 < m) (hma : m ≤ a) (hb : b ≤ M)
    (hC : M - Real.log m - 1 ≤ C)
    (htrace : Tnext = T - q / cosine ^ 2 + b)
    (hdet : Dnext = D * a / q) :
    Tnext - Real.log Dnext ≤
      T - Real.log D + C + Real.log (cosine ^ 2) := by
  have hlogdet : Real.log Dnext = Real.log D + Real.log a - Real.log q := by
    rw [hdet, Real.log_div (mul_ne_zero (ne_of_gt hD) (ne_of_gt ha))
      (ne_of_gt hq), Real.log_mul (ne_of_gt hD) (ne_of_gt ha)]
  have hc2 : 0 < cosine ^ 2 := sq_pos_of_pos hc
  have hqsplit : Real.log q =
      Real.log (q / cosine ^ 2) + Real.log (cosine ^ 2) := by
    have heq : q = q / cosine ^ 2 * cosine ^ 2 := by
      field_simp
    calc
      Real.log q = Real.log (q / cosine ^ 2 * cosine ^ 2) := congrArg Real.log heq
      _ = _ := Real.log_mul (ne_of_gt (div_pos hq hc2)) (ne_of_gt hc2)
  have hloga : Real.log m ≤ Real.log a := Real.log_le_log hm hma
  have ht := Real.log_le_sub_one_of_pos (div_pos hq hc2)
  rw [htrace, hlogdet, hqsplit]
  linarith

/-- A lower-bounded BFGS potential with the book's logarithmic recurrence
prevents the positive search-angle cosine from converging to zero. -/
theorem bfgs_angle_not_tendsto_zero
    (potential cosine : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hpotential : ∀ k, 0 ≤ potential k)
    (hcosine : ∀ k, 0 < cosine k)
    (hupdate : ∀ k, potential (k + 1) ≤
      potential k + C + Real.log (cosine k ^ 2)) :
    ¬ Filter.Tendsto cosine Filter.atTop (nhds 0) := by
  intro hzero
  have hexp : 0 < Real.exp (-C) := Real.exp_pos _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hzero.eventually_lt_const hexp)
  have hlog (k : ℕ) (hk : N ≤ k) :
      Real.log (cosine k ^ 2) < -2 * C := by
    have hl := Real.log_lt_log (hcosine k) (hN k hk)
    rw [Real.log_exp] at hl
    calc
      Real.log (cosine k ^ 2) = 2 * Real.log (cosine k) := by
        rw [Real.log_pow]; norm_num
      _ < 2 * (-C) := mul_lt_mul_of_pos_left hl (by norm_num)
      _ = -2 * C := by ring
  have hdrop (k : ℕ) (hk : N ≤ k) :
      potential (k + 1) ≤ potential k - C := by
    linarith [hupdate k, hlog k hk]
  have hbound : ∀ j : ℕ, potential (N + j) ≤ potential N - C * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hNj : N ≤ N + j := Nat.le_add_right N j
      rw [Nat.add_succ]
      have hd := hdrop (N + j) hNj
      push_cast
      linarith
  obtain ⟨j, hj⟩ := exists_nat_gt (potential N / C)
  have hlarge : potential N < C * (j : ℝ) := by
    have := (div_lt_iff₀ hC).mp hj
    nlinarith
  have hnonneg := hpotential (N + j)
  have hupper := hbound j
  nlinarith

end QuasiNewtonConvergence

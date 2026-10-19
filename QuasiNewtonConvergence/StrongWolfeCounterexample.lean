module

public import QuasiNewtonConvergence.BroydenUpdates
public import QuasiNewtonConvergence.LineSearch

@[expose] public section

/-!
# Strong Wolfe steps do not by themselves imply superlinear BFGS convergence

On `f(x) = x²/2`, the exact BFGS Hessian is `1`. A line search can
nevertheless choose the fixed half step forever. It satisfies strong Wolfe
with `c₁ = 1/4` and `c₂ = 3/4`, but has error ratio `1/2`.
-/

noncomputable section
namespace QuasiNewtonConvergence

open Filter

/-- The explicit iterate sequence used in the public BFGS counterexample. -/
def halfStepIterate (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

private theorem halfStepIterate_pos (k : ℕ) : 0 < halfStepIterate k :=
  pow_pos (by norm_num) k

private theorem halfStepIterate_succ (k : ℕ) :
    halfStepIterate (k + 1) = halfStepIterate k / 2 := by
  simp [halfStepIterate, pow_succ, div_eq_mul_inv]

/-- A half step satisfies the Armijo and strong curvature inequalities on
the one-dimensional positive quadratic. -/
theorem quadratic_half_step_strongWolfe (x : ℝ) :
    WolfeStep (1 / 4) (3 / 4) (1 / 2)
      (-x ^ 2) (-(x ^ 2) / 2) (x ^ 2 / 2) ((x / 2) ^ 2 / 2) ∧
      |-(x ^ 2) / 2| ≤ (3 / 4 : ℝ) * |-x ^ 2| := by
  constructor
  · constructor <;> nlinarith [sq_nonneg x]
  · simp only [abs_div, abs_neg, abs_of_nonneg (sq_nonneg x)]
    norm_num
    nlinarith [sq_nonneg x]

/-- The exact unit Hessian is unchanged by any nonzero secant pair `y = s`. -/
theorem bfgs_identity_update (s : ℝ) :
    bfgsUpdateMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) s s = LinearMap.id := by
  simp [bfgsUpdateMap]

/-- Every iteration is a BFGS iteration whose line search satisfies strong
Wolfe, yet the contraction factor is exactly one half. -/
theorem quadratic_half_step_bfgs_counterexample :
    (∀ k, bfgsUpdateMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
      (halfStepIterate (k + 1) - halfStepIterate k)
      (halfStepIterate (k + 1) - halfStepIterate k) = LinearMap.id) ∧
    (∀ k, halfStepIterate (k + 1) = halfStepIterate k +
      (1 / 2 : ℝ) * (-halfStepIterate k)) ∧
    (∀ k, WolfeStep (1 / 4) (3 / 4) (1 / 2)
      (-(halfStepIterate k) ^ 2)
      (-(halfStepIterate k) ^ 2 / 2)
      ((halfStepIterate k) ^ 2 / 2)
      (((halfStepIterate k) / 2) ^ 2 / 2) ∧
      |-(halfStepIterate k) ^ 2 / 2| ≤
        (3 / 4 : ℝ) * |-(halfStepIterate k) ^ 2|) ∧
    (∀ k, ‖halfStepIterate (k + 1)‖ / ‖halfStepIterate k‖ = (1 / 2 : ℝ)) ∧
    ¬ Tendsto (fun k => ‖halfStepIterate (k + 1)‖ /
      ‖halfStepIterate k‖) atTop (nhds 0) := by
  have hratio (k : ℕ) :
      ‖halfStepIterate (k + 1)‖ / ‖halfStepIterate k‖ =
        (1 / 2 : ℝ) := by
    rw [halfStepIterate_succ]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (halfStepIterate_pos k),
      abs_of_pos (div_pos (halfStepIterate_pos k) (by norm_num))]
    have hx : halfStepIterate k ≠ 0 := ne_of_gt (halfStepIterate_pos k)
    field_simp [hx]
  refine ⟨fun k => bfgs_identity_update _, ?_,
    fun k => quadratic_half_step_strongWolfe _, hratio, ?_⟩
  · intro k
    rw [halfStepIterate_succ]
    ring
  intro h
  have hhalf : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds 0) := by
    simpa only [hratio] using h
  have : (1 / 2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hhalf
  norm_num at this

end QuasiNewtonConvergence

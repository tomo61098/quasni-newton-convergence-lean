import Mathlib.Analysis.InnerProductSpace.Basic
import QuasiNewtonConvergence.LineSearch
import QuasiNewtonConvergence.GradientDescent
import QuasiNewtonConvergence.DiminishingGradientDescent
import QuasiNewtonConvergence.Subgradient
import QuasiNewtonConvergence.Nesterov
import QuasiNewtonConvergence.NesterovStrong
import QuasiNewtonConvergence.StrongConvexMinimizer
import QuasiNewtonConvergence.WolfeGradientDescent

/-!
# Foundations for BFGS convergence

The update below is the Hessian form of BFGS (Nocedal--Wright, (6.19)).
It is defined on a real inner product space so its secant property can be
established independently of a choice of coordinates. The convergence
theorems require additional results about positivity, trace, determinant,
Wolfe line searches, and the Dennis--Moré condition.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strict positivity of a Hessian approximation's quadratic form. -/
def PositiveDefinite (B : E →ₗ[ℝ] E) : Prop :=
  ∀ z : E, z ≠ 0 → 0 < inner ℝ (B z) z

/-- The Hessian form of the BFGS rank two update. The two denominators are
nonzero for a positive definite `B` and a step satisfying the curvature
condition. -/
def bfgsUpdate (B : E →ₗ[ℝ] E) (s y : E) (z : E) : E :=
  B z - (inner ℝ (B s) z / inner ℝ (B s) s) • B s +
    (inner ℝ y z / inner ℝ y s) • y

/-- BFGS satisfies the secant equation `B₊ s = y`. -/
theorem bfgsUpdate_secant (B : E →ₗ[ℝ] E) (s y : E)
    (hBs : inner ℝ (B s) s ≠ 0) (hys : inner ℝ y s ≠ 0) :
    bfgsUpdate B s y s = y := by
  simp [bfgsUpdate, div_self hBs, div_self hys]

/-- The usual positive definiteness and curvature assumptions supply the
nonzero denominators in the BFGS secant equation. -/
theorem bfgsUpdate_secant_of_curvature (B : E →ₗ[ℝ] E) (s y : E)
    (hB : PositiveDefinite B) (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) :
    bfgsUpdate B s y s = y :=
  bfgsUpdate_secant B s y (ne_of_gt (hB s hs)) (ne_of_gt hcurv)

end QuasiNewtonConvergence

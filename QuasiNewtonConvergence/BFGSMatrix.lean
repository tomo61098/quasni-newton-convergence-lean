import QuasiNewtonConvergence.BroydenUpdates
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Finite-dimensional BFGS trace identity

This is the trace half of the matrix potential argument in Nocedal–Wright,
Theorem 6.5. The determinant identity remains to be formalized.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def innerLinear (a : E) : E →ₗ[ℝ] ℝ where
  toFun z := inner ℝ a z
  map_add' z w := by simp [inner_add_right]
  map_smul' c z := by simp [real_inner_smul_right]

private theorem trace_rankOne (a b : E) :
    (rankOne a b).trace ℝ E = inner ℝ a b := by
  have heq : rankOne a b = (innerLinear a).smulRight b := by
    ext z
    rfl
  rw [heq]
  exact LinearMap.trace_smulRight (innerLinear a) b

/-- Equation (6.44): the exact trace change under a BFGS update. -/
theorem bfgs_trace_update (B : E →ₗ[ℝ] E) (s y : E) :
    (bfgsUpdateMap B s y).trace ℝ E =
      B.trace ℝ E - ‖B s‖ ^ 2 / inner ℝ (B s) s +
        ‖y‖ ^ 2 / inner ℝ y s := by
  simp only [bfgsUpdateMap, map_add, map_sub, map_smul,
    trace_rankOne, real_inner_self_eq_norm_sq]
  ring

/-- The two-dimensional determinant reduction behind the BFGS determinant
identity. The hypotheses are the three entries fixed by the secant geometry;
the remaining entry cancels from the determinant. -/
theorem bfgs_det_rank_two_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (U : Matrix ι (Fin 2) ℝ)
    (V : Matrix (Fin 2) ι ℝ) (β η : ℝ)
    (hA : IsUnit A.det)
    (h00 : ((1 : Matrix (Fin 2) (Fin 2) ℝ) + V * A⁻¹ * U) 0 0 = 0)
    (h01 : ((1 : Matrix (Fin 2) (Fin 2) ℝ) + V * A⁻¹ * U) 0 1 = η / β)
    (h10 : ((1 : Matrix (Fin 2) (Fin 2) ℝ) + V * A⁻¹ * U) 1 0 = -1) :
    (A + U * V).det = A.det * (η / β) := by
  rw [Matrix.det_add_mul U V hA, Matrix.det_fin_two, h00, h01, h10]
  ring

end QuasiNewtonConvergence

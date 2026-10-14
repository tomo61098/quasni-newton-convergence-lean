import QuasiNewtonConvergence.BroydenUpdates
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

private theorem positive_eigenvalues (B : E →ₗ[ℝ] E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (i : Fin (Module.finrank ℝ E)) :
    0 < (show B.IsSymmetric from hSym).eigenvalues rfl i := by
  apply eigenvalue_pos_of_pos
    ((show B.IsSymmetric from hSym).hasEigenvalue_eigenvalues rfl i)
  intro z hz
  simpa only [RCLike.re_to_real, real_inner_comm z (B z)] using hB z hz

/-- A symmetric positive definite endomorphism has positive determinant,
including in dimension zero. -/
theorem positiveDefinite_det_pos (B : E →ₗ[ℝ] E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B) :
    0 < B.det := by
  classical
  rw [(show B.IsSymmetric from hSym).det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos fun i _ => positive_eigenvalues B hB hSym i

/-- The trace–logdet potential is bounded below by the dimension. -/
theorem positiveDefinite_trace_sub_log_det (B : E →ₗ[ℝ] E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B) :
    (Module.finrank ℝ E : ℝ) ≤ B.trace ℝ E - Real.log B.det := by
  classical
  let hS : B.IsSymmetric := hSym
  rw [hS.trace_eq_sum_eigenvalues rfl, hS.det_eq_prod_eigenvalues rfl]
  rw [Real.log_prod (fun i _ => ne_of_gt (positive_eigenvalues B hB hSym i))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Real.log_le_sub_one_of_pos (positive_eigenvalues B hB hSym i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  exact (le_sub_iff_add_le).mpr (by linarith)

private theorem det_one_add_comp (U : (Fin 2 → ℝ) →ₗ[ℝ] E)
    (V : E →ₗ[ℝ] (Fin 2 → ℝ)) :
    (1 + U.comp V).det = (1 + V.comp U).det := by
  classical
  let b := Module.finBasis ℝ E
  let c := Pi.basisFun ℝ (Fin 2)
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix c]
  simp only [map_add, LinearMap.toMatrix_one,
    LinearMap.toMatrix_comp b c b, LinearMap.toMatrix_comp c b c]
  exact Matrix.det_one_add_mul_comm _ _

end QuasiNewtonConvergence

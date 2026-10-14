import QuasiNewtonConvergence.BroydenUpdates
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement

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

/-- The determinant update for the actual BFGS endomorphism. -/
theorem bfgs_det_update (B : E →ₗ[ℝ] E) (s y : E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hy : 0 < inner ℝ y s) :
    (bfgsUpdateMap B s y).det =
      B.det * (inner ℝ y s / inner ℝ (B s) s) := by
  classical
  have hβ : inner ℝ (B s) s ≠ 0 := ne_of_gt (hB s hs)
  have hη : inner ℝ y s ≠ 0 := ne_of_gt hy
  have hinj : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have hp := hB z hne
    simp [hz] at hp
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo B hinj
  have he (z : E) : B (e.symm z) = z := e.apply_symm_apply z
  let U : (Fin 2 → ℝ) →ₗ[ℝ] E :=
    (LinearMap.proj 0).smulRight (-s) + (LinearMap.proj 1).smulRight (e.symm y)
  let V : E →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi ![(inner ℝ (B s) s)⁻¹ • innerLinear (B s),
      (inner ℝ y s)⁻¹ • innerLinear y]
  have hfactor : bfgsUpdateMap B s y = B.comp (1 + U.comp V) := by
    ext z
    simp [bfgsUpdate, U, V, innerLinear, he, div_eq_mul_inv,
      mul_comm, sub_eq_add_neg, add_assoc]
  have hsym : inner ℝ (B s) (e.symm y) = inner ℝ y s := by
    rw [hSym, he, real_inner_comm]
  let A := LinearMap.toMatrix' (1 + V.comp U)
  have h00 : A 0 0 = 0 := by
    simp [A, LinearMap.toMatrix'_apply, U, V, innerLinear, hβ]
  have h01 : A 0 1 = inner ℝ y s / inner ℝ (B s) s := by
    simp [A, LinearMap.toMatrix'_apply, U, V, innerLinear, hsym, div_eq_mul_inv,
      mul_comm]
  have h10 : A 1 0 = -1 := by
    simp [A, LinearMap.toMatrix'_apply, U, V, innerLinear, hη]
  rw [hfactor, LinearMap.det_comp, det_one_add_comp,
    ← LinearMap.det_toMatrix']
  change B.det * A.det = _
  rw [Matrix.det_fin_two, h00, h01, h10]
  ring

end QuasiNewtonConvergence



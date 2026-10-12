import QuasiNewtonConvergence.BFGSMatrix
import QuasiNewtonConvergence.BFGSDennisMore

/-!
# Directional Dennis–Moré from BFGS scalar potential data

The update supplies the trace change and the directional geometry. The
determinant recurrence and summable secant error remain explicit hypotheses.
-/

noncomputable section
namespace QuasiNewtonConvergence

open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem bfgs_trace_normalized (B : E →ₗ[ℝ] E) (s y : E)
    (hs : 0 < inner ℝ (B s) s)
    (hy : 0 < inner ℝ y s) :
    (bfgsUpdateMap B s y).trace ℝ E = B.trace ℝ E -
      (inner ℝ (B s) s / ‖s‖ ^ 2) /
        (inner ℝ (B s) s / (‖B s‖ * ‖s‖)) ^ 2 +
      ‖y‖ ^ 2 / inner ℝ y s := by
  have hsn : ‖s‖ ≠ 0 := by
    intro hz
    have : s = 0 := norm_eq_zero.mp hz
    simp [this] at hs
  have hBn : ‖B s‖ ≠ 0 := by
    intro hz
    have : B s = 0 := norm_eq_zero.mp hz
    simp [this] at hs
  have hinner : inner ℝ (B s) s ≠ 0 := ne_of_gt hs
  rw [bfgs_trace_update]
  field_simp

/-- The directional Dennis–Moré ratio for an actual sequence of BFGS updates.
The determinant recurrence and the summable secant error are the remaining
potential-theorem inputs. The reference Hessian is the identity. -/
theorem bfgs_update_directional_dennis_more
    (B : ℕ → E →ₗ[ℝ] E) (s y : ℕ → E)
    (determinant secantError : ℕ → ℝ)
    (hupdate : ∀ k, B (k + 1) = bfgsUpdateMap (B k) (s k) (y k))
    (hs : ∀ k, 0 < inner ℝ (B k (s k)) (s k))
    (hy : ∀ k, 0 < inner ℝ (y k) (s k))
    (hD : ∀ k, 0 < determinant k)
    (hpot : ∀ k, 0 ≤ (B k).trace ℝ E - Real.log (determinant k))
    (herr : ∀ k, 0 ≤ secantError k)
    (hsum : Summable secantError)
    (hdet : ∀ k, determinant (k + 1) = determinant k *
      (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) /
      (inner ℝ (B k (s k)) (s k) / ‖s k‖ ^ 2))
    (herror : ∀ k, ‖y k‖ ^ 2 / inner ℝ (y k) (s k) -
      Real.log (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) - 1 ≤
        secantError k) :
    Tendsto (fun k => ‖B k (s k) - s k‖ / ‖s k‖)
      atTop (nhds 0) := by
  let q : ℕ → ℝ := fun k => inner ℝ (B k (s k)) (s k) / ‖s k‖ ^ 2
  let c : ℕ → ℝ := fun k =>
    inner ℝ (B k (s k)) (s k) / (‖B k (s k)‖ * ‖s k‖)
  let m : ℕ → ℝ := fun k => inner ℝ (y k) (s k) / ‖s k‖ ^ 2
  let M : ℕ → ℝ := fun k => ‖y k‖ ^ 2 / inner ℝ (y k) (s k)
  have hsn (k : ℕ) : 0 < ‖s k‖ := by
    have : s k ≠ 0 := by
      intro hz
      have hh := hs k
      simp [hz] at hh
    exact norm_pos_iff.mpr this
  have hBn (k : ℕ) : 0 < ‖B k (s k)‖ := by
    have : B k (s k) ≠ 0 := by
      intro hz
      have hh := hs k
      simp [hz] at hh
    exact norm_pos_iff.mpr this
  have hq (k : ℕ) : 0 < q k := div_pos (hs k) (sq_pos_of_pos (hsn k))
  have hm (k : ℕ) : 0 < m k := div_pos (hy k) (sq_pos_of_pos (hsn k))
  have hc (k : ℕ) : 0 < c k := div_pos (hs k) (mul_pos (hBn k) (hsn k))
  have hcle (k : ℕ) : c k ≤ 1 := by
    dsimp [c]
    exact (div_le_one (mul_pos (hBn k) (hsn k))).mpr
      (real_inner_le_norm (B k (s k)) (s k))
  have htrace (k : ℕ) : (B (k + 1)).trace ℝ E =
      (B k).trace ℝ E - q k / c k ^ 2 + M k := by
    rw [hupdate k]
    exact bfgs_trace_normalized (B k) (s k) (y k) (hs k) (hy k)
  have hgeom (k : ℕ) : (‖B k (s k) - s k‖ / ‖s k‖) ^ 2 =
      q k ^ 2 / c k ^ 2 - 2 * q k + 1 := by
    simpa only [q, c, div_pow, mul_pow] using
      (bfgs_geometric_identity (B k (s k)) (s k) (hs k))
  exact bfgs_scalar_trace_det_dennis_more
    (fun k => (B k).trace ℝ E) determinant m M q c secantError
    (fun k => ‖B k (s k) - s k‖ / ‖s k‖)
    hD hm hq hc hcle hpot herr hsum htrace hdet herror
    (fun k => div_nonneg (norm_nonneg _) (norm_nonneg _)) hgeom

end QuasiNewtonConvergence

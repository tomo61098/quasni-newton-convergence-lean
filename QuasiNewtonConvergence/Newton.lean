import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local quadratic convergence of full Newton steps

The main estimate is the standard Newton error inequality.  A globally
Lipschitz Hessian is used here to keep the mean-value argument independent
of a chosen neighborhood; only its restriction to a neighborhood of the
stationary point is needed for the local conclusion.
-/

noncomputable section

namespace QuasiNewtonConvergence

open Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A full Newton step, with `inverseHessian x` the inverse of the Hessian at `x`. -/
def newtonStep (gradient : E → E) (inverseHessian : E → E →L[ℝ] E) (x : E) : E :=
  x - inverseHessian x (gradient x)

/-- Lipschitz continuity of the Hessian gives a quadratic gradient remainder.
The constant is slightly weaker than the sharp `L/2` constant. -/
theorem newton_gradient_remainder (gradient : E → E)
    (hessian : E → E →L[ℝ] E) (L : ℝ) (x xstar : E)
    (hL : 0 ≤ L)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLip : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖) :
    ‖hessian x (x - xstar) - (gradient x - gradient xstar)‖ ≤
      L * ‖x - xstar‖ ^ 2 := by
  let e : ℝ := ‖x - xstar‖
  let s : Set E := closedBall x e
  let φ : E → E := fun y => gradient y - hessian x y
  have hφ : ∀ y ∈ s, HasFDerivWithinAt φ (hessian y - hessian x) s y := by
    intro y _
    exact ((hderiv y).sub (hessian x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ y ∈ s, ‖hessian y - hessian x‖ ≤ L * e := by
    intro y hy
    exact (hLip y x).trans (mul_le_mul_of_nonneg_left (by
      simpa [s, e, dist_eq_norm] using hy) hL)
  have hs : Convex ℝ s := convex_closedBall x e
  have hx : x ∈ s := mem_closedBall_self (norm_nonneg _)
  have hxstar : xstar ∈ s := by
    simp [s, e, dist_eq_norm, norm_sub_rev]
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hφ hb hx hxstar
  calc
    _ = ‖φ xstar - φ x‖ := by
      congr 1
      dsimp [φ]
      rw [map_sub]
      abel
    _ ≤ L * e * ‖xstar - x‖ := h
    _ = L * ‖x - xstar‖ ^ 2 := by rw [norm_sub_rev]; dsimp [e]; ring

/-- The fundamental quadratic error bound for a full Newton step. -/
theorem newtonStep_quadratic_bound (gradient : E → E)
    (hessian inverseHessian : E → E →L[ℝ] E) (L B : ℝ) (x xstar : E)
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLip : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (hstationary : gradient xstar = 0)
    (hinverse : ∀ y v, inverseHessian y (hessian y v) = v)
    (hbound : ‖inverseHessian x‖ ≤ B) :
    ‖newtonStep gradient inverseHessian x - xstar‖ ≤
      (B * L) * ‖x - xstar‖ ^ 2 := by
  have hrem := newton_gradient_remainder gradient hessian L x xstar hL hderiv hLip
  have herr : newtonStep gradient inverseHessian x - xstar =
      inverseHessian x
        (hessian x (x - xstar) - (gradient x - gradient xstar)) := by
    simp only [newtonStep, map_sub, hinverse, hstationary, sub_zero]
    abel
  rw [herr]
  calc
    _ ≤ ‖inverseHessian x‖ *
        ‖hessian x (x - xstar) - (gradient x - gradient xstar)‖ :=
      (inverseHessian x).le_opNorm _
    _ ≤ B * (L * ‖x - xstar‖ ^ 2) :=
      mul_le_mul hbound hrem (norm_nonneg _) hB
    _ = (B * L) * ‖x - xstar‖ ^ 2 := by ring

/-- Full Newton iterates satisfy a quadratic recurrence and a geometric
majorant whenever the starting error lies in a sufficiently small ball. -/
theorem newton_local_quadratic_convergence (gradient : E → E)
    (hessian inverseHessian : E → E →L[ℝ] E) (L B r : ℝ)
    (x : ℕ → E) (xstar : E)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hsmall : (B * L) * r < 1)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLip : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (hstationary : gradient xstar = 0)
    (hinverse : ∀ y v, inverseHessian y (hessian y v) = v)
    (hbound : ∀ y, ‖y - xstar‖ ≤ r → ‖inverseHessian y‖ ≤ B)
    (hinit : ‖x 0 - xstar‖ ≤ r)
    (hstep : ∀ k, x (k + 1) = newtonStep gradient inverseHessian (x k)) :
    (∀ k, ‖x (k + 1) - xstar‖ ≤ (B * L) * ‖x k - xstar‖ ^ 2) ∧
    (∀ k, ‖x k - xstar‖ ≤ ((B * L) * r) ^ k * ‖x 0 - xstar‖) ∧
    Tendsto x atTop (nhds xstar) := by
  let C : ℝ := B * L
  let q : ℝ := C * r
  have hC : 0 ≤ C := mul_nonneg hB hL
  have hq0 : 0 ≤ q := mul_nonneg hC hr
  have hq1 : q < 1 := hsmall
  have hball : ∀ k, ‖x k - xstar‖ ≤ r := by
    intro k
    induction k with
    | zero => exact hinit
    | succ k ih =>
      have hquad := newtonStep_quadratic_bound gradient hessian inverseHessian
        L B (x k) xstar hL hB hderiv hLip hstationary hinverse (hbound (x k) ih)
      rw [hstep k]
      calc
        _ ≤ C * ‖x k - xstar‖ ^ 2 := hquad
        _ = (C * ‖x k - xstar‖) * ‖x k - xstar‖ := by ring
        _ ≤ q * ‖x k - xstar‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih hC) (norm_nonneg _)
        _ ≤ ‖x k - xstar‖ := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) (norm_nonneg (x k - xstar))]
        _ ≤ r := ih
  have hquad : ∀ k, ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ 2 := by
    intro k
    rw [hstep k]
    exact newtonStep_quadratic_bound gradient hessian inverseHessian
      L B (x k) xstar hL hB hderiv hLip hstationary hinverse (hbound (x k) (hball k))
  have hgeo : ∀ k, ‖x k - xstar‖ ≤ q ^ k * ‖x 0 - xstar‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ C * ‖x k - xstar‖ ^ 2 := hquad k
        _ = (C * ‖x k - xstar‖) * ‖x k - xstar‖ := by ring
        _ ≤ q * ‖x k - xstar‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hball k) hC) (norm_nonneg _)
        _ ≤ q * (q ^ k * ‖x 0 - xstar‖) :=
          mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * ‖x 0 - xstar‖ := by rw [pow_succ]; ring
  have hupper : Tendsto (fun k : ℕ => q ^ k * ‖x 0 - xstar‖) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      ‖x 0 - xstar‖
  have hnorm : Tendsto (fun k : ℕ => ‖x k - xstar‖) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact norm_nonneg _
    · exact hgeo
  exact ⟨hquad, hgeo, tendsto_iff_norm_sub_tendsto_zero.mpr hnorm⟩

end QuasiNewtonConvergence

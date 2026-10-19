module

public import QuasiNewtonConvergence.ProximalBFGS
public import QuasiNewtonConvergence.Newton

@[expose] public section

/-!
# Dennis–Moré superlinear convergence for proximal quasi-Newton steps

The approximation is measured on the actual step, not on the displacement
from the minimizer. Convexity of the nonsmooth term enters through its two
variational inequalities.
-/

noncomputable section
namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A directional, quantitative Dennis–Moré condition. -/
def DennisMoreOnSteps (B : ℕ → E →ₗ[ℝ] E)
    (Hstar : E →ₗ[ℝ] E) (x : ℕ → E) (δ : ℕ → ℝ) : Prop :=
  ∀ k, ‖(B k - Hstar) (x (k + 1) - x k)‖ ≤
    δ k * ‖x (k + 1) - x k‖

/-- The textbook normalized directional error. At a zero step it is
defined to be zero, consistently with the vanishing numerator. -/
def dennisMoreRatio (B : ℕ → E →ₗ[ℝ] E)
    (Hstar : E →ₗ[ℝ] E) (x : ℕ → E) (k : ℕ) : ℝ :=
  ‖(B k - Hstar) (x (k + 1) - x k)‖ /
    ‖x (k + 1) - x k‖

def DennisMoreCriterion (B : ℕ → E →ₗ[ℝ] E)
    (Hstar : E →ₗ[ℝ] E) (x : ℕ → E) : Prop :=
  Filter.Tendsto (dennisMoreRatio B Hstar x)
    Filter.atTop (nhds 0)

theorem dennisMoreRatio_nonneg (B : ℕ → E →ₗ[ℝ] E)
    (Hstar : E →ₗ[ℝ] E) (x : ℕ → E) (k : ℕ) :
    0 ≤ dennisMoreRatio B Hstar x k := by
  dsimp [dennisMoreRatio]
  positivity

theorem dennisMoreRatio_bounds (B : ℕ → E →ₗ[ℝ] E)
    (Hstar : E →ₗ[ℝ] E) (x : ℕ → E) :
    DennisMoreOnSteps B Hstar x (dennisMoreRatio B Hstar x) := by
  intro k
  let d := x (k + 1) - x k
  by_cases hd : ‖d‖ = 0
  · have hzero : d = 0 := norm_eq_zero.mp hd
    simp [dennisMoreRatio, d, hzero]
  · dsimp [dennisMoreRatio]
    change ‖(B k - Hstar) d‖ ≤
      ‖(B k - Hstar) d‖ / ‖d‖ * ‖d‖
    rw [div_mul_cancel₀ _ hd]

/-- Uniformly positive and bounded proximal metrics make the step no
larger than a constant times the error in the current iterate. -/
theorem metricProximal_step_bound
    (g : E → ℝ) (gradient : E → E)
    (B : E →ₗ[ℝ] E) (x z xstar : E)
    (m M G : ℝ) (hm : 0 < m) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hcoercive : ∀ v, m * ‖v‖ ^ 2 ≤ inner ℝ (B v) v)
    (hBbound : ∀ v, ‖B v‖ ≤ M * ‖v‖)
    (hgradient : ‖gradient x - gradient xstar‖ ≤ G * ‖x - xstar‖)
    (hprox : MetricProximalOptimality g gradient B x z)
    (hstar : ∀ u, g u - g xstar ≥
      inner ℝ (-(gradient xstar)) (u - xstar)) :
    ‖z - x‖ ≤ (1 + (M + G) / m) * ‖x - xstar‖ := by
  let q := z - xstar
  let e := x - xstar
  let d := z - x
  have hp := hprox xstar
  have hs := hstar z
  have hneg : xstar - z = -q := by dsimp [q]; abel
  rw [hneg, inner_neg_right] at hp
  simp only [inner_sub_left, inner_neg_left] at hp
  simp only [inner_neg_left] at hs
  have hmono : inner ℝ (gradient x - gradient xstar + B d) q ≤ 0 := by
    dsimp [d, q]
    simp only [inner_add_left, inner_sub_left]
    nlinarith [hp, hs]
  have hd : d = q - e := by dsimp [d, q, e]; abel
  rw [hd, map_sub, inner_add_left, inner_sub_left] at hmono
  have hmetric : m * ‖q‖ ^ 2 ≤
      inner ℝ (B e - (gradient x - gradient xstar)) q := by
    have hh := hcoercive q
    simp only [inner_sub_left] at hmono ⊢
    nlinarith [hh, hmono]
  have hBe : ‖B e‖ ≤ M * ‖e‖ := hBbound e
  have hge : ‖gradient x - gradient xstar‖ ≤ G * ‖e‖ := hgradient
  have hnorm : ‖B e - (gradient x - gradient xstar)‖ ≤
      (M + G) * ‖e‖ := by
    calc
      _ ≤ ‖B e‖ + ‖gradient x - gradient xstar‖ := norm_sub_le _ _
      _ ≤ M * ‖e‖ + G * ‖e‖ := add_le_add hBe hge
      _ = _ := by ring
  have hinner := real_inner_le_norm (B e - (gradient x - gradient xstar)) q
  have hquad : m * ‖q‖ ^ 2 ≤ (M + G) * ‖e‖ * ‖q‖ := by
    calc
      _ ≤ inner ℝ (B e - (gradient x - gradient xstar)) q := hmetric
      _ ≤ ‖B e - (gradient x - gradient xstar)‖ * ‖q‖ := hinner
      _ ≤ (M + G) * ‖e‖ * ‖q‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have hlin : m * ‖q‖ ≤ (M + G) * ‖e‖ := by
    by_cases hzero : ‖q‖ = 0
    · simp only [hzero, mul_zero]
      exact mul_nonneg (add_nonneg hM hG) (norm_nonneg _)
    · have hpos : 0 < ‖q‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      exact le_of_mul_le_mul_right (by nlinarith [hquad]) hpos
  have hqbound : ‖q‖ ≤ ((M + G) / m) * ‖e‖ := by
    have hdiv := (le_div_iff₀ hm).2 (by simpa [mul_comm] using hlin)
    simpa [div_mul_eq_mul_div] using hdiv
  have heq : z - x = q - e := by dsimp [q, e]; abel
  calc
    ‖z - x‖ = ‖q - e‖ := by rw [heq]
    _ ≤ ‖q‖ + ‖e‖ := norm_sub_le _ _
    _ ≤ ((M + G) / m) * ‖e‖ + ‖e‖ :=
      add_le_add hqbound le_rfl
    _ = (1 + (M + G) / m) * ‖x - xstar‖ := by dsimp [e]; ring

/-- The local error estimate for a full proximal quasi-Newton step. The
regularizer may be nonsmooth; only its variational inequalities are used. -/
theorem proximalDennisMore_one_step
    (g : E → ℝ) (gradient : E → E)
    (Hstar B : E →ₗ[ℝ] E) (x z xstar : E)
    (μ L C δ : ℝ) (hμ : 0 < μ) (_hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hH : ∀ v, μ * ‖v‖ ^ 2 ≤ inner ℝ (Hstar v) v)
    (hprox : MetricProximalOptimality g gradient B x z)
    (hstar : ∀ u, g u - g xstar ≥
      inner ℝ (-(gradient xstar)) (u - xstar))
    (hrem : ‖gradient x - gradient xstar -
      Hstar (x - xstar)‖ ≤ L * ‖x - xstar‖ ^ 2)
    (hDM : ‖(B - Hstar) (z - x)‖ ≤ δ * ‖z - x‖)
    (hstep : ‖z - x‖ ≤ C * ‖x - xstar‖) :
    ‖z - xstar‖ ≤
      ((δ * C + L * ‖x - xstar‖) / μ) * ‖x - xstar‖ := by
  let q := z - xstar
  let d := z - x
  let e := x - xstar
  let err := (B - Hstar) d
  let rem := gradient x - gradient xstar - Hstar e
  have hp := hprox xstar
  have hs := hstar z
  have hneg : xstar - z = -q := by dsimp [q]; abel
  rw [hneg, inner_neg_right] at hp
  simp only [inner_sub_left, inner_neg_left] at hp
  simp only [inner_neg_left] at hs
  have hmono : inner ℝ (gradient x - gradient xstar + B d) q ≤ 0 := by
    dsimp [d, q]
    simp only [inner_add_left, inner_sub_left]
    nlinarith [hp, hs]
  have hq : q = e + d := by dsimp [q, e, d]; abel
  have hid : gradient x - gradient xstar + B d =
      Hstar q + err + rem := by
    dsimp [err, rem]
    rw [hq, map_add]
    abel
  rw [hid, inner_add_left, inner_add_left] at hmono
  have hc1 := real_inner_le_norm (-err) q
  have hc2 := real_inner_le_norm (-rem) q
  simp only [inner_neg_left, norm_neg] at hc1 hc2
  have hquad : μ * ‖q‖ ^ 2 ≤ (‖err‖ + ‖rem‖) * ‖q‖ := by
    have hh := hH q
    nlinarith [hh, hmono, hc1, hc2]
  have hlin : μ * ‖q‖ ≤ ‖err‖ + ‖rem‖ := by
    by_cases hzero : ‖q‖ = 0
    · simp only [hzero, mul_zero]
      exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    · have hpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      exact le_of_mul_le_mul_right (by nlinarith [hquad]) hpos
  have herr : ‖err‖ ≤ δ * C * ‖e‖ := by
    calc
      ‖err‖ ≤ δ * ‖d‖ := hDM
      _ ≤ δ * (C * ‖e‖) := by
        exact mul_le_mul_of_nonneg_left hstep hδ
      _ = _ := by ring
  have hsum : ‖err‖ + ‖rem‖ ≤
      (δ * C + L * ‖e‖) * ‖e‖ := by
    have hr : ‖rem‖ ≤ L * ‖e‖ ^ 2 := hrem
    nlinarith [herr, hr]
  have hbound : μ * ‖q‖ ≤
      (δ * C + L * ‖e‖) * ‖e‖ := le_trans hlin hsum
  dsimp [q, e] at hbound ⊢
  calc
    ‖z - xstar‖ ≤ ((δ * C + L * ‖x - xstar‖) * ‖x - xstar‖) / μ :=
      (le_div_iff₀ hμ).2 (by simpa [mul_comm] using hbound)
    _ = _ := by ring

/-- The directional Dennis–Moré criterion implies Q-superlinear convergence
of full proximal quasi-Newton iterates. The step bound can be obtained from
uniform metric bounds. -/
theorem proximalDennisMore_superlinear
    (g : E → ℝ) (gradient : E → E)
    (Hstar : E →ₗ[ℝ] E) (B : ℕ → E →ₗ[ℝ] E)
    (x : ℕ → E) (xstar : E) (δ : ℕ → ℝ)
    (μ L C : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hH : ∀ v, μ * ‖v‖ ^ 2 ≤ inner ℝ (Hstar v) v)
    (hprox : ∀ k, MetricProximalOptimality g gradient (B k)
      (x k) (x (k + 1)))
    (hstar : ∀ u, g u - g xstar ≥
      inner ℝ (-(gradient xstar)) (u - xstar))
    (hrem : ∀ k, ‖gradient (x k) - gradient xstar -
      Hstar (x k - xstar)‖ ≤ L * ‖x k - xstar‖ ^ 2)
    (hDM : DennisMoreOnSteps B Hstar x δ)
    (hδnonneg : ∀ k, 0 ≤ δ k)
    (hstepBound : ∀ k, ‖x (k + 1) - x k‖ ≤ C * ‖x k - xstar‖)
    (hx : Filter.Tendsto x Filter.atTop (nhds xstar))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => ‖x (k + 1) - xstar‖ / ‖x k - xstar‖)
      Filter.atTop (nhds 0) := by
  have herror (k : ℕ) : ‖x (k + 1) - xstar‖ ≤
      ((δ k * C + L * ‖x k - xstar‖) / μ) * ‖x k - xstar‖ :=
    proximalDennisMore_one_step g gradient Hstar (B k)
      (x k) (x (k + 1)) xstar μ L C (δ k) hμ hL
      (hδnonneg k) hH (hprox k) hstar (hrem k) (hDM k)
      (hstepBound k)
  have he : Filter.Tendsto (fun k => ‖x k - xstar‖)
      Filter.atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hupper : Filter.Tendsto
      (fun k => (δ k * C + L * ‖x k - xstar‖) / μ)
      Filter.atTop (nhds 0) := by
    have ha := (hδ.mul_const C).add (he.const_mul L)
    simpa using ha.div_const μ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro k
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro k
    by_cases he0 : ‖x k - xstar‖ = 0
    · have hzero : ‖x (k + 1) - xstar‖ = 0 := by
        have hh := herror k
        rw [he0] at hh
        exact le_antisymm (by simpa using hh) (norm_nonneg _)
      simp [he0, hzero]
      exact div_nonneg (mul_nonneg (hδnonneg k) hC) hμ.le
    · have hpos : 0 < ‖x k - xstar‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm he0)
      exact (div_le_iff₀ hpos).2 (by
        simpa [mul_comm] using herror k)

/-- The same proximal result stated with the usual Dennis–Moré ratio
converging to zero. -/
theorem proximalDennisMore_standard
    (g : E → ℝ) (gradient : E → E)
    (Hstar : E →ₗ[ℝ] E) (B : ℕ → E →ₗ[ℝ] E)
    (x : ℕ → E) (xstar : E)
    (μ L C : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hH : ∀ v, μ * ‖v‖ ^ 2 ≤ inner ℝ (Hstar v) v)
    (hprox : ∀ k, MetricProximalOptimality g gradient (B k)
      (x k) (x (k + 1)))
    (hstar : ∀ u, g u - g xstar ≥
      inner ℝ (-(gradient xstar)) (u - xstar))
    (hrem : ∀ k, ‖gradient (x k) - gradient xstar -
      Hstar (x k - xstar)‖ ≤ L * ‖x k - xstar‖ ^ 2)
    (hstepBound : ∀ k, ‖x (k + 1) - x k‖ ≤ C * ‖x k - xstar‖)
    (hx : Filter.Tendsto x Filter.atTop (nhds xstar))
    (hDM : DennisMoreCriterion B Hstar x) :
    Filter.Tendsto
      (fun k => ‖x (k + 1) - xstar‖ / ‖x k - xstar‖)
      Filter.atTop (nhds 0) :=
  proximalDennisMore_superlinear g gradient Hstar B x xstar
    (dennisMoreRatio B Hstar x) μ L C hμ hL hC hH hprox hstar
    hrem (dennisMoreRatio_bounds B Hstar x)
    (dennisMoreRatio_nonneg B Hstar x) hstepBound hx hDM

/-- Taylor's quadratic remainder with the Hessian fixed at the solution. -/
theorem dennisMore_gradient_remainder
    (gradient : E → E) (hessian : E → E →L[ℝ] E)
    (L : ℝ) (hL : 0 ≤ L)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLip : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (x xstar : E) :
    ‖gradient x - gradient xstar -
      hessian xstar (x - xstar)‖ ≤ L * ‖x - xstar‖ ^ 2 := by
  have h := newton_gradient_remainder gradient hessian L xstar x
    hL hderiv hLip
  have heq : hessian xstar (xstar - x) -
      (gradient xstar - gradient x) =
        gradient x - gradient xstar -
          hessian xstar (x - xstar) := by
    rw [show xstar - x = -(x - xstar) by abel, map_neg]
    abel
  rw [heq, norm_sub_rev xstar x] at h
  exact h

/-- Proximal Dennis–Moré with the usual uniform spectral and smoothness
assumptions, so the step bound is derived rather than assumed. -/
theorem proximalDennisMore_of_uniform_metrics
    (g : E → ℝ) (gradient : E → E)
    (hessian : E → E →L[ℝ] E)
    (B : ℕ → E →ₗ[ℝ] E) (x : ℕ → E) (xstar : E)
    (δ : ℕ → ℝ) (μ m M G L : ℝ)
    (hμ : 0 < μ) (hm : 0 < m) (hM : 0 ≤ M)
    (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hH : ∀ v, μ * ‖v‖ ^ 2 ≤ inner ℝ (hessian xstar v) v)
    (hBcoercive : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (B k v) v)
    (hBbound : ∀ k v, ‖B k v‖ ≤ M * ‖v‖)
    (hgradBound : ∀ k, ‖gradient (x k) - gradient xstar‖ ≤
      G * ‖x k - xstar‖)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLipH : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (hprox : ∀ k, MetricProximalOptimality g gradient (B k)
      (x k) (x (k + 1)))
    (hstar : ∀ u, g u - g xstar ≥
      inner ℝ (-(gradient xstar)) (u - xstar))
    (hDM : DennisMoreOnSteps B (hessian xstar) x δ)
    (hδnonneg : ∀ k, 0 ≤ δ k)
    (hx : Filter.Tendsto x Filter.atTop (nhds xstar))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => ‖x (k + 1) - xstar‖ / ‖x k - xstar‖)
      Filter.atTop (nhds 0) := by
  let C := 1 + (M + G) / m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hstep (k : ℕ) : ‖x (k + 1) - x k‖ ≤
      C * ‖x k - xstar‖ :=
    metricProximal_step_bound g gradient (B k)
      (x k) (x (k + 1)) xstar m M G hm hM hG
      (hBcoercive k) (hBbound k) (hgradBound k) (hprox k) hstar
  have hrem (k : ℕ) : ‖gradient (x k) - gradient xstar -
      hessian xstar (x k - xstar)‖ ≤
        L * ‖x k - xstar‖ ^ 2 :=
    dennisMore_gradient_remainder gradient hessian L hL
      hderiv hLipH (x k) xstar
  exact proximalDennisMore_superlinear g gradient (hessian xstar) B x
    xstar δ μ L C hμ hL hC hH hprox hstar hrem hDM
    hδnonneg hstep hx hδ

/-- The ordinary smooth Dennis–Moré theorem is the zero-regularizer case
of the proximal theorem. The full quasi-Newton equation replaces proximal
optimality. -/
theorem dennisMore_smooth_superlinear
    (gradient : E → E) (hessian : E → E →L[ℝ] E)
    (B : ℕ → E →ₗ[ℝ] E) (x : ℕ → E) (xstar : E)
    (δ : ℕ → ℝ) (μ m M G L : ℝ)
    (hμ : 0 < μ) (hm : 0 < m) (hM : 0 ≤ M)
    (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hH : ∀ v, μ * ‖v‖ ^ 2 ≤ inner ℝ (hessian xstar v) v)
    (hBcoercive : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (B k v) v)
    (hBbound : ∀ k v, ‖B k v‖ ≤ M * ‖v‖)
    (hgradBound : ∀ k, ‖gradient (x k) - gradient xstar‖ ≤
      G * ‖x k - xstar‖)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLipH : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (hstationary : gradient xstar = 0)
    (hstep : ∀ k, gradient (x k) +
      B k (x (k + 1) - x k) = 0)
    (hDM : DennisMoreOnSteps B (hessian xstar) x δ)
    (hδnonneg : ∀ k, 0 ≤ δ k)
    (hx : Filter.Tendsto x Filter.atTop (nhds xstar))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => ‖x (k + 1) - xstar‖ / ‖x k - xstar‖)
      Filter.atTop (nhds 0) := by
  have hprox (k : ℕ) :
      MetricProximalOptimality (fun _ : E => 0) gradient (B k)
        (x k) (x (k + 1)) := by
    intro u
    have hz : -(gradient (x k)) -
        B k (x (k + 1) - x k) = 0 := by
      have hs := hstep k
      calc
        _ = -(gradient (x k) + B k (x (k + 1) - x k)) := by abel
        _ = 0 := by rw [hs]; simp
    change (0 : ℝ) - 0 ≥ inner ℝ
      (-(gradient (x k)) - B k (x (k + 1) - x k))
      (u - x (k + 1))
    rw [hz]
    simp
  have hstar : ∀ u, (0 : ℝ) - 0 ≥
      inner ℝ (-(gradient xstar)) (u - xstar) := by
    intro u
    simp [hstationary]
  exact proximalDennisMore_of_uniform_metrics (fun _ : E => 0)
    gradient hessian B x xstar δ μ m M G L
    hμ hm hM hG hL hH hBcoercive hBbound hgradBound
    hderiv hLipH hprox hstar hDM hδnonneg hx hδ

/-- An exact full-step proximal BFGS run. The update recurrence is part of
the run; uniform metric bounds and Dennis–Moré remain separate conditions. -/
structure ProximalBFGSRun (g : E → ℝ) (gradient : E → E) where
  x : ℕ → E
  B : ℕ → E →ₗ[ℝ] E
  step : ∀ k, MetricProximalOptimality g gradient (B k)
    (x k) (x (k + 1))
  update : ∀ k, B (k + 1) = bfgsUpdateMap (B k)
    (x (k + 1) - x k)
    (gradient (x (k + 1)) - gradient (x k))

/-- BFGS-metric specialization of proximal Dennis–Moré. -/
theorem ProximalBFGSRun.dennisMore_superlinear
    (run : ProximalBFGSRun g gradient)
    (hessian : E → E →L[ℝ] E) (xstar : E)
    (δ : ℕ → ℝ) (μ m M G L : ℝ)
    (hμ : 0 < μ) (hm : 0 < m) (hM : 0 ≤ M)
    (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hH : ∀ v, μ * ‖v‖ ^ 2 ≤ inner ℝ (hessian xstar v) v)
    (hBcoercive : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (run.B k v) v)
    (hBbound : ∀ k v, ‖run.B k v‖ ≤ M * ‖v‖)
    (hgradBound : ∀ k, ‖gradient (run.x k) - gradient xstar‖ ≤
      G * ‖run.x k - xstar‖)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLipH : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (hstar : ∀ u, g u - g xstar ≥
      inner ℝ (-(gradient xstar)) (u - xstar))
    (hDM : DennisMoreOnSteps run.B (hessian xstar) run.x δ)
    (hδnonneg : ∀ k, 0 ≤ δ k)
    (hx : Filter.Tendsto run.x Filter.atTop (nhds xstar))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => ‖run.x (k + 1) - xstar‖ / ‖run.x k - xstar‖)
      Filter.atTop (nhds 0) :=
  proximalDennisMore_of_uniform_metrics g gradient hessian
    run.B run.x xstar δ μ m M G L hμ hm hM hG hL
    hH hBcoercive hBbound hgradBound hderiv hLipH
    run.step hstar hDM hδnonneg hx hδ

end QuasiNewtonConvergence

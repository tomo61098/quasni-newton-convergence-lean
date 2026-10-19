module

public import QuasiNewtonConvergence.ProximalGradient
public import QuasiNewtonConvergence.BroydenUpdates
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! Variable-metric proximal steps, including steps with BFGS Hessian
approximations. The rate hypotheses on the metrics are explicit: a BFGS
secant update alone does not establish uniform spectral bounds. -/

noncomputable section
namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def MetricProximalOptimality (g : E → ℝ) (gradient : E → E)
    (B : E →ₗ[ℝ] E) (x z : E) : Prop :=
  ∀ u, g u - g z ≥ inner ℝ (-(gradient x) - B (z - x)) (u - z)

/-- The full variable-metric proximal step has a quantitative descent bound. -/
theorem metricProximal_descent (f g : E → ℝ) (gradient : E → E)
    (L m : ℝ) (B : E →ₗ[ℝ] E)
    (hsmooth : SmoothUpper f gradient L)
    (hcoercive : ∀ v, m * ‖v‖ ^ 2 ≤ inner ℝ (B v) v)
    (x z : E) (hprox : MetricProximalOptimality g gradient B x z) :
    composite f g z ≤ composite f g x - (m - L / 2) * ‖z - x‖ ^ 2 := by
  have hs := hsmooth x z
  have hp := hprox x
  have hneg : x - z = -(z - x) := by abel
  rw [hneg, inner_neg_right] at hp
  simp only [inner_sub_left, inner_neg_left] at hp
  have hc := hcoercive (z - x)
  dsimp [composite]
  nlinarith

/-- Every BFGS-metric proximal step inherits the variable-metric descent
bound, provided the current BFGS matrix has the stated lower bound. -/
theorem proximalBFGS_descent (f g : E → ℝ) (gradient : E → E)
    (L m : ℝ) (B : E →ₗ[ℝ] E) (s y x z : E)
    (hsmooth : SmoothUpper f gradient L)
    (hcoercive : ∀ v, m * ‖v‖ ^ 2 ≤
      inner ℝ (bfgsUpdateMap B s y v) v)
    (hprox : MetricProximalOptimality g gradient
      (bfgsUpdateMap B s y) x z) :
    composite f g z ≤ composite f g x -
      (m - L / 2) * ‖z - x‖ ^ 2 :=
  metricProximal_descent f g gradient L m (bfgsUpdateMap B s y)
    hsmooth hcoercive x z hprox

/-- Under uniform coercivity and a lower objective bound, the squared
displacements of a variable-metric proximal run are summable. In particular,
the step lengths tend to zero. This applies to a BFGS run whenever its
metrics satisfy the uniform bound assumed here. -/
theorem metricProximal_steps_summable (f g : E → ℝ)
    (gradient : E → E) (L m : ℝ) (x : ℕ → E)
    (B : ℕ → E →ₗ[ℝ] E)
    (hsmooth : SmoothUpper f gradient L)
    (hc : 0 < m - L / 2)
    (hcoercive : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (B k v) v)
    (hprox : ∀ k, MetricProximalOptimality g gradient (B k)
      (x k) (x (k + 1)))
    (lower : ℝ) (hlower : ∀ k, lower ≤ composite f g (x k)) :
    Summable (fun k => ‖x (k + 1) - x k‖ ^ 2) := by
  let c := m - L / 2
  have hdes (k : ℕ) : c * ‖x (k + 1) - x k‖ ^ 2 ≤
      composite f g (x k) - composite f g (x (k + 1)) := by
    have h := metricProximal_descent f g gradient L m (B k)
      hsmooth (hcoercive k) (x k) (x (k + 1)) (hprox k)
    dsimp [c]
    linarith
  have hsum (n : ℕ) : c * ∑ k ∈ Finset.range n, ‖x (k + 1) - x k‖ ^ 2 ≤
      composite f g (x 0) - composite f g (x n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hdes n]
  apply summable_of_sum_range_le (fun k => sq_nonneg _)
    (c := (composite f g (x 0) - lower) / c)
  intro n
  have h := hsum n
  have hb := hlower n
  dsimp [c] at h
  apply (le_div_iff₀ hc).2
  nlinarith

theorem metricProximal_steps_tendsto_zero (f g : E → ℝ)
    (gradient : E → E) (L m : ℝ) (x : ℕ → E)
    (B : ℕ → E →ₗ[ℝ] E)
    (hsmooth : SmoothUpper f gradient L)
    (hc : 0 < m - L / 2)
    (hcoercive : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (B k v) v)
    (hprox : ∀ k, MetricProximalOptimality g gradient (B k)
      (x k) (x (k + 1)))
    (lower : ℝ) (hlower : ∀ k, lower ≤ composite f g (x k)) :
    Filter.Tendsto (fun k => ‖x (k + 1) - x k‖ ^ 2)
      Filter.atTop (nhds 0) :=
  (metricProximal_steps_summable f g gradient L m x B hsmooth hc
    hcoercive hprox lower hlower).tendsto_atTop_zero

/-- A proximal BFGS run is geometrically convergent in objective value
when its composite error bound controls the objective gap by the squared
step length. For strongly convex composites, this error bound follows from
bounded metrics and a Lipschitz gradient. -/
theorem metricProximal_linear_rate (f g : E → ℝ)
    (gradient : E → E) (L m C : ℝ) (x : ℕ → E)
    (B : ℕ → E →ₗ[ℝ] E) (u : E)
    (hsmooth : SmoothUpper f gradient L)
    (hc : 0 < m - L / 2) (hC : 0 < C)
    (hcoercive : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (B k v) v)
    (hprox : ∀ k, MetricProximalOptimality g gradient (B k)
      (x k) (x (k + 1)))
    (herror : ∀ k, composite f g (x (k + 1)) - composite f g u ≤
      C * ‖x (k + 1) - x k‖ ^ 2)
    (k : ℕ) :
    composite f g (x k) - composite f g u ≤
      (C / (C + (m - L / 2))) ^ k *
        (composite f g (x 0) - composite f g u) := by
  let c := m - L / 2
  let q := C / (C + c)
  have hq : 0 ≤ q := by dsimp [q, c]; positivity
  have hden : 0 < C + c := by dsimp [c]; linarith
  have hstep (j : ℕ) : composite f g (x (j + 1)) - composite f g u ≤
      q * (composite f g (x j) - composite f g u) := by
    have hd := metricProximal_descent f g gradient L m (B j)
      hsmooth (hcoercive j) (x j) (x (j + 1)) (hprox j)
    have he := herror j
    have hscale := mul_le_mul_of_nonneg_left he hc.le
    dsimp [q, c]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < C + (m - L / 2))).2
    nlinarith [hscale]
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      composite f g (x (k + 1)) - composite f g u ≤
          q * (composite f g (x k) - composite f g u) := hstep k
      _ ≤ q * (q ^ k * (composite f g (x 0) - composite f g u)) :=
        mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (k + 1) * (composite f g (x 0) - composite f g u) := by
        rw [pow_succ]; ring

end QuasiNewtonConvergence

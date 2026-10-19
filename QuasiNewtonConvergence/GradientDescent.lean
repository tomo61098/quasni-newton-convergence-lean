module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import QuasiNewtonConvergence.Potential

@[expose] public section

/-!
# Fixed-step gradient descent

The gradient is supplied explicitly. The first-order inequalities below are
the usual consequences of differentiability, convexity, strong convexity,
and an `L`-Lipschitz gradient. The step size is `1 / L`.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gradientStep (gradient : E → E) (L : ℝ) (x : E) : E :=
  x - (1 / L) • gradient x

def SmoothUpper (f : E → ℝ) (gradient : E → E) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + inner ℝ (gradient x) (y - x) +
    L / 2 * ‖y - x‖ ^ 2

def ConvexFirstOrder (f : E → ℝ) (gradient : E → E) : Prop :=
  ∀ x y, f y ≥ f x + inner ℝ (gradient x) (y - x)

def StrongConvexFirstOrder (f : E → ℝ) (gradient : E → E) (μ : ℝ) : Prop :=
  ∀ x y, f y ≥ f x + inner ℝ (gradient x) (y - x) +
    μ / 2 * ‖y - x‖ ^ 2

private theorem step_sub (gradient : E → E) (L : ℝ) (x : E) :
    gradientStep gradient L x - x = -(1 / L) • gradient x := by
  simp [gradientStep, sub_eq_add_neg, add_assoc]

private theorem step_norm_sq (gradient : E → E) (L : ℝ) (x : E) :
    ‖gradientStep gradient L x - x‖ ^ 2 = (1 / L) ^ 2 * ‖gradient x‖ ^ 2 := by
  rw [step_sub, norm_smul, Real.norm_eq_abs, mul_pow]
  simp

/-- One step reduces the objective by at least `‖∇f(x)‖²/(2L)`. -/
theorem gradientStep_descent (f : E → ℝ) (gradient : E → E) (L : ℝ)
    (hL : 0 < L) (hsmooth : SmoothUpper f gradient L) (x : E) :
    f (gradientStep gradient L x) ≤ f x - ‖gradient x‖ ^ 2 / (2 * L) := by
  have h := hsmooth x (gradientStep gradient L x)
  rw [step_norm_sq, step_sub, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at h
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp at h ⊢
  nlinarith

private theorem step_distance_sq (gradient : E → E) (L : ℝ) (x minimizer : E) :
    ‖gradientStep gradient L x - minimizer‖ ^ 2 =
      ‖x - minimizer‖ ^ 2 - 2 / L * inner ℝ (gradient x) (x - minimizer) +
        (1 / L) ^ 2 * ‖gradient x‖ ^ 2 := by
  have heq : gradientStep gradient L x - minimizer =
      (x - minimizer) + -(1 / L) • gradient x := by
    simp [gradientStep, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [heq, norm_add_sq_real, real_inner_smul_right, real_inner_comm,
    norm_smul, Real.norm_eq_abs, mul_pow]
  simp
  ring

/-- The objective gap after one step is paid for by squared distance to a
minimizer. This is the standard telescoping inequality for convex descent. -/
theorem gradientStep_convex_potential (f : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient) (x minimizer : E) :
    f (gradientStep gradient L x) - f minimizer ≤
      L / 2 * (‖x - minimizer‖ ^ 2 -
        ‖gradientStep gradient L x - minimizer‖ ^ 2) := by
  have hconv := hconvex x minimizer
  have hneg : minimizer - x = -(x - minimizer) := by abel
  rw [hneg, inner_neg_right] at hconv
  have hdesc := gradientStep_descent f gradient L hL hsmooth x
  have hdist := step_distance_sq gradient L x minimizer
  have hLne : L ≠ 0 := ne_of_gt hL
  have hbound : f (gradientStep gradient L x) - f minimizer ≤
      inner ℝ (gradient x) (x - minimizer) - ‖gradient x‖ ^ 2 / (2 * L) := by
    linarith
  have heq : inner ℝ (gradient x) (x - minimizer) - ‖gradient x‖ ^ 2 / (2 * L) =
      L / 2 * (‖x - minimizer‖ ^ 2 -
        ‖gradientStep gradient L x - minimizer‖ ^ 2) := by
    rw [hdist]
    field_simp
    ring
  exact le_trans hbound heq.le

/-- For a convex objective, the objective gap after `k+1` steps is at most
`L ‖x₀-x★‖² / (2(k+1))`. -/
theorem gradientDescent_convex_rate (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L : ℝ)
    (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k))
    (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * (f (x (k + 1)) - f minimizer) ≤
      L / 2 * ‖x 0 - minimizer‖ ^ 2 := by
  have hmono (j : ℕ) : f (x (j + 1)) ≤ f (x j) := by
    rw [hstep j]
    have h := gradientStep_descent f gradient L hL hsmooth (x j)
    nlinarith [div_nonneg (sq_nonneg ‖gradient (x j)‖)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL.le)]
  apply potential_last_iterate_bound
    (fun j => f (x j) - f minimizer)
    (fun j => L / 2 * ‖x j - minimizer‖ ^ 2)
    (fun j => sub_le_sub_right (hmono j) (f minimizer))
  · intro j
    have hp := gradientStep_convex_potential f gradient L hL hsmooth
      hconvex (x j) minimizer
    rw [← hstep j, mul_sub] at hp
    exact hp
  · intro j
    exact mul_nonneg (div_nonneg hL.le (by norm_num)) (sq_nonneg _)

/-- Strong convexity gives a Polyak–Łojasiewicz bound at a minimizer. -/
theorem strongConvex_gradient_bound (f : E → ℝ) (gradient : E → E)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : StrongConvexFirstOrder f gradient μ)
    (x minimizer : E) :
    2 * μ * (f x - f minimizer) ≤ ‖gradient x‖ ^ 2 := by
  have h := hstrong x minimizer
  have hneg : minimizer - x = -(x - minimizer) := by abel
  rw [hneg, inner_neg_right, norm_neg] at h
  have hc := real_inner_le_norm (gradient x) (x - minimizer)
  have hmul := mul_le_mul_of_nonneg_left h hμ.le
  have hcmul := mul_le_mul_of_nonneg_left hc hμ.le
  nlinarith [sq_nonneg (‖gradient x‖ - μ * ‖x - minimizer‖)]

/-- A fixed step contracts the objective gap by `1 - μ/L`. -/
theorem gradientStep_strong_contraction (f : E → ℝ) (gradient : E → E)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x minimizer : E) :
    f (gradientStep gradient L x) - f minimizer ≤
      (1 - μ / L) * (f x - f minimizer) := by
  have hd := gradientStep_descent f gradient L hL hsmooth x
  have hg := strongConvex_gradient_bound f gradient μ hμ hstrong x minimizer
  have hLne : L ≠ 0 := ne_of_gt hL
  have hscaled := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hL.le)
  field_simp at hd hscaled ⊢
  nlinarith

/-- Geometric convergence of objective values for strongly convex descent. -/
theorem gradientDescent_strong_rate (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k))
    (k : ℕ) :
    f (x k) - f minimizer ≤
      (1 - μ / L) ^ k * (f (x 0) - f minimizer) := by
  have hq : 0 ≤ 1 - μ / L := by
    apply sub_nonneg.mpr
    exact (div_le_one hL).mpr hμL
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hstep k]
    have hc := gradientStep_strong_contraction f gradient L μ hL hμ hsmooth
      hstrong (x k) minimizer
    calc
      f (gradientStep gradient L (x k)) - f minimizer ≤
          (1 - μ / L) * (f (x k) - f minimizer) := hc
      _ ≤ (1 - μ / L) * ((1 - μ / L) ^ k *
            (f (x 0) - f minimizer)) := mul_le_mul_of_nonneg_left ih hq
      _ = (1 - μ / L) ^ (k + 1) * (f (x 0) - f minimizer) := by
        rw [pow_succ]; ring

/-- Convex gradient descent converges in objective value. -/
theorem gradientDescent_convex_tendsto (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L : ℝ)
    (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  have hupper : Filter.Tendsto
      (fun k : ℕ => (L / 2 * ‖x 0 - minimizer‖ ^ 2) / ((k : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := L / 2 * ‖x 0 - minimizer‖ ^ 2)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgap : Filter.Tendsto (fun k => f (x (k + 1)) - f minimizer)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k
      linarith [hmin (x (k + 1))]
    · intro k
      have hr := gradientDescent_convex_rate f gradient x minimizer L
        hL hsmooth hconvex hstep k
      apply (le_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ) + 1)).2
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hr
  have hshift : Filter.Tendsto (fun k => f (x (k + 1)))
      Filter.atTop (nhds (f minimizer)) := by
    simpa only [sub_add_cancel, zero_add] using hgap.add_const (f minimizer)
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 (by simpa using hshift)

/-- Strongly convex gradient descent converges geometrically in objective
value, and therefore converges to the minimum value. -/
theorem gradientDescent_strong_tendsto (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  have hq0 : 0 ≤ 1 - μ / L := sub_nonneg.mpr ((div_le_one hL).mpr hμL)
  have hq1 : 1 - μ / L < 1 := by
    have : 0 < μ / L := div_pos hμ hL
    linarith
  have hp : Filter.Tendsto
      (fun k : ℕ => (1 - μ / L) ^ k * (f (x 0) - f minimizer))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (f (x 0) - f minimizer)
  have hgap : Filter.Tendsto (fun k => f (x k) - f minimizer)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp
    · intro k
      linarith [hmin (x k)]
    · intro k
      exact gradientDescent_strong_rate f gradient x minimizer L μ hL hμ hμL
        hsmooth hstrong hstep k
  simpa only [sub_add_cancel, zero_add] using hgap.add_const (f minimizer)

/-- Strong convexity and a stationary minimizer turn the geometric objective
rate into convergence of the iterates. -/
theorem gradientDescent_strong_iterates_tendsto (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstationary : gradient minimizer = 0)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k)) :
    Filter.Tendsto x Filter.atTop (nhds minimizer) := by
  have hmin (y : E) : f minimizer ≤ f y := by
    have h := hstrong minimizer y
    simp only [hstationary, inner_zero_left] at h
    nlinarith [mul_nonneg (div_nonneg hμ.le (by norm_num : (0:ℝ) ≤ 2))
      (sq_nonneg ‖y - minimizer‖)]
  have hval := gradientDescent_strong_tendsto f gradient x minimizer L μ hL hμ
    hμL hsmooth hstrong hmin hstep
  have hgap : Filter.Tendsto (fun k => f (x k) - f minimizer)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hval.sub_const (f minimizer)
  have hnormsq : Filter.Tendsto (fun k => ‖x k - minimizer‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hbound : ∀ k, ‖x k - minimizer‖ ^ 2 ≤
        (2 / μ) * (f (x k) - f minimizer) := by
      intro k
      have h := hstrong minimizer (x k)
      simp only [hstationary, inner_zero_left] at h
      calc
        _ ≤ (2 * (f (x k) - f minimizer)) / μ :=
          (le_div_iff₀ hμ).2 (by nlinarith)
        _ = _ := by ring
    have hupper : Filter.Tendsto
        (fun k => (2 / μ) * (f (x k) - f minimizer))
        Filter.atTop (nhds 0) := by
      simpa using hgap.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact sq_nonneg _
    · intro k; exact hbound k
  have hnorm : Filter.Tendsto (fun k => ‖x k - minimizer‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hnormsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end QuasiNewtonConvergence

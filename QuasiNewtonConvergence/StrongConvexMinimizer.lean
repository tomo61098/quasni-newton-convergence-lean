import QuasiNewtonConvergence.GradientDescent
import QuasiNewtonConvergence.DiminishingGradientDescent
import QuasiNewtonConvergence.LineSearch
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Existence of a minimizer for a smooth strongly convex objective

Completeness matters: the gradient descent sequence constructed below has a
limit in the ambient space only when the space is complete.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The strong first-order inequality makes the gradient strongly monotone. -/
theorem strongConvex_gradient_monotone (f : E → ℝ) (gradient : E → E)
    (μ : ℝ) (hstrong : StrongConvexFirstOrder f gradient μ) (x y : E) :
    μ * ‖x - y‖ ^ 2 ≤ inner ℝ (gradient x - gradient y) (x - y) := by
  have hxy := hstrong x y
  have hyx := hstrong y x
  have hneg : y - x = -(x - y) := by abel
  rw [hneg, inner_neg_right, norm_neg] at hxy
  rw [inner_sub_left]
  nlinarith [norm_sub_rev x y, real_inner_comm (gradient y) (x - y)]

/-- Distance between two points is controlled by their gradient norms. -/
theorem strongConvex_distance_le_gradients (f : E → ℝ) (gradient : E → E)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : StrongConvexFirstOrder f gradient μ)
    (x y : E) :
    ‖x - y‖ ≤ (‖gradient x‖ + ‖gradient y‖) / μ := by
  have hm := strongConvex_gradient_monotone f gradient μ hstrong x y
  have hc := real_inner_le_norm (gradient x - gradient y) (x - y)
  have ht := norm_sub_le (gradient x) (gradient y)
  have hd : ‖x - y‖ ≤ (‖gradient x - gradient y‖) / μ := by
    by_cases hz : ‖x - y‖ = 0
    · rw [hz]
      exact div_nonneg (norm_nonneg _) hμ.le
    · have hp : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (le_div_iff₀ hμ).2
      by_contra hn
      have hlt : ‖gradient x - gradient y‖ < ‖x - y‖ * μ := lt_of_not_ge hn
      have hprod := mul_pos (sub_pos.mpr hlt) hp
      nlinarith
  exact hd.trans (div_le_div_of_nonneg_right ht hμ.le)

/-- Fixed-step descent on a smooth strongly convex objective has gradients
whose norms tend to zero, without assuming a minimizer in advance. -/
theorem gradientDescent_gradient_tendsto_zero (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k)) :
    Filter.Tendsto (fun k => ‖gradient (x k)‖) Filter.atTop (nhds 0) := by
  have hlower (k : ℕ) :
      f (x 0) - ‖gradient (x 0)‖ ^ 2 / (2 * μ) ≤ f (x k) := by
    have h := strongConvex_gradient_bound f gradient μ hμ hstrong (x 0) (x k)
    have hb : f (x 0) - f (x k) ≤ ‖gradient (x 0)‖ ^ 2 / (2 * μ) := by
      apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hμ)).2
      nlinarith
    linarith
  have hsum : Summable (fun k => ‖gradient (x k)‖ ^ 2) := by
    apply summable_of_descent (fun k => f (x k))
      (fun k => ‖gradient (x k)‖ ^ 2)
      (f (x 0) - ‖gradient (x 0)‖ ^ 2 / (2 * μ))
      (1 / (2 * L)) (one_div_pos.mpr (mul_pos (by norm_num) hL))
    · intro k; exact sq_nonneg _
    · exact hlower
    · intro k
      have h := gradientStep_descent f gradient L hL hsmooth (x k)
      rw [← hstep k] at h
      calc
        (1 / (2 * L)) * ‖gradient (x k)‖ ^ 2 =
            ‖gradient (x k)‖ ^ 2 / (2 * L) := by ring
        _ ≤ f (x k) - f (x (k + 1)) := by linarith
  have hsq := hsum.tendsto_atTop_zero
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- The fixed-step gradient descent sequence is Cauchy by strong monotonicity. -/
theorem gradientDescent_cauchySeq_of_strongConvex (f : E → ℝ)
    (gradient : E → E) (x : ℕ → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k)) :
    CauchySeq x := by
  have hg := gradientDescent_gradient_tendsto_zero f gradient x L μ hL hμ
    hsmooth hstrong hstep
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hevent : ∀ᶠ k in Filter.atTop,
      ‖gradient (x k)‖ < μ * ε / 2 :=
    hg.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have hd := strongConvex_distance_le_gradients f gradient μ hμ hstrong (x m) (x n)
  have hb := (le_div_iff₀ hμ).mp hd
  nlinarith [hN m hm, hN n hn]

/-- Smoothness and the strong first-order lower bound squeeze objective values
when points converge. -/
theorem objective_tendsto_of_points_tendsto
    (f : E → ℝ) (gradient : E → E) (x : ℕ → E) (limit : E)
    (L μ : ℝ) (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hx : Filter.Tendsto x Filter.atTop (nhds limit)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f limit)) := by
  have hsub : Filter.Tendsto (fun k => x k - limit)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hx.sub_const limit
  have hinner : Filter.Tendsto
      (fun k => inner ℝ (gradient limit) (x k - limit))
      Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.inner
      (tendsto_const_nhds (x := gradient limit)) hsub)
  have hnorm : Filter.Tendsto (fun k => ‖x k - limit‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hsub.norm.pow 2
  have hlow : Filter.Tendsto (fun k =>
      f limit + inner ℝ (gradient limit) (x k - limit) +
        μ / 2 * ‖x k - limit‖ ^ 2)
      Filter.atTop (nhds (f limit)) := by
    convert ((tendsto_const_nhds.add hinner).add
      (tendsto_const_nhds.mul hnorm)) using 1; simp
  have hupp : Filter.Tendsto (fun k =>
      f limit + inner ℝ (gradient limit) (x k - limit) +
        L / 2 * ‖x k - limit‖ ^ 2)
      Filter.atTop (nhds (f limit)) := by
    convert ((tendsto_const_nhds.add hinner).add
      (tendsto_const_nhds.mul hnorm)) using 1; simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro k; exact hstrong limit (x k)
  · intro k; exact hsmooth limit (x k)

/-- A smooth strongly convex objective on a complete real inner product
space has a stationary global minimizer. -/
theorem exists_strongConvex_minimizer
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ) :
    ∃ minimizer : E, gradient minimizer = 0 ∧
      ∀ y, f minimizer ≤ f y := by
  let x : ℕ → E := fun k => (gradientStep gradient L)^[k] 0
  have hstep (k : ℕ) : x (k + 1) = gradientStep gradient L (x k) := by
    simp [x, Function.iterate_succ_apply']
  have hc := gradientDescent_cauchySeq_of_strongConvex f gradient x L μ
    hL hμ hsmooth hstrong hstep
  obtain ⟨minimizer, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hg := gradientDescent_gradient_tendsto_zero f gradient x L μ
    hL hμ hsmooth hstrong hstep
  have hf := objective_tendsto_of_points_tendsto f gradient x minimizer
    L μ hsmooth hstrong hx
  have hmin (y : E) : f minimizer ≤ f y := by
    have hbound (k : ℕ) :
        f (x k) - f y ≤ ‖gradient (x k)‖ ^ 2 / (2 * μ) := by
      have hb := strongConvex_gradient_bound f gradient μ hμ hstrong (x k) y
      apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hμ)).2
      nlinarith
    have hlim := le_of_tendsto_of_tendsto
      (hf.sub_const (f y)) ((hg.pow 2).div_const (2 * μ))
      (Filter.Eventually.of_forall hbound)
    have : f minimizer - f y ≤ 0 := by simpa using hlim
    linarith
  have hstationary : gradient minimizer = 0 := by
    have hd := gradientStep_descent f gradient L hL hsmooth minimizer
    have hm := hmin (gradientStep gradient L minimizer)
    have hsq : ‖gradient minimizer‖ ^ 2 ≤ 0 := by
      have hLpos : 0 < 2 * L := mul_pos (by norm_num) hL
      have hdiv : ‖gradient minimizer‖ ^ 2 / (2 * L) ≤ 0 := by linarith
      exact (div_le_iff₀ hLpos).mp hdiv |>.trans_eq (by ring)
    have hn : ‖gradient minimizer‖ = 0 := by
      nlinarith [norm_nonneg (gradient minimizer)]
    exact norm_eq_zero.mp hn
  exact ⟨minimizer, hstationary, hmin⟩

/-- The minimizer of a smooth strongly convex objective is unique. -/
theorem existsUnique_strongConvex_minimizer
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ) :
    ∃! minimizer : E, ∀ y, f minimizer ≤ f y := by
  obtain ⟨minimizer, hstationary, hmin⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  refine ⟨minimizer, hmin, ?_⟩
  intro y hy
  have h := hstrong minimizer y
  simp only [hstationary, inner_zero_left] at h
  have heq : f y = f minimizer := le_antisymm (hy minimizer) (hmin y)
  have hnorm : ‖y - minimizer‖ = 0 := by
    by_contra hz
    have hp : 0 < ‖y - minimizer‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hprod : 0 < μ / 2 * ‖y - minimizer‖ ^ 2 :=
      mul_pos (div_pos hμ (by norm_num)) (sq_pos_of_pos hp)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Square-root-step gradient descent converges to the unique minimizer.
The minimizer and its stationarity are consequences of the hypotheses. -/
theorem gradientDescent_sqrt_strong_converges
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize gradient (sqrtStepSize k) (x k)) :
    ∃ minimizer : E, (∀ y, f minimizer ≤ f y) ∧
      Filter.Tendsto x Filter.atTop (nhds minimizer) := by
  obtain ⟨minimizer, hstationary, hmin⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  exact ⟨minimizer, hmin,
    gradientDescent_sqrt_strong_iterates_tendsto f gradient x minimizer L μ
      hL hμ hsmooth hstrong hstationary hstep⟩

/-- The fixed-step version also converges without a supplied minimizer. -/
theorem gradientDescent_strong_converges
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstep : ∀ k, x (k + 1) = gradientStep gradient L (x k)) :
    ∃ minimizer : E, (∀ y, f minimizer ≤ f y) ∧
      Filter.Tendsto x Filter.atTop (nhds minimizer) := by
  obtain ⟨minimizer, hstationary, hmin⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  exact ⟨minimizer, hmin,
    gradientDescent_strong_iterates_tendsto f gradient x minimizer L μ
      hL hμ hμL hsmooth hstrong hstationary hstep⟩

end QuasiNewtonConvergence

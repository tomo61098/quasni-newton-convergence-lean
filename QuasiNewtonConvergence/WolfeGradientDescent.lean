module

public import QuasiNewtonConvergence.StrongConvexMinimizer

@[expose] public section

/-!
# Steepest descent with weak Wolfe line searches

The direction is `-gradient (x k)`. A stationary iterate is allowed; its
direction is zero and the Armijo condition prevents an objective increase.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The global quadratic upper bound and convex first-order inequality imply
the usual Lipschitz gradient estimate. -/
theorem smoothUpper_gradient_lipschitz (f : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient) (x y : E) :
    ‖gradient y - gradient x‖ ≤ L * ‖y - x‖ := by
  let φ : E → ℝ := fun z => f z - inner ℝ (gradient x) z
  let gφ : E → E := fun z => gradient z - gradient x
  have hsφ : SmoothUpper φ gφ L := by
    intro u v
    have h := hsmooth u v
    dsimp [φ, gφ]
    simp only [inner_sub_left, inner_sub_right]
    rw [inner_sub_right] at h
    linarith
  let z := gradientStep gφ L y
  have hdesc := gradientStep_descent φ gφ L hL hsφ y
  have hmin : φ x ≤ φ z := by
    have h := hconvex x z
    dsimp [φ]
    rw [inner_sub_right] at h
    linarith
  have hupper : φ y - φ x ≤ L / 2 * ‖y - x‖ ^ 2 := by
    have h := hsmooth x y
    dsimp [φ]
    rw [inner_sub_right] at h
    linarith
  have hsq : ‖gradient y - gradient x‖ ^ 2 ≤ L ^ 2 * ‖y - x‖ ^ 2 := by
    have hchain : ‖gradient y - gradient x‖ ^ 2 / (2 * L) ≤
        L / 2 * ‖y - x‖ ^ 2 := by
      dsimp [gφ] at hdesc
      linarith
    have hL2 : 0 < 2 * L := mul_pos (by norm_num) hL
    have hscaled := (div_le_iff₀ hL2).mp hchain
    nlinarith
  have hnonneg : 0 ≤ L * ‖y - x‖ := mul_nonneg hL.le (norm_nonneg _)
  nlinarith [sq_nonneg (‖gradient y - gradient x‖ - L * ‖y - x‖)]

/-- One weak Wolfe step along `-g` pays for a fixed multiple of `‖g‖²`.
The directional Lipschitz bound follows from a Lipschitz gradient. -/
theorem wolfe_steepest_descent_bound
    (g gNext : E) (L c₁ c₂ α f fNext : ℝ)
    (hL : 0 < L) (hc₁ : 0 < c₁) (hc₂ : c₂ < 1)
    (hw : WolfeStep c₁ c₂ α
      (inner ℝ g (-g)) (inner ℝ gNext (-g)) f fNext)
    (hLip : inner ℝ gNext (-g) - inner ℝ g (-g) ≤
      L * α * ‖g‖ ^ 2) :
    (c₁ * (1 - c₂) / L) * ‖g‖ ^ 2 ≤ f - fNext := by
  have hdir : inner ℝ g (-g) = -‖g‖ ^ 2 := by
    rw [inner_neg_right, real_inner_self_eq_norm_sq]
  by_cases hg : g = 0
  · subst g
    simpa [WolfeStep] using hw.armijo
  · have hd : 0 < ‖g‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
    have hb := wolfe_descent_bound c₁ c₂ L α (inner ℝ g (-g))
      (inner ℝ gNext (-g)) (‖g‖ ^ 2) f fNext
      hc₁ hc₂ hL (by rw [hdir]; linarith) hd hw hLip
    rw [hdir] at hb
    have hcancel : c₁ * (1 - c₂) * ‖g‖ ^ 2 ≤ L * (f - fNext) := by
      by_contra hn
      have ht : L * (f - fNext) < c₁ * (1 - c₂) * ‖g‖ ^ 2 :=
        lt_of_not_ge hn
      have hp := mul_pos (sub_pos.mpr ht) hd
      nlinarith [hb]
    calc
      (c₁ * (1 - c₂) / L) * ‖g‖ ^ 2 =
          (c₁ * (1 - c₂) * ‖g‖ ^ 2) / L := by ring
      _ ≤ f - fNext := (div_le_iff₀ hL).2 (by nlinarith [hcancel])

/-- Weak Wolfe steepest descent converges to the unique minimizer of a smooth
strongly convex objective on a complete inner product space. -/
theorem gradientDescent_wolfe_strong_converges
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (α : ℕ → ℝ) (L μ c₁ c₂ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hc₁ : 0 < c₁) (hc₂ : c₂ < 1)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hα : ∀ k, 0 ≤ α k)
    (hstep : ∀ k, x (k + 1) = x k + α k • (-gradient (x k)))
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (α k)
      (inner ℝ (gradient (x k)) (-gradient (x k)))
      (inner ℝ (gradient (x (k + 1))) (-gradient (x k)))
      (f (x k)) (f (x (k + 1)))) :
    ∃ minimizer : E, (∀ y, f minimizer ≤ f y) ∧
      Filter.Tendsto x Filter.atTop (nhds minimizer) ∧
      Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  obtain ⟨minimizer, hstationary, hmin⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  have hgradientLip (u v : E) :
      ‖gradient v - gradient u‖ ≤ L * ‖v - u‖ :=
    smoothUpper_gradient_lipschitz f gradient L hL hsmooth
      (StrongConvexFirstOrder.toConvexFirstOrder f gradient μ hμ hstrong) u v
  have hdescent (k : ℕ) :
      (c₁ * (1 - c₂) / L) * ‖gradient (x k)‖ ^ 2 ≤
        f (x k) - f (x (k + 1)) := by
    let g := gradient (x k)
    have hdist : ‖x (k + 1) - x k‖ = α k * ‖g‖ := by
      rw [hstep k]
      simp [g, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα k)]
    have hgrad : ‖gradient (x (k + 1)) - g‖ ≤ L * α k * ‖g‖ := by
      calc
        _ ≤ L * ‖x (k + 1) - x k‖ := hgradientLip (x k) (x (k + 1))
        _ = L * α k * ‖g‖ := by rw [hdist]; ring
    have hdir := directional_derivative_lipschitz g
      (gradient (x (k + 1))) (-g) L (α k) (by simpa only [norm_neg] using hgrad)
    exact wolfe_steepest_descent_bound g (gradient (x (k + 1))) L c₁ c₂
      (α k) (f (x k)) (f (x (k + 1))) hL hc₁ hc₂ (hWolfe k)
      (by simpa only [norm_neg] using hdir)
  have hrate : 0 < c₁ * (1 - c₂) / L :=
    div_pos (mul_pos hc₁ (sub_pos.mpr hc₂)) hL
  have hsum : Summable (fun k => ‖gradient (x k)‖ ^ 2) := by
    exact summable_of_descent (fun k => f (x k))
      (fun k => ‖gradient (x k)‖ ^ 2) (f minimizer)
      (c₁ * (1 - c₂) / L) hrate
      (fun k => sq_nonneg _) (fun k => hmin (x k)) hdescent
  have hg : Filter.Tendsto (fun k => ‖gradient (x k)‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsum.tendsto_atTop_zero
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hx : Filter.Tendsto x Filter.atTop (nhds minimizer) := by
    have hbound (k : ℕ) : ‖x k - minimizer‖ ≤ ‖gradient (x k)‖ / μ := by
      have hd := strongConvex_distance_le_gradients f gradient μ hμ
        hstrong (x k) minimizer
      simpa only [hstationary, norm_zero, add_zero] using hd
    have hupper : Filter.Tendsto (fun k => ‖gradient (x k)‖ / μ)
        Filter.atTop (nhds 0) := by
      simpa using hg.div_const μ
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact norm_nonneg _
    · intro k; exact hbound k
  exact ⟨minimizer, hmin, hx,
    objective_tendsto_of_points_tendsto f gradient x minimizer L μ
      hsmooth hstrong hx⟩

end QuasiNewtonConvergence

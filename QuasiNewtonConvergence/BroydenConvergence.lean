import QuasiNewtonConvergence.BroydenUpdates
import QuasiNewtonConvergence.LineSearch
import QuasiNewtonConvergence.StrongConvexMinimizer
import QuasiNewtonConvergence.Newton

/-!
# Conditional line-search convergence for quasi-Newton directions

The result here applies to BFGS, DFP, or SR1 sequences when their inverse
approximations obey uniform coercivity and norm bounds. These bounds are
explicit assumptions; they do not follow from a secant equation alone.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A quasi-Newton search direction from an inverse Hessian approximation. -/
def quasiNewtonDirection (H : E →L[ℝ] E) (g : E) : E := -(H g)

/-- A line-search quasi-Newton iteration with a chosen Hessian update at
each step. `H` is the inverse used for the search direction. -/
structure QuasiNewtonRun (gradient : E → E) where
  x : ℕ → E
  B : ℕ → E →ₗ[ℝ] E
  H : ℕ → E →L[ℝ] E
  α : ℕ → ℝ
  method : ℕ → HessianUpdateMethod
  step : ∀ k, x (k + 1) = x k + α k • quasiNewtonDirection (H k) (gradient (x k))
  update : ∀ k, B (k + 1) = hessianUpdate (method k) (B k)
    (x (k + 1) - x k) (gradient (x (k + 1)) - gradient (x k))
  leftInverse : ∀ k v, H k (B k v) = v
  rightInverse : ∀ k v, B k (H k v) = v

/-- Uniform coercivity and boundedness of inverse approximations force
the normalized Wolfe descent weight to control the gradient norm. -/
theorem quasiNewton_direction_weight_bound (H : E →L[ℝ] E) (g : E)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M) (hg : g ≠ 0)
    (hcoercive : m * ‖g‖ ^ 2 ≤ inner ℝ g (H g))
    (hbound : ‖H‖ ≤ M) :
    (m / M) ^ 2 * ‖g‖ ^ 2 ≤
      (inner ℝ g (quasiNewtonDirection H g)) ^ 2 /
        ‖quasiNewtonDirection H g‖ ^ 2 := by
  let p := quasiNewtonDirection H g
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hp : 0 < ‖p‖ := by
    have hinner : 0 < inner ℝ g (H g) :=
      lt_of_lt_of_le (mul_pos hm (sq_pos_of_pos hgpos)) hcoercive
    have hne : H g ≠ 0 := by
      intro hz
      simp [hz] at hinner
    simpa [p, quasiNewtonDirection] using (norm_pos_iff.mpr hne)
  have hpbound : ‖p‖ ≤ M * ‖g‖ := by
    calc
      ‖p‖ = ‖H g‖ := by simp [p, quasiNewtonDirection]
      _ ≤ ‖H‖ * ‖g‖ := H.le_opNorm g
      _ ≤ M * ‖g‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  have hratio : (m / M) * ‖g‖ ≤
      -(inner ℝ g p) / ‖p‖ := by
    apply (le_div_iff₀ hp).2
    have hmul := mul_le_mul_of_nonneg_left hpbound
      (mul_nonneg (div_nonneg hm.le hM.le) (norm_nonneg g))
    have hvalue : -(inner ℝ g p) = inner ℝ g (H g) := by
      simp [p, quasiNewtonDirection]
    rw [hvalue]
    calc
      m / M * ‖g‖ * ‖p‖ ≤ m / M * ‖g‖ * (M * ‖g‖) := hmul
      _ = m * ‖g‖ ^ 2 := by field_simp
      _ ≤ inner ℝ g (H g) := hcoercive
  have hpow := pow_le_pow_left₀
    (mul_nonneg (div_nonneg hm.le hM.le) (norm_nonneg _)) hratio 2
  simpa only [mul_pow, neg_pow, Even.neg_pow (by decide : Even (2 : ℕ)), div_pow] using hpow

/-- A nonstationary quasi-Newton run with weak Wolfe steps has gradients
tending to zero if its inverse approximations are uniformly positive and
bounded. The update rule for `H` may be BFGS, DFP, or safeguarded SR1. -/
theorem quasiNewton_wolfe_gradient_tendsto
    (f : E → ℝ) (gradient : E → E) (x : ℕ → E)
    (H : ℕ → E →L[ℝ] E) (α : ℕ → ℝ)
    (lower c₁ c₂ L m M : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (hL : 0 < L)
    (hm : 0 < m) (hM : 0 < M)
    (hα : ∀ k, 0 ≤ α k)
    (hstep : ∀ k, x (k + 1) = x k + α k •
      quasiNewtonDirection (H k) (gradient (x k)))
    (hnotstationary : ∀ k, gradient (x k) ≠ 0)
    (hcoercive : ∀ k, m * ‖gradient (x k)‖ ^ 2 ≤
      inner ℝ (gradient (x k)) (H k (gradient (x k))))
    (hbound : ∀ k, ‖H k‖ ≤ M)
    (hlower : ∀ k, lower ≤ f (x k))
    (hgradientLip : ∀ u v, ‖gradient v - gradient u‖ ≤ L * ‖v - u‖)
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (α k)
      (inner ℝ (gradient (x k))
        (quasiNewtonDirection (H k) (gradient (x k))))
      (inner ℝ (gradient (x (k + 1)))
        (quasiNewtonDirection (H k) (gradient (x k))))
      (f (x k)) (f (x (k + 1)))) :
    Filter.Tendsto (fun k => ‖gradient (x k)‖) Filter.atTop (nhds 0) := by
  let p : ℕ → E := fun k => quasiNewtonDirection (H k) (gradient (x k))
  have hdescent (k : ℕ) : inner ℝ (gradient (x k)) (p k) < 0 := by
    have hgpos : 0 < ‖gradient (x k)‖ := norm_pos_iff.mpr (hnotstationary k)
    have hinner : 0 < inner ℝ (gradient (x k)) (H k (gradient (x k))) :=
      lt_of_lt_of_le (mul_pos hm (sq_pos_of_pos hgpos)) (hcoercive k)
    simpa [p, quasiNewtonDirection] using (neg_lt_zero.mpr hinner)
  have hsum := zoutendijk_of_lipschitz_gradient f gradient x p α lower c₁ c₂ L
    hc₁ hc₂ hL hα hstep hdescent hlower hgradientLip hWolfe
  have hθ : 0 < (m / M) ^ 2 := sq_pos_of_pos (div_pos hm hM)
  have hsumgrad : Summable (fun k => ‖gradient (x k)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => ?_) (hsum.mul_left (1 / (m / M) ^ 2))
    have hw := quasiNewton_direction_weight_bound (H k) (gradient (x k))
      m M hm hM (hnotstationary k) (hcoercive k) (hbound k)
    calc
      ‖gradient (x k)‖ ^ 2 =
          (1 / (m / M) ^ 2) * ((m / M) ^ 2 * ‖gradient (x k)‖ ^ 2) := by
            field_simp
      _ ≤ (1 / (m / M) ^ 2) *
          ((inner ℝ (gradient (x k)) (p k)) ^ 2 / ‖p k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsumgrad.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- The stationary case is handled by the fact that a zero gradient produces
a zero quasi-Newton direction and all subsequent iterates stay fixed. -/
theorem quasiNewton_wolfe_gradient_tendsto_all
    (f : E → ℝ) (gradient : E → E) (x : ℕ → E)
    (H : ℕ → E →L[ℝ] E) (α : ℕ → ℝ)
    (lower c₁ c₂ L m M : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (hL : 0 < L)
    (hm : 0 < m) (hM : 0 < M)
    (hα : ∀ k, 0 ≤ α k)
    (hstep : ∀ k, x (k + 1) = x k + α k •
      quasiNewtonDirection (H k) (gradient (x k)))
    (hcoercive : ∀ k, m * ‖gradient (x k)‖ ^ 2 ≤
      inner ℝ (gradient (x k)) (H k (gradient (x k))))
    (hbound : ∀ k, ‖H k‖ ≤ M)
    (hlower : ∀ k, lower ≤ f (x k))
    (hgradientLip : ∀ u v, ‖gradient v - gradient u‖ ≤ L * ‖v - u‖)
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (α k)
      (inner ℝ (gradient (x k))
        (quasiNewtonDirection (H k) (gradient (x k))))
      (inner ℝ (gradient (x (k + 1)))
        (quasiNewtonDirection (H k) (gradient (x k))))
      (f (x k)) (f (x (k + 1)))) :
    Filter.Tendsto (fun k => ‖gradient (x k)‖) Filter.atTop (nhds 0) := by
  by_cases hnonzero : ∀ k, gradient (x k) ≠ 0
  · exact quasiNewton_wolfe_gradient_tendsto f gradient x H α
      lower c₁ c₂ L m M hc₁ hc₂ hL hm hM hα hstep hnonzero
      hcoercive hbound hlower hgradientLip hWolfe
  · push Not at hnonzero
    obtain ⟨k, hk⟩ := hnonzero
    have hfixed : ∀ j : ℕ, x (k + j) = x k := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Nat.add_succ, hstep (k + j), ih, hk]
        simp [quasiNewtonDirection]
    have hevent : (fun n => ‖gradient (x n)‖) =ᶠ[Filter.atTop]
        (fun _ : ℕ => (0 : ℝ)) := by
      apply Filter.eventually_atTop.2
      refine ⟨k, ?_⟩
      intro n hn
      have hnk : x n = x k := by
        simpa [Nat.add_sub_of_le hn] using hfixed (n - k)
      simp [hnk, hk]
    exact Filter.Tendsto.congr' hevent.symm tendsto_const_nhds

/-- Under strong convexity, the same conditional quasi-Newton guarantee
gives convergence of iterates and objective values to the stationary minimizer. -/
theorem quasiNewton_wolfe_strong_converges
    (f : E → ℝ) (gradient : E → E) (x : ℕ → E)
    (H : ℕ → E →L[ℝ] E) (α : ℕ → ℝ) (xstar : E)
    (lower c₁ c₂ L m M μ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (hL : 0 < L)
    (hm : 0 < m) (hM : 0 < M) (hμ : 0 < μ)
    (hα : ∀ k, 0 ≤ α k)
    (hstep : ∀ k, x (k + 1) = x k + α k •
      quasiNewtonDirection (H k) (gradient (x k)))
    (hcoercive : ∀ k, m * ‖gradient (x k)‖ ^ 2 ≤
      inner ℝ (gradient (x k)) (H k (gradient (x k))))
    (hbound : ∀ k, ‖H k‖ ≤ M)
    (hlower : ∀ k, lower ≤ f (x k))
    (hgradientLip : ∀ u v, ‖gradient v - gradient u‖ ≤ L * ‖v - u‖)
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (α k)
      (inner ℝ (gradient (x k))
        (quasiNewtonDirection (H k) (gradient (x k))))
      (inner ℝ (gradient (x (k + 1)))
        (quasiNewtonDirection (H k) (gradient (x k))))
      (f (x k)) (f (x (k + 1))))
    (hstationary : gradient xstar = 0)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ) :
    Filter.Tendsto x Filter.atTop (nhds xstar) ∧
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f xstar)) := by
  have hg := quasiNewton_wolfe_gradient_tendsto_all f gradient x H α
    lower c₁ c₂ L m M hc₁ hc₂ hL hm hM hα hstep
    hcoercive hbound hlower hgradientLip hWolfe
  have hx : Filter.Tendsto x Filter.atTop (nhds xstar) := by
    have hbound' (k : ℕ) : ‖x k - xstar‖ ≤ ‖gradient (x k)‖ / μ := by
      have hd := strongConvex_distance_le_gradients f gradient μ hμ
        hstrong (x k) xstar
      simpa only [hstationary, norm_zero, add_zero] using hd
    have hupper : Filter.Tendsto (fun k => ‖gradient (x k)‖ / μ)
        Filter.atTop (nhds 0) := by simpa using hg.div_const μ
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact norm_nonneg _
    · exact hbound'
  exact ⟨hx, objective_tendsto_of_points_tendsto f gradient x xstar
    L μ hsmooth hstrong hx⟩

/-- Convergence guarantee for an actual BFGS, DFP, SR1, or varying Broyden
update run. The update recurrence is part of `run`; uniform inverse bounds
remain separate hypotheses. -/
theorem QuasiNewtonRun.strong_converges
    (run : QuasiNewtonRun gradient)
    (f : E → ℝ) (xstar : E) (lower c₁ c₂ L m M μ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (hL : 0 < L)
    (hm : 0 < m) (hM : 0 < M) (hμ : 0 < μ)
    (hα : ∀ k, 0 ≤ run.α k)
    (hcoercive : ∀ k, m * ‖gradient (run.x k)‖ ^ 2 ≤
      inner ℝ (gradient (run.x k)) (run.H k (gradient (run.x k))))
    (hbound : ∀ k, ‖run.H k‖ ≤ M)
    (hlower : ∀ k, lower ≤ f (run.x k))
    (hgradientLip : ∀ u v, ‖gradient v - gradient u‖ ≤ L * ‖v - u‖)
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (run.α k)
      (inner ℝ (gradient (run.x k))
        (quasiNewtonDirection (run.H k) (gradient (run.x k))))
      (inner ℝ (gradient (run.x (k + 1)))
        (quasiNewtonDirection (run.H k) (gradient (run.x k))))
      (f (run.x k)) (f (run.x (k + 1))))
    (hstationary : gradient xstar = 0)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ) :
    Filter.Tendsto run.x Filter.atTop (nhds xstar) ∧
    Filter.Tendsto (fun k => f (run.x k)) Filter.atTop (nhds (f xstar)) :=
  quasiNewton_wolfe_strong_converges f gradient run.x run.H run.α xstar
    lower c₁ c₂ L m M μ hc₁ hc₂ hL hm hM hμ hα run.step hcoercive
    hbound hlower hgradientLip hWolfe hstationary hsmooth hstrong

/-- A local superlinear criterion for full quasi-Newton steps. The error in
the Hessian approximation along the current displacement tends to zero
relative to that displacement. This is stronger than the usual Dennis--Moré
condition on the actual steps, but applies uniformly to Broyden, DFP, and
safeguarded SR1 updates whenever the stated approximation holds. -/
theorem quasiNewton_full_step_superlinear
    (gradient : E → E) (hessian : E → E →L[ℝ] E)
    (B : ℕ → E →ₗ[ℝ] E) (H : ℕ → E →L[ℝ] E)
    (x : ℕ → E) (xstar : E) (δ : ℕ → ℝ) (L M : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hδnonneg : ∀ k, 0 ≤ δ k)
    (hderiv : ∀ y, HasFDerivAt gradient (hessian y) y)
    (hLip : ∀ y z, ‖hessian y - hessian z‖ ≤ L * ‖y - z‖)
    (hstationary : gradient xstar = 0)
    (hinverse : ∀ k v, H k (B k v) = v)
    (hbound : ∀ k, ‖H k‖ ≤ M)
    (happrox : ∀ k, ‖B k (x k - xstar) -
      hessian (x k) (x k - xstar)‖ ≤ δ k * ‖x k - xstar‖)
    (hstep : ∀ k, x (k + 1) = x k - H k (gradient (x k)))
    (hx : Filter.Tendsto x Filter.atTop (nhds xstar))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ‖x (k + 1) - xstar‖ / ‖x k - xstar‖)
      Filter.atTop (nhds 0) := by
  have herror (k : ℕ) : ‖x (k + 1) - xstar‖ ≤
      M * (δ k + L * ‖x k - xstar‖) * ‖x k - xstar‖ := by
    let e := x k - xstar
    have hrem := newton_gradient_remainder gradient hessian L (x k) xstar
      hL hderiv hLip
    have herr : x (k + 1) - xstar =
        H k (B k e - (gradient (x k) - gradient xstar)) := by
      rw [hstep k]
      simp only [map_sub, hinverse, hstationary, sub_zero]
      dsimp [e]
      abel
    rw [herr]
    have htri : ‖B k e - (gradient (x k) - gradient xstar)‖ ≤
        δ k * ‖e‖ + L * ‖e‖ ^ 2 := by
      calc
        _ = ‖(B k e - hessian (x k) e) +
            (hessian (x k) e - (gradient (x k) - gradient xstar))‖ := by
              congr 1; abel
        _ ≤ ‖B k e - hessian (x k) e‖ +
            ‖hessian (x k) e - (gradient (x k) - gradient xstar)‖ := norm_add_le _ _
        _ ≤ δ k * ‖e‖ + L * ‖e‖ ^ 2 := add_le_add (happrox k) hrem
    calc
      _ ≤ ‖H k‖ * ‖B k e - (gradient (x k) - gradient xstar)‖ :=
        (H k).le_opNorm _
      _ ≤ M * (δ k * ‖e‖ + L * ‖e‖ ^ 2) :=
        mul_le_mul (hbound k) htri (norm_nonneg _) hM
      _ = M * (δ k + L * ‖x k - xstar‖) * ‖x k - xstar‖ := by
        dsimp [e]; ring
  have he : Filter.Tendsto (fun k => ‖x k - xstar‖)
      Filter.atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hupper : Filter.Tendsto
      (fun k => M * (δ k + L * ‖x k - xstar‖))
      Filter.atTop (nhds 0) := by
    have h := hδ.add (Filter.Tendsto.const_mul L he)
    simpa using h.const_mul M
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro k
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro k
    by_cases he0 : ‖x k - xstar‖ = 0
    · have hzero : ‖x (k + 1) - xstar‖ = 0 := by
        have hh := herror k
        rw [he0] at hh
        have : 0 ≤ ‖x (k + 1) - xstar‖ := norm_nonneg _
        simpa using le_antisymm (by simpa using hh) this
      simp [he0, hzero, mul_nonneg hM (hδnonneg k)]
    · exact (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm he0))).2
        (by simpa [mul_comm] using herror k)

end QuasiNewtonConvergence

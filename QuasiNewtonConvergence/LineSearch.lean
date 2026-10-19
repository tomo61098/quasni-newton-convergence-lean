module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Wolfe line searches and summable descent

The scalar directional derivative is `g = ⟪∇f(x), p⟫`. The parameter `d`
represents `‖p‖²`. A Lipschitz gradient yields the directional derivative
bound used below; its vector form is proved separately.
-/

namespace QuasiNewtonConvergence

/-- Cauchy--Schwarz turns a bound on the change of gradient into the
directional derivative bound used in a Wolfe line search. -/
theorem directional_derivative_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g gNext p : E) (L α : ℝ)
    (hgrad : ‖gNext - g‖ ≤ L * α * ‖p‖) :
    inner ℝ gNext p - inner ℝ g p ≤ L * α * ‖p‖ ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right hgrad (norm_nonneg p)
  calc
    inner ℝ gNext p - inner ℝ g p = inner ℝ (gNext - g) p := by
      rw [inner_sub_left]
    _ ≤ ‖gNext - g‖ * ‖p‖ := real_inner_le_norm _ _
    _ ≤ (L * α * ‖p‖) * ‖p‖ := hmul
    _ = L * α * ‖p‖ ^ 2 := by ring

/-- A Wolfe line-search step, expressed through objective values and
directional derivatives. The second inequality is the weak curvature
condition. -/
structure WolfeStep (c₁ c₂ α g gNext f fNext : ℝ) : Prop where
  armijo : fNext ≤ f + c₁ * α * g
  curvature : c₂ * g ≤ gNext

/-- A weak Wolfe curvature condition makes the directional derivative
increase strictly along a descent direction when `c₂ < 1`. -/
theorem wolfe_directional_curvature_positive
    (c₂ g gNext : ℝ) (hc₂ : c₂ < 1) (hg : g < 0)
    (hcurvature : c₂ * g ≤ gNext) :
    0 < gNext - g := by
  nlinarith

/-- The Wolfe curvature condition implies the BFGS curvature condition
`⟪y,s⟫ > 0` for `s = α • p` and `y = gNext - g`. -/
theorem wolfe_secant_curvature_positive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g gNext p : E) (α c₂ : ℝ)
    (hα : 0 < α) (hc₂ : c₂ < 1)
    (hdescent : inner ℝ g p < 0)
    (hcurvature : c₂ * inner ℝ g p ≤ inner ℝ gNext p) :
    0 < inner ℝ (gNext - g) (α • p) := by
  have hdir : 0 < inner ℝ gNext p - inner ℝ g p :=
    wolfe_directional_curvature_positive c₂ _ _ hc₂ hdescent hcurvature
  have heq : inner ℝ (gNext - g) (α • p) =
      α * (inner ℝ gNext p - inner ℝ g p) := by
    rw [real_inner_smul_right, inner_sub_left]
  rw [heq]
  exact mul_pos hα hdir

/-- The two Wolfe inequalities and directional Lipschitz bound give a
quantitative descent estimate. Here `g < 0` is the directional derivative,
`d > 0` is the squared direction norm, and `L` is a Lipschitz constant. -/
theorem wolfe_descent_bound
    (c₁ c₂ L α g gNext d f fNext : ℝ)
    (hc₁ : 0 < c₁) (_hc₂ : c₂ < 1) (hL : 0 < L)
    (hg : g < 0) (hd : 0 < d)
    (hw : WolfeStep c₁ c₂ α g gNext f fNext)
    (hLip : gNext - g ≤ L * α * d) :
    c₁ * (1 - c₂) * g ^ 2 ≤ L * d * (f - fNext) := by
  have hcurv : (1 - c₂) * (-g) ≤ L * α * d := by
    rcases hw with ⟨_, hcurvature⟩
    nlinarith
  have harmijo : c₁ * α * (-g) ≤ f - fNext := by
    rcases hw with ⟨hdecrease, _⟩
    nlinarith
  have h₁ : 0 ≤ L * α * d - (1 - c₂) * (-g) := sub_nonneg.mpr hcurv
  have h₂ : 0 ≤ c₁ * (-g) := mul_nonneg hc₁.le (by linarith)
  have h₃ : 0 ≤ f - fNext - c₁ * α * (-g) := sub_nonneg.mpr harmijo
  have h₄ : 0 ≤ L * d := mul_nonneg hL.le hd.le
  nlinarith [mul_nonneg h₁ h₂, mul_nonneg h₃ h₄]

/-- If a nonnegative per-step quantity is paid for by descent of an objective
bounded below, then the quantity is summable. This is the telescoping step in
Zoutendijk's theorem. -/
theorem summable_of_descent
    (energy weight : ℕ → ℝ) (lower rate : ℝ)
    (hrate : 0 < rate)
    (hweight : ∀ k, 0 ≤ weight k)
    (hlower : ∀ k, lower ≤ energy k)
    (hdescent : ∀ k, rate * weight k ≤ energy k - energy (k + 1)) :
    Summable weight := by
  apply summable_of_sum_range_le hweight (c := (energy 0 - lower) / rate)
  intro n
  have htel : (∑ k ∈ Finset.range n, (energy k - energy (k + 1))) =
      energy 0 - energy n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hsum : rate * (∑ k ∈ Finset.range n, weight k) ≤
      energy 0 - energy n := by
    calc
      rate * (∑ k ∈ Finset.range n, weight k) =
          ∑ k ∈ Finset.range n, rate * weight k := by rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range n, (energy k - energy (k + 1)) :=
        Finset.sum_le_sum (fun k _ => hdescent k)
      _ = energy 0 - energy n := htel
  apply (le_div_iff₀ hrate).2
  nlinarith [hlower n]

/-- Zoutendijk's summability conclusion for a sequence of weak Wolfe steps.
`g k` is the directional derivative before step `k`, `gNext k` is the
derivative at the new point along the *same* direction, and `d k = ‖pₖ‖²`.
The gradient Lipschitz condition implies `hLip` by
`directional_derivative_lipschitz`. -/
theorem zoutendijk_summable
    (energy g gNext d α : ℕ → ℝ) (lower c₁ c₂ L : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (hL : 0 < L)
    (hg : ∀ k, g k < 0) (hd : ∀ k, 0 < d k)
    (hlower : ∀ k, lower ≤ energy k)
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (α k) (g k) (gNext k)
      (energy k) (energy (k + 1)))
    (hLip : ∀ k, gNext k - g k ≤ L * α k * d k) :
    Summable (fun k => (g k) ^ 2 / d k) := by
  apply summable_of_descent energy (fun k => (g k) ^ 2 / d k)
    lower (c₁ * (1 - c₂) / L)
  · exact div_pos (mul_pos hc₁ (sub_pos.mpr hc₂)) hL
  · intro k
    exact div_nonneg (sq_nonneg _) (hd k).le
  · exact hlower
  · intro k
    have hbound := wolfe_descent_bound c₁ c₂ L (α k) (g k) (gNext k)
      (d k) (energy k) (energy (k + 1)) hc₁ hc₂ hL (hg k) (hd k)
      (hWolfe k) (hLip k)
    have heq : (c₁ * (1 - c₂) / L) * ((g k) ^ 2 / d k) =
        (c₁ * (1 - c₂) * (g k) ^ 2) / (L * d k) := by ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos hL (hd k))).2
    simpa only [mul_comm (energy k - energy (k + 1)) (L * d k)] using hbound

/-- Zoutendijk's theorem for iterates in a real inner product space. The
gradient map is supplied explicitly, so differentiability of `f` can be
formalized separately. The hypotheses state the weak Wolfe conditions,
Lipschitz continuity of the gradient, and a lower bound on the objective. -/
theorem zoutendijk_of_lipschitz_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (gradient : E → E) (x p : ℕ → E) (α : ℕ → ℝ)
    (lower c₁ c₂ L : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (hL : 0 < L)
    (hα : ∀ k, 0 ≤ α k)
    (hstep : ∀ k, x (k + 1) = x k + α k • p k)
    (hdescent : ∀ k, inner ℝ (gradient (x k)) (p k) < 0)
    (hlower : ∀ k, lower ≤ f (x k))
    (hgradientLip : ∀ u v, ‖gradient v - gradient u‖ ≤ L * ‖v - u‖)
    (hWolfe : ∀ k, WolfeStep c₁ c₂ (α k)
      (inner ℝ (gradient (x k)) (p k))
      (inner ℝ (gradient (x (k + 1))) (p k))
      (f (x k)) (f (x (k + 1)))) :
    Summable (fun k =>
      (inner ℝ (gradient (x k)) (p k)) ^ 2 / ‖p k‖ ^ 2) := by
  apply zoutendijk_summable
    (fun k => f (x k))
    (fun k => inner ℝ (gradient (x k)) (p k))
    (fun k => inner ℝ (gradient (x (k + 1))) (p k))
    (fun k => ‖p k‖ ^ 2) α lower c₁ c₂ L hc₁ hc₂ hL
  · exact hdescent
  · intro k
    have hp : p k ≠ 0 := by
      intro hzero
      have hneg := hdescent k
      simp [hzero] at hneg
    exact pow_pos (norm_pos_iff.mpr hp) _
  · exact hlower
  · exact hWolfe
  · intro k
    have hdist : ‖x (k + 1) - x k‖ = α k * ‖p k‖ := by
      rw [hstep k]
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα k)]
    have hgrad : ‖gradient (x (k + 1)) - gradient (x k)‖ ≤
        L * α k * ‖p k‖ := by
      calc
        _ ≤ L * ‖x (k + 1) - x k‖ := hgradientLip (x k) (x (k + 1))
        _ = L * α k * ‖p k‖ := by rw [hdist]; ring
    exact directional_derivative_lipschitz
      (gradient (x k)) (gradient (x (k + 1))) (p k) L (α k) hgrad

end QuasiNewtonConvergence

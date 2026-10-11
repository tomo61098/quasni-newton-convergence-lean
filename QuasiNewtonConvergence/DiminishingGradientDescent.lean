import QuasiNewtonConvergence.GradientDescent
import Mathlib.Analysis.Real.Sqrt

/-!
# Gradient descent with diminishing steps

Indices start at zero, so step `k` has length `1 / √(k+1)`.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gradientStepSize (gradient : E → E) (α : ℝ) (x : E) : E :=
  x - α • gradient x

def sqrtStepSize (k : ℕ) : ℝ := 1 / Real.sqrt (k + 1)

private theorem smoothUpper_of_small_step (f : E → ℝ) (gradient : E → E)
    (L α : ℝ) (hL : 0 < L) (hα : 0 < α) (hsmall : α ≤ 1 / L)
    (hsmooth : SmoothUpper f gradient L) :
    SmoothUpper f gradient (1 / α) := by
  have hαinv : 0 < 1 / α := one_div_pos.mpr hα
  have hL' : L ≤ 1 / α := by
    apply (le_div_iff₀ hα).2
    have hp := (le_div_iff₀ hL).mp hsmall
    nlinarith
  intro x y
  have h := hsmooth x y
  have hnorm := mul_nonneg (sub_nonneg.mpr hL') (sq_nonneg ‖y - x‖)
  nlinarith

/-- For `α ≤ 1/L`, one step pays for its objective gap by a decrease in
squared distance to any comparison point. -/
theorem gradientStepSize_convex_potential (f : E → ℝ) (gradient : E → E)
    (L α : ℝ) (hL : 0 < L) (hα : 0 < α) (hsmall : α ≤ 1 / L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient) (x minimizer : E) :
    2 * α * (f (gradientStepSize gradient α x) - f minimizer) ≤
      ‖x - minimizer‖ ^ 2 - ‖gradientStepSize gradient α x - minimizer‖ ^ 2 := by
  have hs := smoothUpper_of_small_step f gradient L α hL hα hsmall hsmooth
  have h := gradientStep_convex_potential f gradient (1 / α)
    (one_div_pos.mpr hα) hs
    hconvex x minimizer
  have heq : gradientStep gradient (1 / α) x = gradientStepSize gradient α x := by
    simp [gradientStep, gradientStepSize]
  rw [heq] at h
  have hαne : α ≠ 0 := ne_of_gt hα
  have hmul := mul_le_mul_of_nonneg_left h
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hα.le)
  calc
    _ ≤ 2 * α * (1 / α / 2 *
        (‖x - minimizer‖ ^ 2 - ‖gradientStepSize gradient α x - minimizer‖ ^ 2)) := hmul
    _ = _ := by field_simp

private theorem gradientStepSize_descent (f : E → ℝ) (gradient : E → E)
    (L α : ℝ) (hL : 0 < L) (hα : 0 < α) (hsmall : α ≤ 1 / L)
    (hsmooth : SmoothUpper f gradient L) (x : E) :
    f (gradientStepSize gradient α x) ≤ f x := by
  have hs := smoothUpper_of_small_step f gradient L α hL hα hsmall hsmooth
  have h := gradientStep_descent f gradient (1 / α) (one_div_pos.mpr hα) hs x
  have heq : gradientStep gradient (1 / α) x = gradientStepSize gradient α x := by
    simp [gradientStep, gradientStepSize]
  rw [heq] at h
  have hn : 0 ≤ ‖gradient x‖ ^ 2 / (2 * (1 / α)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- Weighted potential bound for any positive steps at most `1/L`.
This gives `f(xₙ)-f(x★) ≤ ‖x₀-x★‖²/(2∑_{j<n} αⱼ)`. -/
theorem gradientDescent_variable_rate (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L : ℝ) (α : ℕ → ℝ)
    (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hαpos : ∀ k, 0 < α k) (hαsmall : ∀ k, α k ≤ 1 / L)
    (hstep : ∀ k, x (k + 1) = gradientStepSize gradient (α k) (x k))
    (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, α k) * (f (x n) - f minimizer) ≤
      ‖x 0 - minimizer‖ ^ 2 := by
  have hmono (k : ℕ) : f (x (k + 1)) ≤ f (x k) := by
    rw [hstep k]
    exact gradientStepSize_descent f gradient L (α k) hL (hαpos k)
      (hαsmall k) hsmooth (x k)
  have hsum (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range n, α k :=
    Finset.sum_nonneg (fun k _ => (hαpos k).le)
  have hpot (n : ℕ) :
      2 * (∑ k ∈ Finset.range n, α k) * (f (x n) - f minimizer) +
        ‖x n - minimizer‖ ^ 2 ≤ ‖x 0 - minimizer‖ ^ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hp := gradientStepSize_convex_potential f gradient L (α n)
        hL (hαpos n) (hαsmall n) hsmooth hconvex (x n) minimizer
      rw [← hstep n] at hp
      have hm := mul_le_mul_of_nonneg_left
        (sub_le_sub_right (hmono n) (f minimizer))
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hsum n))
      rw [Finset.sum_range_succ]
      nlinarith
  have h := hpot n
  nlinarith [sq_nonneg ‖x n - minimizer‖]

/-- Positive diminishing steps whose partial sums diverge still converge in
objective value, provided all steps are at most `1/L`. -/
theorem gradientDescent_variable_tendsto (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L : ℝ) (α : ℕ → ℝ)
    (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hαpos : ∀ k, 0 < α k) (hαsmall : ∀ k, α k ≤ 1 / L)
    (hstep : ∀ k, x (k + 1) = gradientStepSize gradient (α k) (x k))
    (hdiv : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, α k)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f minimizer)) := by
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, α k
  have hpos : ∀ᶠ n in Filter.atTop, 0 < S n :=
    hdiv.eventually (Filter.eventually_gt_atTop 0)
  have hupper : Filter.Tendsto (fun n =>
      ‖x 0 - minimizer‖ ^ 2 / (2 * S n)) Filter.atTop (nhds 0) := by
    have hi := tendsto_inv_atTop_zero.comp hdiv
    convert (tendsto_const_nhds (x := ‖x 0 - minimizer‖ ^ 2 / 2)).mul hi using 1
    · ext n
      simp only [S, Function.comp_def, div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  have hgap : Filter.Tendsto (fun n => f (x n) - f minimizer)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall (fun n => sub_nonneg.mpr (hmin (x n)))
    · filter_upwards [hpos] with n hn
      have hr := gradientDescent_variable_rate f gradient x minimizer L α
        hL hsmooth hconvex hαpos hαsmall hstep n
      apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hn)).2
      dsimp [S] at hn ⊢
      nlinarith
  simpa only [sub_add_cancel, zero_add] using hgap.add_const (f minimizer)

theorem sqrtStepSize_pos (k : ℕ) : 0 < sqrtStepSize k := by
  unfold sqrtStepSize
  positivity

private theorem sqrtStepSize_ge_sqrt_difference (k : ℕ) :
    Real.sqrt (k + 1) - Real.sqrt k ≤ sqrtStepSize k := by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have ha := Real.sqrt_nonneg (k:ℝ)
    have hb := Real.sqrt_pos.2 hk1
    have hc := Real.sqrt_le_sqrt (show (k:ℝ) ≤ (k:ℝ) + 1 by linarith)
    have hd := mul_le_mul_of_nonneg_left hc ha
    have he := Real.sq_sqrt hk
    have hf := Real.sq_sqrt hk1.le
    unfold sqrtStepSize
    apply (le_div_iff₀ hb).2
    nlinarith

/-- The sum of `1/√(K+k+1)` diverges for every finite starting index `K`. -/
theorem sqrtStepSize_tail_sum_diverges (K : ℕ) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, sqrtStepSize (K + k))
      Filter.atTop Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt n)
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbound (n : ℕ) : Real.sqrt n ≤
      Real.sqrt K + ∑ k ∈ Finset.range n, sqrtStepSize (K + k) := by
    have htel : (∑ k ∈ Finset.range n,
        (Real.sqrt (K + k + 1) - Real.sqrt (K + k))) =
        Real.sqrt (K + n) - Real.sqrt K := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring_nf
    have hs : (∑ k ∈ Finset.range n,
        (Real.sqrt (K + k + 1) - Real.sqrt (K + k))) ≤
        ∑ k ∈ Finset.range n, sqrtStepSize (K + k) := by
      exact Finset.sum_le_sum (fun k _ => by
        simpa only [Nat.cast_add, Nat.add_assoc] using
          sqrtStepSize_ge_sqrt_difference (K + k))
    have hm : Real.sqrt n ≤ Real.sqrt (K + n) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_add_left n K)
    linarith [htel]
  have hsum : Filter.Tendsto
      (fun n => Real.sqrt K + ∑ k ∈ Finset.range n, sqrtStepSize (K + k))
      Filter.atTop Filter.atTop := Filter.tendsto_atTop_mono hbound hsqrt
  simpa [add_assoc] using
    (Filter.tendsto_atTop_add_const_right Filter.atTop (-Real.sqrt K) hsum)

/-- The sum of the unshifted step lengths diverges as a special case. -/
theorem sqrtStepSize_sum_diverges :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, sqrtStepSize k)
      Filter.atTop Filter.atTop := by
  simpa using sqrtStepSize_tail_sum_diverges 0

private theorem sqrtStepSize_tendsto_zero :
    Filter.Tendsto sqrtStepSize Filter.atTop (nhds 0) := by
  have hcast : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    norm_num
  have hsqrt := Real.tendsto_sqrt_atTop.comp hcast
  have hinv := tendsto_inv_atTop_zero.comp hsqrt
  change Filter.Tendsto (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1))
    Filter.atTop (nhds 0)
  simpa only [one_div, Function.comp_def] using hinv

/-- For every `L > 0`, the `1/√(k+1)` steps eventually satisfy `αₖ ≤ 1/L`.
Hence finite early steps do not affect convergence. -/
theorem gradientDescent_sqrt_tendsto (f : E → ℝ) (gradient : E → E)
    (x : ℕ → E) (minimizer : E) (L : ℝ)
    (hL : 0 < L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize gradient (sqrtStepSize k) (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  have hevent : ∀ᶠ k in Filter.atTop, sqrtStepSize k ≤ 1 / L := by
    have hh := sqrtStepSize_tendsto_zero.eventually
      (eventually_lt_nhds (one_div_pos.mpr hL))
    exact hh.mono (fun _ hk => hk.le)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hevent
  have htail : Filter.Tendsto (fun n => f (x (K + n)))
      Filter.atTop (nhds (f minimizer)) := by
    apply gradientDescent_variable_tendsto f gradient
      (fun n => x (K + n)) minimizer L (fun n => sqrtStepSize (K + n))
      hL hsmooth hconvex hmin
    · intro n; exact sqrtStepSize_pos _
    · intro n; exact hK _ (Nat.le_add_right K n)
    · intro n
      simpa only [Nat.add_assoc] using hstep (K + n)
    · exact sqrtStepSize_tail_sum_diverges K
  exact (Filter.tendsto_add_atTop_iff_nat K).1 (by simpa [Nat.add_comm] using htail)

/-- Strong convexity implies the first-order convex inequality. -/
theorem StrongConvexFirstOrder.toConvexFirstOrder (f : E → ℝ)
    (gradient : E → E) (μ : ℝ) (hμ : 0 < μ)
    (hstrong : StrongConvexFirstOrder f gradient μ) :
    ConvexFirstOrder f gradient := by
  intro x y
  have h := hstrong x y
  have hn := mul_nonneg (div_nonneg hμ.le (by norm_num : (0:ℝ) ≤ 2))
    (sq_nonneg ‖y - x‖)
  linarith

/-- Objective values converge under strong convexity for the square-root
schedule, with no restriction on `L/μ`. -/
theorem gradientDescent_sqrt_strong_tendsto
    (f : E → ℝ) (gradient : E → E) (x : ℕ → E)
    (minimizer : E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize gradient (sqrtStepSize k) (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) :=
  gradientDescent_sqrt_tendsto f gradient x minimizer L hL hsmooth
    (StrongConvexFirstOrder.toConvexFirstOrder f gradient μ hμ hstrong)
    hmin hstep

/-- With `μ`-strong convexity and a stationary minimizer, the same
`1/√(k+1)` schedule makes the iterates converge to the unique minimizer. -/
theorem gradientDescent_sqrt_strong_iterates_tendsto
    (f : E → ℝ) (gradient : E → E) (x : ℕ → E)
    (minimizer : E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (hstationary : gradient minimizer = 0)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize gradient (sqrtStepSize k) (x k)) :
    Filter.Tendsto x Filter.atTop (nhds minimizer) := by
  have hmin (y : E) : f minimizer ≤ f y := by
    have h := hstrong minimizer y
    simp only [hstationary, inner_zero_left] at h
    nlinarith [mul_nonneg (div_nonneg hμ.le (by norm_num : (0:ℝ) ≤ 2))
      (sq_nonneg ‖y - minimizer‖)]
  have hval := gradientDescent_sqrt_strong_tendsto f gradient x minimizer L μ
    hL hμ hsmooth hstrong hmin hstep
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

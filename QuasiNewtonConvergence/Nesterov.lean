module

public import QuasiNewtonConvergence.StrongConvexMinimizer

@[expose] public section

/-!
# Accelerated gradient descent

This is the standard smooth convex Nesterov method, written in its equivalent
three-sequence (linear coupling) form. The weights give an explicit `O(1/k²)`
objective-value bound.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem nesterov_step_potential (f : E → ℝ) (gradient : E → E)
    (L A a : ℝ) (hL : 0 < L) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hweight : L * a ^ 2 ≤ A + a)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x y z minimizer : E)
    (hcouple : (A + a) • (y - x) = a • (z - x)) :
    (A + a) * (f (gradientStep gradient L y) - f minimizer) +
        ‖z - a • gradient y - minimizer‖ ^ 2 / 2 ≤
      A * (f x - f minimizer) + ‖z - minimizer‖ ^ 2 / 2 := by
  let g := gradient y
  have hx : f y - f x ≤ inner ℝ g (y - x) := by
    have h := hconvex y x
    have heq : x - y = -(y - x) := by abel
    rw [heq, inner_neg_right] at h
    dsimp [g]
    linarith
  have hm : f y - f minimizer ≤ inner ℝ g (y - minimizer) := by
    have h := hconvex y minimizer
    have heq : minimizer - y = -(y - minimizer) := by abel
    rw [heq, inner_neg_right] at h
    dsimp [g]
    linarith
  have hv : A • (y - x) + a • (y - minimizer) =
      a • (z - minimizer) := by
    calc
      A • (y - x) + a • (y - minimizer) =
          (A + a) • (y - x) + a • (x - minimizer) := by
            simp only [add_smul, smul_sub]
            abel
      _ = a • (z - x) + a • (x - minimizer) := by rw [hcouple]
      _ = a • (z - minimizer) := by rw [← smul_add]; congr 1; abel
  have hinner : A * inner ℝ g (y - x) +
      a * inner ℝ g (y - minimizer) =
        a * inner ℝ g (z - minimizer) := by
    have h := congrArg (inner ℝ g) hv
    simpa only [inner_add_right, real_inner_smul_right] using h
  have hobj : (A + a) * (f y - f minimizer) -
      A * (f x - f minimizer) ≤ a * inner ℝ g (z - minimizer) := by
    have hx' := mul_le_mul_of_nonneg_left hx hA
    have hm' := mul_le_mul_of_nonneg_left hm ha
    nlinarith
  have hdesc := gradientStep_descent f gradient L hL hsmooth y
  have hdesc' : (A + a) * (f (gradientStep gradient L y) - f y) ≤
      -((A + a) / (2 * L)) * ‖g‖ ^ 2 := by
    have hAn : 0 ≤ A + a := add_nonneg hA ha
    have ht : f (gradientStep gradient L y) - f y ≤
        -(‖g‖ ^ 2 / (2 * L)) := by dsimp [g]; linarith
    calc
      _ ≤ (A + a) * (-(‖g‖ ^ 2 / (2 * L))) :=
        mul_le_mul_of_nonneg_left ht hAn
      _ = _ := by ring
  have hdist : ‖z - a • g - minimizer‖ ^ 2 =
      ‖z - minimizer‖ ^ 2 - 2 * a * inner ℝ g (z - minimizer) +
        a ^ 2 * ‖g‖ ^ 2 := by
    have heq : z - a • g - minimizer = (z - minimizer) + -(a • g) := by abel
    rw [heq, norm_add_sq_real, inner_neg_right, real_inner_smul_right,
      real_inner_comm (z - minimizer) g,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow]
    rw [sq_abs]
    ring
  have hcoef : a ^ 2 / 2 ≤ (A + a) / (2 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * L)).2
    nlinarith [hweight]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖g‖)
  rw [hdist]
  nlinarith

/-- The cumulative weight at iteration `k`. -/
def nesterovWeight (L : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * (k + 1) / (4 * L)

/-- The weight added by iteration `k`. -/
def nesterovIncrement (L : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) / (2 * L)

/-- The point at which the next gradient is evaluated. -/
def nesterovExtrapolate (k : ℕ) (x z : E) : E :=
  x + (2 / ((k : ℝ) + 2)) • (z - x)

private theorem nesterov_weight_succ (L : ℝ) (hL : 0 < L) (k : ℕ) :
    nesterovWeight L (k + 1) =
      nesterovWeight L k + nesterovIncrement L k := by
  have hLne : L ≠ 0 := ne_of_gt hL
  simp only [nesterovWeight, nesterovIncrement, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private theorem nesterov_weight_nonneg (L : ℝ) (hL : 0 < L) (k : ℕ) :
    0 ≤ nesterovWeight L k := by
  unfold nesterovWeight
  positivity

private theorem nesterov_increment_nonneg (L : ℝ) (hL : 0 < L) (k : ℕ) :
    0 ≤ nesterovIncrement L k := by
  unfold nesterovIncrement
  positivity

private theorem nesterov_weight_condition (L : ℝ) (hL : 0 < L) (k : ℕ) :
    L * nesterovIncrement L k ^ 2 ≤
      nesterovWeight L k + nesterovIncrement L k := by
  rw [← nesterov_weight_succ L hL k]
  have hLne : L ≠ 0 := ne_of_gt hL
  unfold nesterovIncrement nesterovWeight
  simp only [Nat.cast_add, Nat.cast_one]
  have heq : L * (((k : ℝ) + 1) / (2 * L)) ^ 2 =
      ((k : ℝ) + 1) ^ 2 / (4 * L) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * L)
    (by positivity : 0 < 4 * L)).2
  have hk : 0 ≤ (k : ℝ) + 1 := by positivity
  nlinarith

private theorem nesterov_extrapolate_couple (L : ℝ) (hL : 0 < L)
    (k : ℕ) (x z : E) :
    (nesterovWeight L k + nesterovIncrement L k) •
        (nesterovExtrapolate k x z - x) =
      nesterovIncrement L k • (z - x) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hk : (k : ℝ) + 2 ≠ 0 := by positivity
  have hcoeff : (nesterovWeight L k + nesterovIncrement L k) *
      (2 / ((k : ℝ) + 2)) = nesterovIncrement L k := by
    unfold nesterovWeight nesterovIncrement
    field_simp
    ring
  simp only [nesterovExtrapolate, add_sub_cancel_left, smul_smul, hcoeff]

/-- Nesterov's accelerated gradient bound in its three-sequence form.
The extrapolated point is `nesterovExtrapolate k (x k) (z k)`; `x` takes a
gradient step there, while `z` takes a weighted gradient step. -/
theorem nesterov_convex_weighted_rate
    (f : E → ℝ) (gradient : E → E) (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x z : ℕ → E) (minimizer : E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x k) (z k)))
    (hz : ∀ k, z (k + 1) = z k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x k) (z k)))
    (n : ℕ) :
    nesterovWeight L n * (f (x n) - f minimizer) ≤
      ‖x 0 - minimizer‖ ^ 2 / 2 := by
  have hpot (n : ℕ) :
      nesterovWeight L n * (f (x n) - f minimizer) +
        ‖z n - minimizer‖ ^ 2 / 2 ≤
          ‖x 0 - minimizer‖ ^ 2 / 2 := by
    induction n with
    | zero => simp [nesterovWeight, hinit]
    | succ k ih =>
      let y := nesterovExtrapolate k (x k) (z k)
      have hs := nesterov_step_potential f gradient L
        (nesterovWeight L k) (nesterovIncrement L k)
        hL (nesterov_weight_nonneg L hL k)
        (nesterov_increment_nonneg L hL k)
        (nesterov_weight_condition L hL k)
        hsmooth hconvex (x k) y (z k) minimizer
        (nesterov_extrapolate_couple L hL k (x k) (z k))
      rw [← nesterov_weight_succ L hL k, ← hx k, ← hz k] at hs
      nlinarith
  have h := hpot n
  nlinarith [sq_nonneg ‖z n - minimizer‖]

/-- Explicit `O(1/n²)` objective gap after `n ≥ 1` accelerated steps. -/
theorem nesterov_convex_rate
    (f : E → ℝ) (gradient : E → E) (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x z : ℕ → E) (minimizer : E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x k) (z k)))
    (hz : ∀ k, z (k + 1) = z k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x k) (z k)))
    (n : ℕ) (hn : 0 < n) :
    f (x n) - f minimizer ≤
      2 * L * ‖x 0 - minimizer‖ ^ 2 / ((n : ℝ) * (n + 1)) := by
  have h := nesterov_convex_weighted_rate f gradient L hL hsmooth
    hconvex x z minimizer hinit hx hz n
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hAn : 0 < nesterovWeight L n := by
    unfold nesterovWeight
    positivity
  have hb : f (x n) - f minimizer ≤
      (‖x 0 - minimizer‖ ^ 2 / 2) / nesterovWeight L n :=
    (le_div_iff₀ hAn).2 (by simpa only [mul_comm] using h)
  calc
    _ ≤ (‖x 0 - minimizer‖ ^ 2 / 2) / nesterovWeight L n := hb
    _ = _ := by
      unfold nesterovWeight
      have hLne : L ≠ 0 := ne_of_gt hL
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- In particular, accelerated gradient objective values converge to the
minimum for a smooth convex objective. -/
theorem nesterov_convex_tendsto
    (f : E → ℝ) (gradient : E → E) (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x z : ℕ → E) (minimizer : E)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x k) (z k)))
    (hz : ∀ k, z (k + 1) = z k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x k) (z k))) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  have hbound : ∀ᶠ n in Filter.atTop,
      f (x n) - f minimizer ≤
        2 * L * ‖x 0 - minimizer‖ ^ 2 / (n : ℝ) := by
    apply Filter.eventually_atTop.2
    refine ⟨1, ?_⟩
    intro n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hden : (n : ℝ) ≤ (n : ℝ) * (n + 1) := by nlinarith
    have hnum : 0 ≤ 2 * L * ‖x 0 - minimizer‖ ^ 2 := by positivity
    exact (nesterov_convex_rate f gradient L hL hsmooth hconvex
      x z minimizer hinit hx hz n hn).trans
      (div_le_div_of_nonneg_left hnum hnR hden)
  have hupper : Filter.Tendsto
      (fun n : ℕ => 2 * L * ‖x 0 - minimizer‖ ^ 2 / (n : ℝ))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) _
  have hgap : Filter.Tendsto (fun n => f (x n) - f minimizer)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall
        (fun n => sub_nonneg.mpr (hmin (x n)))
    · exact hbound
  have hval := hgap.add_const (f minimizer)
  simpa only [sub_add_cancel, zero_add] using hval

private theorem strongConvex_distance_gap
    (f : E → ℝ) (gradient : E → E) (μ : ℝ)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (minimizer : E) (hstationary : gradient minimizer = 0) (y : E) :
    μ / 2 * ‖y - minimizer‖ ^ 2 ≤ f y - f minimizer := by
  have h := hstrong minimizer y
  simp only [hstationary, inner_zero_left] at h
  linarith

/-- A finite restart length satisfying the contraction condition always exists. -/
theorem exists_nesterov_restart_length (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) :
    ∃ m : ℕ, 2 ≤ μ * nesterovWeight L m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (8 * L / μ)
  refine ⟨m, ?_⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have hmR : 8 * L / μ < (m : ℝ) := hm
  have hmprod : 8 * L < μ * (m : ℝ) := by
    have h := (div_lt_iff₀ hμ).1 hmR
    nlinarith
  have hmnon : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hwide : 8 * L ≤ μ * (m : ℝ) * ((m : ℝ) + 1) := by
    nlinarith [mul_nonneg (mul_nonneg hμ.le hmnon) hmnon]
  unfold nesterovWeight
  calc
    2 ≤ (μ * (m : ℝ) * ((m : ℝ) + 1)) / (4 * L) :=
      (le_div_iff₀ (by positivity : 0 < 4 * L)).2 (by nlinarith [hwide])
    _ = μ * ((m : ℝ) * ((m : ℝ) + 1) / (4 * L)) := by ring

/-- For the original accelerated sequence, strong convexity upgrades the
`O(1/n²)` objective bound to convergence of every iterate. -/
theorem nesterov_strong_iterates_tendsto
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (minimizer : E) (hstationary : gradient minimizer = 0)
    (x z : ℕ → E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x k) (z k)))
    (hz : ∀ k, z (k + 1) = z k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x k) (z k))) :
    Filter.Tendsto x Filter.atTop (nhds minimizer) := by
  have hmin (y : E) : f minimizer ≤ f y := by
    have hq := strongConvex_distance_gap f gradient μ hstrong
      minimizer hstationary y
    nlinarith [mul_nonneg (div_nonneg hμ.le
      (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg ‖y - minimizer‖)]
  have hval := nesterov_convex_tendsto f gradient L hL hsmooth
    (StrongConvexFirstOrder.toConvexFirstOrder f gradient μ hμ hstrong)
    x z minimizer hmin hinit hx hz
  have hgap : Filter.Tendsto (fun k => f (x k) - f minimizer)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hval.sub_const (f minimizer)
  have hsq : Filter.Tendsto (fun k => ‖x k - minimizer‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hupper : Filter.Tendsto
        (fun k => (2 / μ) * (f (x k) - f minimizer))
        Filter.atTop (nhds 0) := by simpa using hgap.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact sq_nonneg _
    · intro k
      have hq := strongConvex_distance_gap f gradient μ hstrong
        minimizer hstationary (x k)
      calc
        _ ≤ (2 * (f (x k) - f minimizer)) / μ :=
          (le_div_iff₀ hμ).2 (by nlinarith [hq])
        _ = _ := by ring
  have hnorm : Filter.Tendsto (fun k => ‖x k - minimizer‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- One restarted block of `m` Nesterov steps halves the objective gap when
`μ * nesterovWeight L m ≥ 2`, equivalently `μ m(m+1) ≥ 8L`. -/
theorem nesterov_strong_restart_half
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (minimizer : E) (hstationary : gradient minimizer = 0)
    (x z : ℕ → E) (m : ℕ)
    (hm : 2 ≤ μ * nesterovWeight L m)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x k) (z k)))
    (hz : ∀ k, z (k + 1) = z k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x k) (z k))) :
    2 * (f (x m) - f minimizer) ≤ f (x 0) - f minimizer := by
  have hconvex := StrongConvexFirstOrder.toConvexFirstOrder f gradient μ hμ hstrong
  have hb := nesterov_convex_weighted_rate f gradient L hL hsmooth
    hconvex x z minimizer hinit hx hz m
  have hquad := strongConvex_distance_gap f gradient μ hstrong
    minimizer hstationary (x 0)
  have hgap : 0 ≤ f (x m) - f minimizer := by
    have h := strongConvex_distance_gap f gradient μ hstrong
      minimizer hstationary (x m)
    nlinarith [sq_nonneg ‖x m - minimizer‖]
  have hmul := mul_le_mul_of_nonneg_left hb hμ.le
  have hcoef := mul_le_mul_of_nonneg_right hm hgap
  nlinarith

/-- Restart the accelerated method every `m` inner iterations. The objective
gap at the start of block `r` contracts by `2⁻ʳ`. -/
theorem nesterov_strong_restarted_rate
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (minimizer : E) (hstationary : gradient minimizer = 0)
    (x z : ℕ → ℕ → E) (m : ℕ)
    (hm : 2 ≤ μ * nesterovWeight L m)
    (hinit : ∀ r, z r 0 = x r 0)
    (hx : ∀ r k, x r (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x r k) (z r k)))
    (hz : ∀ r k, z r (k + 1) = z r k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x r k) (z r k)))
    (hjoin : ∀ r, x (r + 1) 0 = x r m)
    (r : ℕ) :
    f (x r 0) - f minimizer ≤
      (1 / 2 : ℝ) ^ r * (f (x 0 0) - f minimizer) := by
  have hhalf (r : ℕ) :
      2 * (f (x (r + 1) 0) - f minimizer) ≤
        f (x r 0) - f minimizer := by
    rw [hjoin r]
    exact nesterov_strong_restart_half f gradient L μ hL hμ hsmooth
      hstrong minimizer hstationary (x r) (z r) m hm
      (hinit r) (hx r) (hz r)
  induction r with
  | zero => simp
  | succ r ih =>
    have hh := hhalf r
    have hpow := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [pow_succ]
    nlinarith

/-- The restart points converge to the unique minimizer, and their objective
values converge geometrically. -/
theorem nesterov_strong_restarted_converges
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (minimizer : E) (hstationary : gradient minimizer = 0)
    (x z : ℕ → ℕ → E) (m : ℕ)
    (hm : 2 ≤ μ * nesterovWeight L m)
    (hinit : ∀ r, z r 0 = x r 0)
    (hx : ∀ r k, x r (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x r k) (z r k)))
    (hz : ∀ r k, z r (k + 1) = z r k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x r k) (z r k)))
    (hjoin : ∀ r, x (r + 1) 0 = x r m) :
    Filter.Tendsto (fun r => x r 0) Filter.atTop (nhds minimizer) ∧
      Filter.Tendsto (fun r => f (x r 0)) Filter.atTop (nhds (f minimizer)) := by
  have hgap_nonneg (r : ℕ) : 0 ≤ f (x r 0) - f minimizer := by
    have hq := strongConvex_distance_gap f gradient μ hstrong
      minimizer hstationary (x r 0)
    nlinarith [sq_nonneg ‖x r 0 - minimizer‖]
  have hrate (r : ℕ) := nesterov_strong_restarted_rate f gradient L μ
    hL hμ hsmooth hstrong minimizer hstationary x z m hm
    hinit hx hz hjoin r
  have hupper : Filter.Tendsto
      (fun r : ℕ => (1 / 2 : ℝ) ^ r *
        (f (x 0 0) - f minimizer)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
        (f (x 0 0) - f minimizer)
  have hgap : Filter.Tendsto (fun r => f (x r 0) - f minimizer)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · exact hgap_nonneg
    · exact hrate
  have hval : Filter.Tendsto (fun r => f (x r 0))
      Filter.atTop (nhds (f minimizer)) := by
    simpa only [sub_add_cancel, zero_add] using hgap.add_const (f minimizer)
  have hsq : Filter.Tendsto (fun r => ‖x r 0 - minimizer‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hupper' : Filter.Tendsto
        (fun r => (2 / μ) * (f (x r 0) - f minimizer))
        Filter.atTop (nhds 0) := by simpa using hgap.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper'
    · intro r; exact sq_nonneg _
    · intro r
      have hq := strongConvex_distance_gap f gradient μ hstrong
        minimizer hstationary (x r 0)
      calc
        _ ≤ (2 * (f (x r 0) - f minimizer)) / μ :=
          (le_div_iff₀ hμ).2 (by nlinarith [hq])
        _ = _ := by ring
  have hnorm : Filter.Tendsto (fun r => ‖x r 0 - minimizer‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact ⟨tendsto_iff_norm_sub_tendsto_zero.mpr hnorm, hval⟩

/-- On a complete space, smooth strong convexity supplies the minimizer for
the original accelerated sequence. -/
theorem nesterov_strong_converges
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z : ℕ → E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x k) (z k)))
    (hz : ∀ k, z (k + 1) = z k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x k) (z k))) :
    ∃ minimizer : E,
      Filter.Tendsto x Filter.atTop (nhds minimizer) ∧
      Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  obtain ⟨minimizer, hstationary, hmin⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  refine ⟨minimizer, ?_, ?_⟩
  · exact nesterov_strong_iterates_tendsto f gradient L μ hL hμ
      hsmooth hstrong minimizer hstationary x z hinit hx hz
  · exact nesterov_convex_tendsto f gradient L hL hsmooth
      (StrongConvexFirstOrder.toConvexFirstOrder f gradient μ hμ hstrong)
      x z minimizer hmin hinit hx hz

/-- On a complete space, the restarted scheme also needs no supplied
minimizer or stationary-point assumption. -/
theorem nesterov_strong_restarted_exists_minimizer
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z : ℕ → ℕ → E) (m : ℕ)
    (hm : 2 ≤ μ * nesterovWeight L m)
    (hinit : ∀ r, z r 0 = x r 0)
    (hx : ∀ r k, x r (k + 1) =
      gradientStep gradient L (nesterovExtrapolate k (x r k) (z r k)))
    (hz : ∀ r k, z r (k + 1) = z r k -
      nesterovIncrement L k •
        gradient (nesterovExtrapolate k (x r k) (z r k)))
    (hjoin : ∀ r, x (r + 1) 0 = x r m) :
    ∃ minimizer : E,
      Filter.Tendsto (fun r => x r 0) Filter.atTop (nhds minimizer) ∧
      Filter.Tendsto (fun r => f (x r 0)) Filter.atTop (nhds (f minimizer)) := by
  obtain ⟨minimizer, hstationary, _⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  exact ⟨minimizer, nesterov_strong_restarted_converges f gradient
    L μ hL hμ hsmooth hstrong minimizer hstationary x z m hm
    hinit hx hz hjoin⟩

end QuasiNewtonConvergence

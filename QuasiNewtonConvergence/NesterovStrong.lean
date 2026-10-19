module

public import QuasiNewtonConvergence.Nesterov

@[expose] public section

/-!
# Constant-momentum Nesterov acceleration under strong convexity

The three-sequence formulation here is Algorithm 15 of the acceleration
monograph: `t = √(μ/L)`, `y = x + t/(1+t) • (z-x)`, one gradient step at `y`,
and a weighted update of `z`. Its potential contracts by `1-t` each step.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_sq_convex_combo (u v : E) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • u + t • v‖ ^ 2 ≤
      (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 := by
  have hinner : 2 * inner ℝ u v ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have h := norm_sub_sq_real u v
    nlinarith [sq_nonneg ‖u - v‖]
  have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hh := mul_le_mul_of_nonneg_left hinner ht
  have hexpand : ‖(1 - t) • u + t • v‖ ^ 2 =
      (1 - t) ^ 2 * ‖u‖ ^ 2 +
        2 * t * (1 - t) * inner ℝ u v + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow]
    rw [sq_abs, sq_abs]
    ring
  rw [hexpand]
  nlinarith

def strongNesterovExtrapolate (t : ℝ) (x z : E) : E :=
  x + (t / (1 + t)) • (z - x)

def strongNesterovAuxiliary (t μ : ℝ) (z y g : E) : E :=
  (1 - t) • z + t • y - (t / μ) • g

private theorem strongNesterov_extrapolate_relation (t : ℝ)
    (ht : 0 ≤ t) (x z : E) :
    strongNesterovExtrapolate t x z - x =
      t • (z - strongNesterovExtrapolate t x z) := by
  have htne : 1 + t ≠ 0 := by positivity
  have hcoeff : (1 + t) * (t / (1 + t)) = t := by field_simp
  have hscaled : (1 + t) • (strongNesterovExtrapolate t x z - x) =
      t • (z - x) := by
    simp [strongNesterovExtrapolate, smul_smul, hcoeff]
  have hscaled' : (strongNesterovExtrapolate t x z - x) +
      t • (strongNesterovExtrapolate t x z - x) = t • (z - x) := by
    simpa only [add_smul, one_smul] using hscaled
  calc
    strongNesterovExtrapolate t x z - x =
        (strongNesterovExtrapolate t x z - x) +
          t • (strongNesterovExtrapolate t x z - x) -
            t • (strongNesterovExtrapolate t x z - x) := by abel
    _ = t • (z - x) - t • (strongNesterovExtrapolate t x z - x) := by
      rw [hscaled']
    _ = t • (z - strongNesterovExtrapolate t x z) := by
      rw [← smul_sub]
      congr 1
      abel

/-- The strongly convex accelerated potential contracts in one iteration. -/
theorem strongNesterov_step_potential
    (f : E → ℝ) (gradient : E → E) (L μ t : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htsq : t ^ 2 = μ / L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z minimizer : E) :
    let y := strongNesterovExtrapolate t x z
    let xnext := gradientStep gradient L y
    let znext := strongNesterovAuxiliary t μ z y (gradient y)
    f xnext - f minimizer + μ / 2 * ‖znext - minimizer‖ ^ 2 ≤
      (1 - t) * (f x - f minimizer + μ / 2 * ‖z - minimizer‖ ^ 2) := by
  dsimp
  let y := strongNesterovExtrapolate t x z
  let g := gradient y
  let w := (1 - t) • z + t • y
  have hsum : (1 - t) • y + t • y = y := by
    rw [← add_smul]
    simp
  have hw : w - minimizer = (1 - t) • (z - y) + (y - minimizer) := by
    dsimp [w]
    rw [smul_sub]
    have hty : t • y = y - (1 - t) • y := by
      calc
        t • y = ((1 - t) • y + t • y) - (1 - t) • y := by abel
        _ = y - (1 - t) • y := by rw [hsum]
    -- The two expressions differ by `(1-t) • y + t • y = y`.
    rw [hty]
    abel
  have hcouple : (1 - t) • (y - x) + t • (y - minimizer) =
      t • (w - minimizer) := by
    have hr := strongNesterov_extrapolate_relation t ht0 x z
    change y - x = t • (z - y) at hr
    rw [hr, hw]
    simp only [smul_add, smul_smul]
    have heq : (1 - t) * t = t * (1 - t) := mul_comm _ _
    rw [heq]
  have hinner : (1 - t) * inner ℝ g (y - x) +
      t * inner ℝ g (y - minimizer) =
        t * inner ℝ g (w - minimizer) := by
    have h := congrArg (inner ℝ g) hcouple
    simpa only [inner_add_right, real_inner_smul_right] using h
  have hx : f y - f x ≤ inner ℝ g (y - x) := by
    have hc := (StrongConvexFirstOrder.toConvexFirstOrder
      f gradient μ hμ hstrong) y x
    have heq : x - y = -(y - x) := by abel
    rw [heq, inner_neg_right] at hc
    dsimp [g]
    linarith
  have hm : f y - f minimizer ≤
      inner ℝ g (y - minimizer) - μ / 2 * ‖y - minimizer‖ ^ 2 := by
    have hs := hstrong y minimizer
    have heq : minimizer - y = -(y - minimizer) := by abel
    rw [heq, inner_neg_right, norm_neg] at hs
    dsimp [g]
    linarith
  have hobj : f y - f minimizer - (1 - t) * (f x - f minimizer) ≤
      t * inner ℝ g (w - minimizer) -
        μ * t / 2 * ‖y - minimizer‖ ^ 2 := by
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht1)
    have hm' := mul_le_mul_of_nonneg_left hm ht0
    nlinarith
  have hgeom : ‖w - minimizer‖ ^ 2 ≤
      (1 - t) * ‖z - minimizer‖ ^ 2 +
        t * ‖y - minimizer‖ ^ 2 := by
    have heq : w - minimizer =
        (1 - t) • (z - minimizer) + t • (y - minimizer) := by
      dsimp [w]
      rw [smul_sub, smul_sub]
      have hm : (1 - t) • minimizer + t • minimizer = minimizer := by
        rw [← add_smul]
        simp
      have htm : t • minimizer = minimizer - (1 - t) • minimizer := by
        calc
          t • minimizer = ((1 - t) • minimizer + t • minimizer) -
              (1 - t) • minimizer := by abel
          _ = minimizer - (1 - t) • minimizer := by rw [hm]
      rw [htm]
      abel
    rw [heq]
    exact norm_sq_convex_combo _ _ t ht0 ht1
  have hdist : ‖strongNesterovAuxiliary t μ z y g - minimizer‖ ^ 2 =
      ‖w - minimizer‖ ^ 2 -
        2 * (t / μ) * inner ℝ g (w - minimizer) +
          (t / μ) ^ 2 * ‖g‖ ^ 2 := by
    have heq : strongNesterovAuxiliary t μ z y g - minimizer =
        (w - minimizer) + -((t / μ) • g) := by
      dsimp [strongNesterovAuxiliary, w]
      abel
    rw [heq, norm_add_sq_real, inner_neg_right, real_inner_smul_right,
      real_inner_comm (w - minimizer) g,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow]
    rw [sq_abs]
    ring
  have hdesc := gradientStep_descent f gradient L hL hsmooth y
  have htμ : μ * (t / μ) = t := by
    field_simp
  have hgrad : μ * (t / μ) ^ 2 = 1 / L := by
    have hLne : L ≠ 0 := ne_of_gt hL
    have hμne : μ ≠ 0 := ne_of_gt hμ
    field_simp at htsq ⊢
    nlinarith [htsq]
  change f (gradientStep gradient L y) - f minimizer +
      μ / 2 * ‖strongNesterovAuxiliary t μ z y g - minimizer‖ ^ 2 ≤
        (1 - t) * (f x - f minimizer + μ / 2 * ‖z - minimizer‖ ^ 2)
  rw [hdist]
  have hgeom' := mul_le_mul_of_nonneg_left hgeom
    (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 2))
  have hcoef : μ / 2 * (t / μ) ^ 2 = 1 / (2 * L) := by
    calc
      _ = (μ * (t / μ) ^ 2) / 2 := by ring
      _ = (1 / L) / 2 := by rw [hgrad]
      _ = _ := by ring
  have henergy : μ / 2 *
      (‖w - minimizer‖ ^ 2 - 2 * (t / μ) * inner ℝ g (w - minimizer) +
        (t / μ) ^ 2 * ‖g‖ ^ 2) =
      μ / 2 * ‖w - minimizer‖ ^ 2 -
        t * inner ℝ g (w - minimizer) +
          1 / (2 * L) * ‖g‖ ^ 2 := by
    calc
      _ = μ / 2 * ‖w - minimizer‖ ^ 2 -
          (μ * (t / μ)) * inner ℝ g (w - minimizer) +
            (μ / 2 * (t / μ) ^ 2) * ‖g‖ ^ 2 := by ring
      _ = _ := by rw [htμ, hcoef]
  rw [henergy]
  change f (gradientStep gradient L y) ≤ f y - ‖g‖ ^ 2 / (2 * L) at hdesc
  have hdiv : ‖g‖ ^ 2 / (2 * L) = 1 / (2 * L) * ‖g‖ ^ 2 := by ring
  rw [hdiv] at hdesc
  have hdesc' : f (gradientStep gradient L y) - f y +
      1 / (2 * L) * ‖g‖ ^ 2 ≤ 0 := by linarith [hdesc]
  have hobj' : f y - f minimizer -
      (1 - t) * (f x - f minimizer) -
        t * inner ℝ g (w - minimizer) +
          μ * t / 2 * ‖y - minimizer‖ ^ 2 ≤ 0 := by linarith [hobj]
  have hgeom'' : μ / 2 * ‖w - minimizer‖ ^ 2 -
      (1 - t) * (μ / 2 * ‖z - minimizer‖ ^ 2) -
        μ * t / 2 * ‖y - minimizer‖ ^ 2 ≤ 0 := by nlinarith [hgeom']
  nlinarith [hdesc', hobj', hgeom'']

/-- The parameter used by the constant-momentum strongly convex method. -/
def strongNesterovMomentum (L μ : ℝ) : ℝ := Real.sqrt (μ / L)

/-- The potential contraction telescopes to a geometric objective bound. -/
theorem strongNesterov_geometric_rate
    (f : E → ℝ) (gradient : E → E) (L μ t : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htsq : t ^ 2 = μ / L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z : ℕ → E) (minimizer : E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L (strongNesterovExtrapolate t (x k) (z k)))
    (hz : ∀ k, z (k + 1) =
      strongNesterovAuxiliary t μ (z k)
        (strongNesterovExtrapolate t (x k) (z k))
        (gradient (strongNesterovExtrapolate t (x k) (z k))))
    (n : ℕ) :
    f (x n) - f minimizer ≤ (1 - t) ^ n *
      (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2) := by
  have hpot (n : ℕ) :
      f (x n) - f minimizer + μ / 2 * ‖z n - minimizer‖ ^ 2 ≤
        (1 - t) ^ n *
          (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2) := by
    induction n with
    | zero => simp [hinit]
    | succ k ih =>
      have hs := strongNesterov_step_potential f gradient L μ t
        hL hμ ht0 ht1 htsq hsmooth hstrong (x k) (z k) minimizer
      dsimp at hs
      rw [← hx k, ← hz k] at hs
      have hmul := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ht1)
      calc
        _ ≤ (1 - t) *
            (f (x k) - f minimizer + μ / 2 * ‖z k - minimizer‖ ^ 2) := hs
        _ ≤ (1 - t) * ((1 - t) ^ k *
            (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2)) := hmul
        _ = (1 - t) ^ (k + 1) *
            (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2) := by
              rw [pow_succ]
              ring
  have h := hpot n
  nlinarith [mul_nonneg (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖z n - minimizer‖)]

/-- Exact per-iteration exponential rate with `t = √(μ/L)`. -/
theorem strongNesterov_sqrt_geometric_rate
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z : ℕ → E) (minimizer : E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L
        (strongNesterovExtrapolate (strongNesterovMomentum L μ) (x k) (z k)))
    (hz : ∀ k, z (k + 1) =
      strongNesterovAuxiliary (strongNesterovMomentum L μ) μ (z k)
        (strongNesterovExtrapolate (strongNesterovMomentum L μ) (x k) (z k))
        (gradient (strongNesterovExtrapolate
          (strongNesterovMomentum L μ) (x k) (z k))))
    (n : ℕ) :
    f (x n) - f minimizer ≤
      (1 - Real.sqrt (μ / L)) ^ n *
        (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2) := by
  have ht0 : 0 ≤ strongNesterovMomentum L μ := by
    unfold strongNesterovMomentum
    exact Real.sqrt_nonneg _
  have ht1 : strongNesterovMomentum L μ ≤ 1 := by
    unfold strongNesterovMomentum
    exact Real.sqrt_le_one.mpr ((div_le_one hL).2 hμL)
  have htsq : strongNesterovMomentum L μ ^ 2 = μ / L := by
    unfold strongNesterovMomentum
    exact Real.sq_sqrt (div_pos hμ hL).le
  exact strongNesterov_geometric_rate f gradient L μ
    (strongNesterovMomentum L μ) hL hμ ht0 ht1 htsq hsmooth hstrong
    x z minimizer hinit hx hz n

/-- The exponential objective bound implies convergence of both objective
values and iterates to a stationary minimizer. -/
theorem strongNesterov_sqrt_tendsto
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z : ℕ → E) (minimizer : E)
    (hstationary : gradient minimizer = 0)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L
        (strongNesterovExtrapolate (strongNesterovMomentum L μ) (x k) (z k)))
    (hz : ∀ k, z (k + 1) =
      strongNesterovAuxiliary (strongNesterovMomentum L μ) μ (z k)
        (strongNesterovExtrapolate (strongNesterovMomentum L μ) (x k) (z k))
        (gradient (strongNesterovExtrapolate
          (strongNesterovMomentum L μ) (x k) (z k)))) :
    Filter.Tendsto x Filter.atTop (nhds minimizer) ∧
      Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  have hq0 : 0 ≤ 1 - Real.sqrt (μ / L) := by
    have ht : Real.sqrt (μ / L) ≤ 1 :=
      Real.sqrt_le_one.mpr ((div_le_one hL).2 hμL)
    linarith
  have hq1 : 1 - Real.sqrt (μ / L) < 1 := by
    have ht : 0 < Real.sqrt (μ / L) :=
      Real.sqrt_pos.2 (div_pos hμ hL)
    linarith
  have hupper : Filter.Tendsto (fun n : ℕ =>
      (1 - Real.sqrt (μ / L)) ^ n *
        (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2)
  have hgap_nonneg (k : ℕ) : 0 ≤ f (x k) - f minimizer := by
    have h := hstrong minimizer (x k)
    simp only [hstationary, inner_zero_left] at h
    nlinarith [mul_nonneg (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg ‖x k - minimizer‖)]
  have hgap : Filter.Tendsto (fun k => f (x k) - f minimizer)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · exact hgap_nonneg
    · intro k
      exact strongNesterov_sqrt_geometric_rate f gradient L μ
        hL hμ hμL hsmooth hstrong x z minimizer hinit hx hz k
  have hval : Filter.Tendsto (fun k => f (x k))
      Filter.atTop (nhds (f minimizer)) := by
    simpa only [sub_add_cancel, zero_add] using hgap.add_const (f minimizer)
  have hsq : Filter.Tendsto (fun k => ‖x k - minimizer‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hupper' : Filter.Tendsto
        (fun k => (2 / μ) * (f (x k) - f minimizer))
        Filter.atTop (nhds 0) := by simpa using hgap.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper'
    · intro k; exact sq_nonneg _
    · intro k
      have h := hstrong minimizer (x k)
      simp only [hstationary, inner_zero_left] at h
      calc
        _ ≤ (2 * (f (x k) - f minimizer)) / μ :=
          (le_div_iff₀ hμ).2 (by nlinarith [h])
        _ = _ := by ring
  have hnorm : Filter.Tendsto (fun k => ‖x k - minimizer‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact ⟨tendsto_iff_norm_sub_tendsto_zero.mpr hnorm, hval⟩

/-- On a complete space, smooth strong convexity supplies the minimizer. -/
theorem strongNesterov_sqrt_converges
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z : ℕ → E)
    (hinit : z 0 = x 0)
    (hx : ∀ k, x (k + 1) =
      gradientStep gradient L
        (strongNesterovExtrapolate (strongNesterovMomentum L μ) (x k) (z k)))
    (hz : ∀ k, z (k + 1) =
      strongNesterovAuxiliary (strongNesterovMomentum L μ) μ (z k)
        (strongNesterovExtrapolate (strongNesterovMomentum L μ) (x k) (z k))
        (gradient (strongNesterovExtrapolate
          (strongNesterovMomentum L μ) (x k) (z k)))) :
    ∃ minimizer : E,
      (∀ n, f (x n) - f minimizer ≤
        (1 - Real.sqrt (μ / L)) ^ n *
          (f (x 0) - f minimizer + μ / 2 * ‖x 0 - minimizer‖ ^ 2)) ∧
      Filter.Tendsto x Filter.atTop (nhds minimizer) ∧
      Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  obtain ⟨minimizer, hstationary, _⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  refine ⟨minimizer, ?_, ?_⟩
  · intro n
    exact strongNesterov_sqrt_geometric_rate f gradient L μ
      hL hμ hμL hsmooth hstrong x z minimizer hinit hx hz n
  · exact strongNesterov_sqrt_tendsto f gradient L μ hL hμ hμL
      hsmooth hstrong x z minimizer hstationary hinit hx hz

end QuasiNewtonConvergence

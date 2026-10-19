module

public import QuasiNewtonConvergence.ProximalNesterov
public import QuasiNewtonConvergence.Nesterov

@[expose] public section

/-!
# The traditional FISTA parameters

The time parameters satisfy `t₀ = 0`, `t₁ = 1` and
`tₖ₊₁ = (1 + √(1 + 4tₖ²))/2`. At step `k`, the coupling parameter is
`θₖ = 1/tₖ₊₁` and the proximal-gradient step size is `1/L`.
The public rate and convergence theorems use the usual two-sequence momentum
update, with no hypotheses about auxiliary estimate-sequence weights.
-/

noncomputable section
namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- FISTA's time parameter; the zero value is an indexing convenience. -/
def fistaTime : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 + Real.sqrt (1 + 4 * fistaTime k ^ 2)) / 2

@[simp] theorem fistaTime_zero : fistaTime 0 = 0 := rfl

@[simp] theorem fistaTime_one : fistaTime 1 = 1 := by
  norm_num [fistaTime]

theorem fistaTime_succ_ge_one (k : ℕ) : 1 ≤ fistaTime (k + 1) := by
  have h : 1 ≤ Real.sqrt (1 + 4 * fistaTime k ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (fistaTime k)])
  change 1 ≤ (1 + Real.sqrt (1 + 4 * fistaTime k ^ 2)) / 2
  linarith

theorem fistaTime_nonneg (k : ℕ) : 0 ≤ fistaTime k := by
  cases k with
  | zero => simp
  | succ k => linarith [fistaTime_succ_ge_one k]

/-- The scalar identity needed by the exact estimate-sequence theorem. -/
theorem fistaTime_sq_succ (k : ℕ) :
    fistaTime (k + 1) ^ 2 = fistaTime k ^ 2 + fistaTime (k + 1) := by
  have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * fistaTime k ^ 2 by positivity)
  change ((1 + Real.sqrt (1 + 4 * fistaTime k ^ 2)) / 2) ^ 2 =
    fistaTime k ^ 2 + (1 + Real.sqrt (1 + 4 * fistaTime k ^ 2)) / 2
  nlinarith

/-- The traditional coupling parameter at the step from `x k` to `x (k+1)`. -/
def fistaTheta (k : ℕ) : ℝ := 1 / fistaTime (k + 1)

theorem fistaTheta_pos (k : ℕ) : 0 < fistaTheta k := by
  unfold fistaTheta
  exact one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (fistaTime_succ_ge_one k))

theorem fistaTheta_le_one (k : ℕ) : fistaTheta k ≤ 1 := by
  unfold fistaTheta
  exact (div_le_one (by linarith [fistaTime_succ_ge_one k])).2
    (fistaTime_succ_ge_one k)

/-- The usual momentum coefficient multiplying `x (k+1) - x k`. -/
def fistaMomentum (k : ℕ) : ℝ :=
  (fistaTime (k + 1) - 1) / fistaTime (k + 2)

private def fistaAuxiliary (x : ℕ → E) : ℕ → E
  | 0 => x 0
  | k + 1 => x k + fistaTime (k + 1) • (x (k + 1) - x k)

private theorem fista_coupling (x y : ℕ → E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k)) :
    (∀ k, y k = (1 - fistaTheta k) • x k +
      fistaTheta k • fistaAuxiliary x k) ∧
    (∀ k, x (k + 1) = (1 - fistaTheta k) • x k +
      fistaTheta k • fistaAuxiliary x (k + 1)) := by
  have hcancel (k : ℕ) : fistaTheta k * fistaTime (k + 1) = 1 := by
    unfold fistaTheta
    exact one_div_mul_cancel (by linarith [fistaTime_succ_ge_one k])
  constructor
  · intro k
    cases k with
    | zero => simp [hy0, fistaTheta, fistaAuxiliary]
    | succ k =>
      rw [hy k]
      simp only [fistaAuxiliary, smul_add, smul_sub, smul_smul,
        sub_smul, one_smul]
      have hc : fistaMomentum k =
          fistaTheta (k + 1) * fistaTime (k + 1) - fistaTheta (k + 1) := by
        simp only [fistaMomentum, fistaTheta]
        rw [show k + 1 + 1 = k + 2 by omega]
        ring
      rw [hc, sub_smul, sub_smul]
      abel
  · intro k
    simp only [fistaAuxiliary, smul_add, smul_smul, hcancel,
      sub_smul, one_smul]
    abel

private theorem fista_weights (L : ℝ) (hL : 0 < L) :
    let A := fun k => fistaTime k ^ 2 / L
    let a := fun k => fistaTime (k + 1) / L
    (A 0 = 0) ∧ (∀ k, 0 ≤ A k) ∧ (∀ k, 0 < a k) ∧
    (∀ k, A (k + 1) = A k + a k) ∧
    (∀ k, (A k + a k) * fistaTheta k = a k) ∧
    (∀ k, (A k + a k) * L * fistaTheta k ^ 2 = 1) := by
  dsimp
  have hLne : L ≠ 0 := ne_of_gt hL
  have htne (k : ℕ) : fistaTime (k + 1) ≠ 0 := by
    linarith [fistaTime_succ_ge_one k]
  have hsum (k : ℕ) : fistaTime k ^ 2 / L + fistaTime (k + 1) / L =
      fistaTime (k + 1) ^ 2 / L := by rw [fistaTime_sq_succ]; ring
  refine ⟨by simp, fun k => by positivity, ?_, ?_, ?_, ?_⟩
  · intro k
    exact div_pos (by linarith [fistaTime_succ_ge_one k]) hL
  · intro k; exact (hsum k).symm
  · intro k
    rw [hsum]
    unfold fistaTheta
    field_simp [hLne, htne k]
  · intro k
    rw [hsum]
    unfold fistaTheta
    field_simp [hLne, htne k]

/-- FISTA with step size `1/L`: the standard `O(1/n²)` composite objective
bound, obtained by instantiating `proximalNesterov_quadratic_rate`. -/
theorem fista_quadratic_rate (f g : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hsegment : SegmentConvex (composite f g))
    (x y : ℕ → E) (u : E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k))
    (hprox : ∀ k, ProximalOptimality g gradient L (y k) (x (k + 1)))
    (hmin : ∀ v, composite f g u ≤ composite f g v)
    (n : ℕ) (hn : 0 < n) :
    composite f g (x n) - composite f g u ≤
      2 * L * ‖x 0 - u‖ ^ 2 / (n : ℝ) ^ 2 := by
  obtain ⟨hA0, hAn, han, hAsucc, hweight, hexact⟩ := fista_weights L hL
  obtain ⟨hcy, hcx⟩ := fista_coupling x y hy0 hy
  exact proximalNesterov_quadratic_rate f g gradient L hL hsmooth hconvex
    hsegment (fun k => fistaTime k ^ 2 / L) (fun k => fistaTime (k + 1) / L)
    fistaTheta x (fistaAuxiliary x) y u hA0 rfl hAn han
    (fun k => (fistaTheta_pos k).le) fistaTheta_le_one
    hAsucc hweight hexact hcy hcx hprox hmin n hn

/-- For the traditional FISTA parameters and step size `1/L`, the composite
objective values converge to the minimum. -/
theorem fista_tendsto (f g : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hsegment : SegmentConvex (composite f g))
    (x y : ℕ → E) (u : E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k))
    (hprox : ∀ k, ProximalOptimality g gradient L (y k) (x (k + 1)))
    (hmin : ∀ v, composite f g u ≤ composite f g v) :
    Filter.Tendsto (fun k => composite f g (x k)) Filter.atTop
      (nhds (composite f g u)) := by
  have hupper : Filter.Tendsto
      (fun n : ℕ => 2 * L * ‖x 0 - u‖ ^ 2 / (n : ℝ))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) _
  have hgap : Filter.Tendsto (fun n => composite f g (x n) - composite f g u)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall (fun n => sub_nonneg.mpr (hmin (x n)))
    · apply Filter.eventually_atTop.2
      refine ⟨1, fun n hn => ?_⟩
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      exact (fista_quadratic_rate f g gradient L hL hsmooth hconvex hsegment
        x y u hy0 hy hprox hmin n hn).trans
        (div_le_div_of_nonneg_left (by positivity) hnR
          (by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]))
  simpa only [sub_add_cancel, zero_add] using hgap.add_const (composite f g u)

/-- Quadratic growth upgrades FISTA objective convergence to convergence of
the iterates. No stationarity or differentiability of `g` is needed. -/
theorem fista_iterates_tendsto_of_quadratic_growth
    (f g : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hsegment : SegmentConvex (composite f g))
    (x y : ℕ → E) (u : E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k))
    (hprox : ∀ k, ProximalOptimality g gradient L (y k) (x (k + 1)))
    (hgrowth : ∀ v, μ / 2 * ‖v - u‖ ^ 2 ≤
      composite f g v - composite f g u) :
    Filter.Tendsto x Filter.atTop (nhds u) := by
  have hmin (v : E) : composite f g u ≤ composite f g v := by
    have h := hgrowth v
    nlinarith [mul_nonneg (by positivity : 0 ≤ μ / 2) (sq_nonneg ‖v - u‖)]
  have hval := fista_tendsto f g gradient L hL hsmooth hconvex hsegment
    x y u hy0 hy hprox hmin
  have hgap : Filter.Tendsto (fun k => composite f g (x k) - composite f g u)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hval.sub_const (composite f g u)
  have hsq : Filter.Tendsto (fun k => ‖x k - u‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hupper : Filter.Tendsto
        (fun k => (2 / μ) * (composite f g (x k) - composite f g u))
        Filter.atTop (nhds 0) := by simpa using hgap.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact sq_nonneg _
    · intro k
      have h := hgrowth (x k)
      calc
        _ ≤ (2 * (composite f g (x k) - composite f g u)) / μ :=
          (le_div_iff₀ hμ).2 (by nlinarith)
        _ = _ := by ring
  have hnorm : Filter.Tendsto (fun k => ‖x k - u‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- The first-order convexity inequality implies the segment inequality. -/
theorem ConvexFirstOrder.segmentConvex (f : E → ℝ) (gradient : E → E)
    (hconvex : ConvexFirstOrder f gradient) : SegmentConvex f := by
  intro x u θ hθ0 hθ1
  let v := (1 - θ) • x + θ • u
  have hx := mul_le_mul_of_nonneg_left (hconvex v x) (sub_nonneg.mpr hθ1)
  have hu := mul_le_mul_of_nonneg_left (hconvex v u) hθ0
  have hv : (1 - θ) • (x - v) + θ • (u - v) = 0 := by
    dsimp [v]
    module
  have hi := congrArg (inner ℝ (gradient v)) hv
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hi
  change f v ≤ _
  nlinarith

private theorem gradientStep_proximal_zero (gradient : E → E)
    (L : ℝ) (hL : 0 < L) (y : E) :
    ProximalOptimality (fun _ => 0) gradient L y (gradientStep gradient L y) := by
  intro u
  simp [gradientStep, smul_smul, ne_of_gt hL]

/-- Smooth Nesterov acceleration with the traditional FISTA momentum and
gradient step size `1/L`. -/
theorem nesterov_fista_quadratic_rate (f : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x y : ℕ → E) (u : E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k))
    (hx : ∀ k, x (k + 1) = gradientStep gradient L (y k))
    (hmin : ∀ v, f u ≤ f v)
    (n : ℕ) (hn : 0 < n) :
    f (x n) - f u ≤ 2 * L * ‖x 0 - u‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hsegment : SegmentConvex (composite f (fun _ => 0)) := by
    simpa only [SegmentConvex, composite, add_zero] using hconvex.segmentConvex f gradient
  have hprox (k : ℕ) : ProximalOptimality (fun _ => 0) gradient L
      (y k) (x (k + 1)) := by
    rw [hx k]
    exact gradientStep_proximal_zero gradient L hL (y k)
  simpa only [composite, add_zero] using fista_quadratic_rate f (fun _ => 0)
    gradient L hL hsmooth hconvex hsegment x y u hy0 hy hprox
    (by simpa only [composite, add_zero] using hmin) n hn

/-- The objective values of the traditional smooth Nesterov method converge. -/
theorem nesterov_fista_tendsto (f : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x y : ℕ → E) (u : E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k))
    (hx : ∀ k, x (k + 1) = gradientStep gradient L (y k))
    (hmin : ∀ v, f u ≤ f v) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f u)) := by
  have hsegment : SegmentConvex (composite f (fun _ => 0)) := by
    simpa only [SegmentConvex, composite, add_zero] using hconvex.segmentConvex f gradient
  have hprox (k : ℕ) : ProximalOptimality (fun _ => 0) gradient L
      (y k) (x (k + 1)) := by
    rw [hx k]
    exact gradientStep_proximal_zero gradient L hL (y k)
  simpa only [composite, add_zero] using fista_tendsto f (fun _ => 0)
    gradient L hL hsmooth hconvex hsegment x y u hy0 hy hprox
    (by simpa only [composite, add_zero] using hmin)

/-- Smooth strong convexity supplies a minimizer on a complete space and
ensures that the traditional FISTA iterates converge to it. -/
theorem nesterov_fista_strong_converges [CompleteSpace E]
    (f : E → ℝ) (gradient : E → E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x y : ℕ → E)
    (hy0 : y 0 = x 0)
    (hy : ∀ k, y (k + 1) = x (k + 1) +
      fistaMomentum k • (x (k + 1) - x k))
    (hx : ∀ k, x (k + 1) = gradientStep gradient L (y k)) :
    ∃ u : E, (∀ v, f u ≤ f v) ∧
      Filter.Tendsto x Filter.atTop (nhds u) ∧
      Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f u)) := by
  obtain ⟨u, hstationary, hmin⟩ :=
    exists_strongConvex_minimizer f gradient L μ hL hμ hsmooth hstrong
  have hconvex := StrongConvexFirstOrder.toConvexFirstOrder f gradient μ hμ hstrong
  refine ⟨u, hmin, ?_, nesterov_fista_tendsto f gradient L hL hsmooth hconvex
    x y u hy0 hy hx hmin⟩
  apply fista_iterates_tendsto_of_quadratic_growth f (fun _ => 0) gradient L μ
    hL hμ hsmooth hconvex
  · simpa only [SegmentConvex, composite, add_zero] using hconvex.segmentConvex f gradient
  · exact hy0
  · exact hy
  · intro k
    rw [hx k]
    exact gradientStep_proximal_zero gradient L hL (y k)
  · intro v
    have h := hstrong u v
    simp only [hstationary, inner_zero_left] at h
    simp only [composite, add_zero]
    linarith

end QuasiNewtonConvergence

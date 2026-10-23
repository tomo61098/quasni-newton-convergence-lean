module
public import QuasiNewtonConvergence.FrankWolfeAnalysis
public import QuasiNewtonConvergence.Subgradient
public import QuasiNewtonConvergence.StrongConvexMinimizer
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Sign
@[expose] public section

/-!
# Ordinary sign gradient descent

The exact linear oracle on a translated infinity ball uses only coordinate
signs. A moving-box comparison gives the Frank–Wolfe scalar rate under a
uniform comparator-distance bound. Smooth strong convexity supplies a separate
boundedness argument and convergence for square-root steps without that input.
-/

noncomputable section
namespace QuasiNewtonConvergence
variable {ι : Type*} [Fintype ι]

/-- Exact coordinate signs, with sign zero equal to zero. -/
def gradientSign (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sign (g i))

def signGradientStep (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (η : ℝ) (x : EuclideanSpace ℝ ι) := x - η • gradientSign (G x)

omit [Fintype ι] in
/-- The implemented update is unchanged when gradient magnitudes change
while every coordinate sign is preserved. -/
theorem signGradientStep_congr (G H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (η : ℝ) (x : EuclideanSpace ℝ ι)
    (h : ∀ i, Real.sign (G x i) = Real.sign (H x i)) :
    signGradientStep G η x = signGradientStep H η x := by
  have he : gradientSign (G x) = gradientSign (H x) := by
    exact congrArg (WithLp.toLp 2) (funext h)
  simp only [signGradientStep, he]

/-- A translated infinity ball, expressed by coordinate bounds. -/
def signBox (c : EuclideanSpace ℝ ι) (R : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {y | ∀ i, |y i - c i| ≤ R}

omit [Fintype ι] in
theorem sign_box_oracle_mem (g c : EuclideanSpace ℝ ι) (R : ℝ) (hR : 0 ≤ R) :
    c - R • gradientSign g ∈ signBox c R := by
  intro i
  change |c i - R * Real.sign (g i) - c i| ≤ R
  rcases Real.sign_apply_eq (g i) with h | h | h <;> rw [h] <;>
    simp [abs_of_nonneg hR, sub_eq_add_neg, add_assoc, hR]

theorem sign_oracle_scalar (g R z : ℝ) (hz : |z| ≤ R) :
    g * (-R * Real.sign g) ≤ g * z := by
  obtain hn | rfl | hp := lt_trichotomy g 0
  · rw [Real.sign_of_neg hn]
    have h := (abs_le.mp hz).2
    nlinarith
  · simp
  · rw [Real.sign_of_pos hp]
    have h := (abs_le.mp hz).1
    nlinarith

/-- The exact Frank–Wolfe oracle on a box needs only coordinate signs. -/
theorem sign_box_oracle (g c : EuclideanSpace ℝ ι) (R : ℝ)
    (y : EuclideanSpace ℝ ι) (hy : y ∈ signBox c R) :
    inner ℝ g (c - R • gradientSign g) ≤ inner ℝ g y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_le_sum
  intro i _
  have h := sign_oracle_scalar (g i) R (y i - c i) (hy i)
  change (c i - R * Real.sign (g i)) * g i ≤ y i * g i
  nlinarith

theorem gradientSign_norm_sq (g : EuclideanSpace ℝ ι) :
    ‖gradientSign g‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      change Real.sign (g i) ^ 2 ≤ 1
      rcases Real.sign_apply_eq (g i) with h | h | h <;> rw [h] <;> norm_num
    _ = _ := by simp

theorem inner_gradientSign (g : EuclideanSpace ℝ ι) :
    inner ℝ g (gradientSign g) = ∑ i, |g i| := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change Real.sign (g i) * g i = |g i|
  obtain h | h | h := lt_trichotomy (g i) 0
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp [h]
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

theorem gradient_norm_sq_le_sign_inner_sq (g : EuclideanSpace ℝ ι) :
    ‖g‖ ^ 2 ≤ inner ℝ g (gradientSign g) ^ 2 := by
  rw [inner_gradientSign, EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun i _ => abs_nonneg (g i))

omit [Fintype ι] in
/-- The ordinary signGD step is a Frank–Wolfe step on a box centered at
the current iterate. The center moves; this is not the fixed-box update. -/
theorem signGradientStep_as_frankWolfe (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (R γ : ℝ) :
    signGradientStep G (γ * R) x =
      x + γ • ((x - R • gradientSign (G x)) - x) := by
  simp [signGradientStep, sub_eq_add_neg, smul_smul, mul_comm]

/-- Smoothness gives the usual curvature error for an ordinary sign step. -/
theorem signGradientStep_descent (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (L η : ℝ)
    (hL : 0 ≤ L) (hs : SmoothUpper f G L) (x : EuclideanSpace ℝ ι) :
    f (signGradientStep G η x) ≤ f x - η * inner ℝ (G x) (gradientSign (G x)) +
      L * (Fintype.card ι : ℝ) / 2 * η ^ 2 := by
  have h := hs x (signGradientStep G η x)
  have he : signGradientStep G η x - x = -η • gradientSign (G x) := by
    simp [signGradientStep, sub_eq_add_neg, neg_smul, add_assoc]
  rw [he, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hb := mul_le_mul_of_nonneg_left (gradientSign_norm_sq (G x))
    (mul_nonneg (div_nonneg hL (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg η))
  nlinarith

/-- If the comparator lies in the current box, the sign oracle provides
the same objective-error domination used in the Frank–Wolfe proof. -/
theorem signGradient_error_bound (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (hc : ConvexFirstOrder f G) (x u : EuclideanSpace ℝ ι)
    (R : ℝ) (hu : u ∈ signBox x R) :
    f x - f u ≤ R * inner ℝ (G x) (gradientSign (G x)) := by
  have ho := sign_box_oracle (G x) x R u hu
  have hs := hc x u
  rw [inner_sub_right, real_inner_smul_right] at ho
  rw [inner_sub_right] at hs
  linarith

/-- Ordinary signGD inherits the Frank–Wolfe scalar rate when a uniform
box radius around the iterates contains the minimizer. -/
theorem signGradient_rate (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : ℕ → EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ ι) (L R : ℝ)
    (hL : 0 ≤ L) (hs : SmoothUpper f G L) (hc : ConvexFirstOrder f G)
    (hbound : ∀ k, u ∈ signBox (x k) R)
    (hstep : ∀ k, x (k + 1) = signGradientStep G (frankWolfeStepSize k * R) (x k))
    (k : ℕ) : f (x (k + 1)) - f u ≤
      2 * (L * (Fintype.card ι : ℝ) * R ^ 2) / ((k : ℝ) + 3) := by
  apply frankWolfe_scalar_rate (fun k => f (x k) - f u)
    (L * (Fintype.card ι : ℝ) * R ^ 2) (by positivity) _ k
  intro j
  have hd := signGradientStep_descent f G L (frankWolfeStepSize j * R) hL hs (x j)
  rw [← hstep j] at hd
  have hg := mul_le_mul_of_nonneg_left
    (signGradient_error_bound f G hc (x j) u R (hbound j)) (frankWolfeStepSize_mem j).1
  nlinarith

/-- Objective convergence for the same moving-box signGD run. -/
theorem signGradient_values_tendsto (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : ℕ → EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ ι) (L R : ℝ)
    (hL : 0 ≤ L) (hs : SmoothUpper f G L) (hc : ConvexFirstOrder f G)
    (hmin : ∀ y, f u ≤ f y) (hbound : ∀ k, u ∈ signBox (x k) R)
    (hstep : ∀ k, x (k + 1) = signGradientStep G (frankWolfeStepSize k * R) (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f u)) := by
  have hi := tendsto_inv_atTop_zero.comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop 3
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hup : Filter.Tendsto (fun k : ℕ =>
      2 * (L * (Fintype.card ι : ℝ) * R ^ 2) / ((k : ℝ) + 3))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      hi.const_mul (2 * (L * (Fintype.card ι : ℝ) * R ^ 2))
  have he : Filter.Tendsto (fun k => f (x (k + 1)) - f u) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    · intro k; exact sub_nonneg.mpr (hmin _)
    · exact signGradient_rate f G x u L R hL hs hc hbound hstep
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 (by simpa using he.add_const (f u))
/-- Sign descent under a PL inequality needs no assumed bound on iterates.
The proof first bounds the objective errors, then uses scalar decay. -/
theorem sign_scalar_decay (e a α : ℕ → ℝ) (μ C : ℝ)
    (hμ : 0 < μ) (hC : 0 ≤ C) (he : ∀ k, 0 ≤ e k) (ha : ∀ k, 0 ≤ a k)
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ 1)
    (hpl : ∀ k, 2 * μ * e k ≤ a k ^ 2)
    (hrec : ∀ k, e (k + 1) ≤ e k - α k * a k + C * α k ^ 2)
    (hzero : Filter.Tendsto α Filter.atTop (nhds 0))
    (htail : ∀ K, Filter.Tendsto (fun n => ∑ j ∈ Finset.range n, α (K + j))
      Filter.atTop Filter.atTop) : Filter.Tendsto e Filter.atTop (nhds 0) := by
  let T : ℝ := C ^ 2 / (2 * μ)
  let H : ℝ := max (e 0) (T + C)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hH : 0 ≤ H := le_trans (he 0) (le_max_left _ _)
  have hbound (k : ℕ) : e k ≤ H := by
    induction k with
    | zero => exact le_max_left _ _
    | succ k ih =>
      have hsq : α k ^ 2 ≤ 1 := by nlinarith [(hα k).1, (hα k).2]
      by_cases hac : a k ≤ C
      · have het : e k ≤ T := by
          apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).2
          nlinarith [hpl k, ha k]
        have htc : T + C ≤ H := le_max_right _ _
        nlinarith [hrec k, mul_nonneg ((hα k).1) (ha k),
          mul_le_mul_of_nonneg_left hsq hC]
      · have hp : C * α k ≤ a k := by
          nlinarith [mul_le_mul_of_nonneg_left (hα k).2 hC]
        have hm := mul_le_mul_of_nonneg_left hp (hα k).1
        nlinarith [hrec k]
  let c : ℝ := min (2 * μ) (1 / (H + 1))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcμ : c ≤ 2 * μ := min_le_left _ _
  have hcH : c * (H + 1) ≤ 1 := by
    exact (le_div_iff₀ (by positivity : 0 < H + 1)).mp (min_le_right _ _)
  have hlinear (k : ℕ) : c * e k ≤ a k := by
    by_cases hk : a k ≤ 1
    · have hm := mul_le_mul_of_nonneg_right hcμ (he k)
      nlinarith [hpl k, ha k]
    · have hm := mul_le_mul_of_nonneg_left (hbound k) hc.le
      nlinarith
  apply scalar_subgradient_decay e α c C hc hC he (fun k => (hα k).1) hzero htail
  intro k
  have hm := mul_le_mul_of_nonneg_left (hlinear k) (hα k).1
  nlinarith [hrec k]

/-- Ordinary signGD with exact signs and steps `1/√(k+1)` converges in
objective value under smooth strong convexity. No iterate bound is assumed. -/
theorem signGradient_strong_sqrt_values_tendsto (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : ℕ → EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ ι) (L μ : ℝ)
    (hL : 0 ≤ L) (hμ : 0 < μ) (hs : SmoothUpper f G L)
    (hc : StrongConvexFirstOrder f G μ) (hmin : ∀ y, f u ≤ f y)
    (hstep : ∀ k, x (k + 1) = signGradientStep G (sqrtStepSize k) (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f u)) := by
  have he : Filter.Tendsto (fun k => f (x k) - f u) Filter.atTop (nhds 0) := by
    apply sign_scalar_decay _ (fun k => inner ℝ (G (x k)) (gradientSign (G (x k))))
      sqrtStepSize μ (L * (Fintype.card ι : ℝ) / 2) hμ (by positivity)
      (fun k => sub_nonneg.mpr (hmin _))
    · intro k; rw [inner_gradientSign]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    · intro k
      refine ⟨(sqrtStepSize_pos k).le, ?_⟩
      unfold sqrtStepSize
      apply (div_le_one (by positivity)).2
      apply Real.one_le_sqrt.2
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    · intro k
      exact (strongConvex_gradient_bound f G μ hμ hc (x k) u).trans
        (gradient_norm_sq_le_sign_inner_sq _)
    · intro k
      have hd := signGradientStep_descent f G L (sqrtStepSize k) hL hs (x k)
      rw [← hstep k] at hd
      linarith
    · exact sqrtStepSize_tendsto_zero
    · exact sqrtStepSize_tail_sum_diverges
  simpa using he.add_const (f u)

/-- The same ordinary signGD iterates converge to a stationary minimizer. -/
theorem signGradient_strong_sqrt_iterates_tendsto (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : ℕ → EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ ι) (L μ : ℝ)
    (hL : 0 ≤ L) (hμ : 0 < μ) (hs : SmoothUpper f G L)
    (hc : StrongConvexFirstOrder f G μ) (hstationary : G u = 0)
    (hstep : ∀ k, x (k + 1) = signGradientStep G (sqrtStepSize k) (x k)) :
    Filter.Tendsto x Filter.atTop (nhds u) := by
  have hmin (y : EuclideanSpace ℝ ι) : f u ≤ f y := by
    have h := hc u y
    rw [hstationary, inner_zero_left] at h
    nlinarith [sq_nonneg ‖y - u‖]
  have he := signGradient_strong_sqrt_values_tendsto f G x u L μ hL hμ hs hc hmin hstep
  have hg : Filter.Tendsto (fun k => f (x k) - f u) Filter.atTop (nhds 0) := by
    simpa using he.sub_const (f u)
  have hsq : Filter.Tendsto (fun k => ‖x k - u‖ ^ 2) Filter.atTop (nhds 0) := by
    have hup : Filter.Tendsto (fun k => (2 / μ) * (f (x k) - f u))
        Filter.atTop (nhds 0) := by simpa using hg.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    · intro k; exact sq_nonneg _
    · intro k
      have h := hc u (x k)
      rw [hstationary, inner_zero_left] at h
      calc
        _ ≤ (2 * (f (x k) - f u)) / μ := (le_div_iff₀ hμ).2 (by nlinarith)
        _ = _ := by ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h

/-- The ordinary signGD sequence converges to the unique smooth strongly
convex minimizer; existence and boundedness are conclusions. -/
theorem signGradient_strong_sqrt_converges (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : ℕ → EuclideanSpace ℝ ι) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hs : SmoothUpper f G L)
    (hc : StrongConvexFirstOrder f G μ)
    (hstep : ∀ k, x (k + 1) = signGradientStep G (sqrtStepSize k) (x k)) :
    ∃ u, (∀ y, f u ≤ f y) ∧ Filter.Tendsto x Filter.atTop (nhds u) ∧
      Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f u)) := by
  obtain ⟨u, hu, hmin⟩ := exists_strongConvex_minimizer f G L μ hL hμ hs hc
  exact ⟨u, hmin,
    signGradient_strong_sqrt_iterates_tendsto f G x u L μ hL.le hμ hs hc hu hstep,
    signGradient_strong_sqrt_values_tendsto f G x u L μ hL.le hμ hs hc hmin hstep⟩
/-- A concrete sign-only trajectory, defined from its starting point. -/
def signGradientIterate (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x₀ : EuclideanSpace ℝ ι) : ℕ → EuclideanSpace ℝ ι
  | 0 => x₀
  | k + 1 => signGradientStep G (sqrtStepSize k) (signGradientIterate G x₀ k)

theorem signGradientIterate_converges (f : EuclideanSpace ℝ ι → ℝ)
    (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x₀ : EuclideanSpace ℝ ι)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hs : SmoothUpper f G L)
    (hc : StrongConvexFirstOrder f G μ) :
    ∃ u, (∀ y, f u ≤ f y) ∧
      Filter.Tendsto (signGradientIterate G x₀) Filter.atTop (nhds u) ∧
      Filter.Tendsto (fun k => f (signGradientIterate G x₀ k)) Filter.atTop (nhds (f u)) :=
  signGradient_strong_sqrt_converges f G _ L μ hL hμ hs hc (fun _ => rfl)
end QuasiNewtonConvergence

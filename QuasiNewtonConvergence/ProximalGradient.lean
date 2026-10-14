import QuasiNewtonConvergence.GradientDescent

/-! Convergence of the composite proximal gradient method. The proximal
optimality condition is stated in variational form, so it also applies to
nonsmooth convex regularizers. -/

noncomputable section
namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def composite (f g : E → ℝ) (x : E) : ℝ := f x + g x

/-- First-order optimality for the exact proximal model at `x`.
For convex `g`, this characterizes the minimizer of
`g(z)+⟪∇f(x),z-x⟫+(L/2)‖z-x‖²`. -/
def ProximalOptimality (g : E → ℝ) (gradient : E → E)
    (L : ℝ) (x z : E) : Prop :=
  ∀ u, g u - g z ≥
    inner ℝ (-(gradient x) - L • (z - x)) (u - z)

private theorem distance_identity (x z u : E) :
    2 * inner ℝ (z - x) (u - z) =
      ‖u - x‖ ^ 2 - ‖z - x‖ ^ 2 - ‖u - z‖ ^ 2 := by
  have hv : u - x = (u - z) + (z - x) := by abel
  rw [hv, norm_add_sq_real, real_inner_comm]
  ring

/-- The fundamental proximal-gradient three-point inequality. -/
theorem proximal_three_point (f g : E → ℝ) (gradient : E → E)
    (L : ℝ) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x z u : E) (hprox : ProximalOptimality g gradient L x z) :
    composite f g z - composite f g u ≤
      L / 2 * (‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) := by
  have hs := hsmooth x z
  have hc := hconvex x u
  have hp := hprox u
  have hi := distance_identity x z u
  have hnorm1 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev x u
  have hnorm2 : ‖z - u‖ = ‖u - z‖ := norm_sub_rev z u
  rw [hnorm1, hnorm2]
  simp only [inner_sub_left, inner_neg_left, real_inner_smul_left] at hp
  have hgrad : inner ℝ (gradient x) (z - x) =
      inner ℝ (gradient x) (u - x) - inner ℝ (gradient x) (u - z) := by
    have hv : z - x = (u - x) - (u - z) := by abel
    rw [hv, inner_sub_right]
  rw [hgrad] at hs
  rw [inner_sub_left] at hi
  have hiscaled := congrArg (fun t : ℝ => L / 2 * t) hi
  dsimp [composite]
  nlinarith [hiscaled]

/-- A proximal step decreases the composite objective. -/
theorem proximal_descent (f g : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 ≤ L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x z : E) (hprox : ProximalOptimality g gradient L x z) :
    composite f g z ≤ composite f g x := by
  have h := proximal_three_point f g gradient L hsmooth hconvex x z x hprox
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  nlinarith [mul_nonneg (div_nonneg hL (by norm_num : (0:ℝ) ≤ 2))
    (sq_nonneg ‖z - x‖)]

/-- The standard `O(1/k)` last-iterate bound. -/
theorem proximalGradient_convex_rate (f g : E → ℝ) (gradient : E → E)
    (L : ℝ) (hL : 0 ≤ L) (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (x : ℕ → E) (u : E)
    (hstep : ∀ k, ProximalOptimality g gradient L (x k) (x (k + 1)))
    (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * (composite f g (x (k + 1)) - composite f g u) ≤
      L / 2 * ‖x 0 - u‖ ^ 2 := by
  have hmono (j : ℕ) : composite f g (x (j + 1)) ≤ composite f g (x j) :=
    proximal_descent f g gradient L hL hsmooth hconvex _ _ (hstep j)
  apply potential_last_iterate_bound
    (fun j => composite f g (x j) - composite f g u)
    (fun j => L / 2 * ‖x j - u‖ ^ 2)
    (fun j => sub_le_sub_right (hmono j) (composite f g u))
  · intro j
    simpa only [mul_sub] using
      proximal_three_point f g gradient L hsmooth hconvex
        (x j) (x (j + 1)) u (hstep j)
  · intro j
    exact mul_nonneg (div_nonneg hL (by norm_num)) (sq_nonneg _)

/-- If the smooth part is strongly convex, its curvature improves the
three-point inequality. -/
theorem proximal_strong_three_point (f g : E → ℝ) (gradient : E → E)
    (L μ : ℝ) (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x z u : E) (hprox : ProximalOptimality g gradient L x z) :
    composite f g z - composite f g u ≤
      L / 2 * (‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) -
        μ / 2 * ‖x - u‖ ^ 2 := by
  have hs := hsmooth x z
  have hc := hstrong x u
  have hp := hprox u
  have hi := distance_identity x z u
  have hnorm1 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev x u
  have hnorm2 : ‖z - u‖ = ‖u - z‖ := norm_sub_rev z u
  rw [hnorm1, hnorm2]
  simp only [inner_sub_left, inner_neg_left, real_inner_smul_left] at hp
  have hgrad : inner ℝ (gradient x) (z - x) =
      inner ℝ (gradient x) (u - x) - inner ℝ (gradient x) (u - z) := by
    have hv : z - x = (u - x) - (u - z) := by abel
    rw [hv, inner_sub_right]
  rw [hgrad] at hs
  rw [inner_sub_left] at hi
  have hiscaled := congrArg (fun t : ℝ => L / 2 * t) hi
  dsimp [composite]
  nlinarith [hiscaled]

/-- Squared distances contract at rate `1-μ/L` for a composite minimizer. -/
theorem proximalGradient_strong_distance_rate (f g : E → ℝ)
    (gradient : E → E) (L μ : ℝ) (hL : 0 < L) (_hμ : 0 < μ)
    (hμL : μ ≤ L) (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x : ℕ → E) (u : E)
    (hmin : ∀ v, composite f g u ≤ composite f g v)
    (hstep : ∀ k, ProximalOptimality g gradient L (x k) (x (k + 1)))
    (k : ℕ) :
    ‖x k - u‖ ^ 2 ≤ (1 - μ / L) ^ k * ‖x 0 - u‖ ^ 2 := by
  have hq : 0 ≤ 1 - μ / L := sub_nonneg.mpr ((div_le_one hL).mpr hμL)
  have hc (j : ℕ) : ‖x (j + 1) - u‖ ^ 2 ≤
      (1 - μ / L) * ‖x j - u‖ ^ 2 := by
    have hp := proximal_strong_three_point f g gradient L μ hsmooth hstrong
      (x j) (x (j + 1)) u (hstep j)
    have hm := hmin (x (j + 1))
    have hbasic : L / 2 * ‖x (j + 1) - u‖ ^ 2 ≤
        (L - μ) / 2 * ‖x j - u‖ ^ 2 := by linarith only [hp, hm]
    calc
      ‖x (j + 1) - u‖ ^ 2 =
          (2 / L) * (L / 2 * ‖x (j + 1) - u‖ ^ 2) := by
            field_simp
      _ ≤ (2 / L) * ((L - μ) / 2 * ‖x j - u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbasic (by positivity)
      _ = (1 - μ / L) * ‖x j - u‖ ^ 2 := by field_simp
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖x (k + 1) - u‖ ^ 2 ≤ (1 - μ / L) * ‖x k - u‖ ^ 2 := hc k
      _ ≤ (1 - μ / L) * ((1 - μ / L) ^ k * ‖x 0 - u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih hq
      _ = (1 - μ / L) ^ (k + 1) * ‖x 0 - u‖ ^ 2 := by
        rw [pow_succ]; ring

/-- The objective gap also decays geometrically, one step after the
distance estimate. -/
theorem proximalGradient_strong_objective_rate (f g : E → ℝ)
    (gradient : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hμL : μ ≤ L) (hsmooth : SmoothUpper f gradient L)
    (hstrong : StrongConvexFirstOrder f gradient μ)
    (x : ℕ → E) (u : E)
    (hmin : ∀ v, composite f g u ≤ composite f g v)
    (hstep : ∀ k, ProximalOptimality g gradient L (x k) (x (k + 1)))
    (k : ℕ) :
    composite f g (x (k + 1)) - composite f g u ≤
      L / 2 * (1 - μ / L) ^ k * ‖x 0 - u‖ ^ 2 := by
  have hp := proximal_three_point f g gradient L hsmooth
    (fun x y => by
      have h := hstrong x y
      nlinarith [mul_nonneg (div_nonneg hμ.le (by norm_num : (0:ℝ) ≤ 2))
        (sq_nonneg ‖y - x‖)])
    (x k) (x (k + 1)) u (hstep k)
  have hd := proximalGradient_strong_distance_rate f g gradient L μ
    hL hμ hμL hsmooth hstrong x u hmin hstep k
  have hcoef : 0 ≤ L / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hd hcoef
  nlinarith [mul_nonneg hcoef (sq_nonneg ‖x (k + 1) - u‖)]

end QuasiNewtonConvergence

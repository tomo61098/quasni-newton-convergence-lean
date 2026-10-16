import QuasiNewtonConvergence.Bregman
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Function

/-!
# Existence of finite-dimensional Bregman proximal steps

An affine lower bound for the objective and strong convexity of the kernel
make each proximal objective coercive. Continuity then gives a minimizer.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A global affine support at every point implies ordinary convexity;
the supporting vector need not be a gradient. -/
private theorem convexOn_of_affine_support (F : E → ℝ) (v : E → E)
    (hsupport : ∀ x y, F x + inner ℝ (v x) (y - x) ≤ F y) :
    ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hsupport z x) ha
  have hy := mul_le_mul_of_nonneg_left (hsupport z y) hb
  have hv : a • (x - z) + b • (y - z) = 0 := by
    rw [smul_sub, smul_sub]
    have hz : a • z + b • z = z := by rw [← add_smul, hab, one_smul]
    calc
      _ = (a • x + b • y) - (a • z + b • z) := by abel
      _ = 0 := by rw [hz]; exact sub_self _
  have hi : a * inner ℝ (v z) (x - z) + b * inner ℝ (v z) (y - z) = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hv,
      inner_zero_right]
  have hz : a * F z + b * F z = F z := by rw [← add_mul, hab, one_mul]
  change F z ≤ a * F x + b * F y
  nlinarith only [hx, hy, hi, hz]

/-- Minimizing the Bregman subproblem implies its variational optimality
condition when the kernel has the stated gradient at the minimizer.
Convexity of `F` suffices; `F` need not be differentiable. -/
theorem bregmanProximalOptimality_of_minimizes
    (F h : E → ℝ) (dh : E → E) (L : ℝ) (x z : E)
    (hF : ConvexOn ℝ Set.univ F) (hh : HasGradientAt h (dh z) z)
    (hmin : ∀ u, F z + L * bregmanD h dh x z ≤
      F u + L * bregmanD h dh x u) :
    BregmanProximalOptimality F h dh L x z := by
  intro u
  let d := u - z
  let φ : ℝ → ℝ := fun t => t * (F u - F z) +
    L * (h (z + t • d) - h z - t * inner ℝ (dh x) d)
  have hpath : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    convert ((hasDerivAt_id' (0 : ℝ)).smul_const d).const_add z using 1 <;> simp
  have hhpath : HasDerivAt (fun t : ℝ => h (z + t • d))
      (inner ℝ (dh z) d) 0 := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hφ : HasDerivAt φ
      (F u - F z + L * (inner ℝ (dh z) d - inner ℝ (dh x) d)) 0 := by
    convert ((hasDerivAt_id' (0 : ℝ)).mul_const (F u - F z)).add
      (((hhpath.sub_const (h z)).sub
        ((hasDerivAt_id' (0 : ℝ)).mul_const (inner ℝ (dh x) d))).const_mul L) using 1 <;>
      simp [φ, funext_iff]
  have hφnonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ φ t := by
    have hc := hF.2 (Set.mem_univ z) (Set.mem_univ u)
      (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
    have hp := hmin (z + t • d)
    have heq : (1 - t) • z + t • u = z + t • d := by
      dsimp [d]
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [heq] at hc
    simp only [smul_eq_mul] at hc
    have hD : bregmanD h dh x (z + t • d) - bregmanD h dh x z =
        h (z + t • d) - h z - t * inner ℝ (dh x) d := by
      have heq : z + t • d - x = (z - x) + t • d := by abel
      simp only [bregmanD, heq, inner_add_right, real_inner_smul_right]
      ring
    dsimp [φ]
    nlinarith [congrArg (fun v : ℝ => L * v) hD]
  have hnonneg : 0 ≤ F u - F z +
      L * (inner ℝ (dh z) d - inner ℝ (dh x) d) := by
    apply ge_of_tendsto hφ.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with t ht0 ht1
    simp only [Set.mem_Ioi] at ht0
    simp only [zero_add, smul_eq_mul]
    have hφzero : φ 0 = 0 := by simp [φ]
    rw [hφzero, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr ht0.le) (hφnonneg t ht0.le ht1.le)
  simp only [inner_neg_left, real_inner_smul_left, inner_sub_left]
  dsimp [d] at hnonneg
  linarith

/-- Existence of a minimizer of a Bregman proximal subproblem. The affine
lower bound is automatic for a finite-valued convex function on a finite-
dimensional space, but is stated explicitly to avoid invoking a supporting-
hyperplane theorem. -/
theorem exists_bregmanProximal_minimizer
    (F h : E → ℝ) (dh : E → E) (x v : E) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ z, F x + inner ℝ v (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ) :
    ∃ z : E, ∀ u : E,
      F z + L * bregmanD h dh x z ≤
        F u + L * bregmanD h dh x u := by
  let Q : E → ℝ := fun z => F z + L * bregmanD h dh x z
  let R : ℝ := 1 + 2 * ‖v‖ / (L * μ)
  have hLM : 0 < L * μ := mul_pos hL hμ
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hRbound : 2 * ‖v‖ ≤ L * μ * R := by
    have hcancel : (L * μ) * (2 * ‖v‖ / (L * μ)) = 2 * ‖v‖ :=
      mul_div_cancel₀ _ (ne_of_gt hLM)
    calc
      2 * ‖v‖ = (L * μ) * (2 * ‖v‖ / (L * μ)) := hcancel.symm
      _ ≤ (L * μ) * (1 + 2 * ‖v‖ / (L * μ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hLM.le
      _ = L * μ * R := rfl
  have houtside : ∀ z : E, R ≤ ‖z - x‖ → Q x ≤ Q z := by
    intro z hz
    have hd : μ / 2 * ‖z - x‖ ^ 2 ≤ bregmanD h dh x z := by
      have h := hstrong x z
      dsimp [bregmanD]
      linarith
    have hinner : -‖v‖ * ‖z - x‖ ≤ inner ℝ v (z - x) := by
      have h := real_inner_le_norm (-v) (z - x)
      rw [inner_neg_left, norm_neg] at h
      linarith
    have hquad : ‖v‖ * ‖z - x‖ ≤
        (L * μ / 2) * ‖z - x‖ ^ 2 := by
      have hcoeff : 2 * ‖v‖ ≤ L * μ * ‖z - x‖ :=
        hRbound.trans (mul_le_mul_of_nonneg_left hz hLM.le)
      have hmul := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (z - x))
      nlinarith
    have hDscaled := mul_le_mul_of_nonneg_left hd hL.le
    have hFx := hFlower z
    simp only [Q, bregmanD_self, mul_zero, add_zero]
    linarith
  have hQcont : Continuous Q := by
    dsimp [Q, bregmanD]
    have hi : Continuous (fun z : E => inner ℝ (dh x) (z - x)) :=
      continuous_const.inner (continuous_id.sub continuous_const)
    exact hFcont.add (continuous_const.mul
      ((hhcont.sub continuous_const).sub hi))
  have hxball : x ∈ Metric.closedBall x R := by
    simp [Metric.mem_closedBall, hR]
  obtain ⟨z, hz, hmin⟩ :=
    (isCompact_closedBall x R).exists_isMinOn ⟨x, hxball⟩
      hQcont.continuousOn
  refine ⟨z, ?_⟩
  intro u
  by_cases hu : u ∈ Metric.closedBall x R
  · exact hmin hu
  · have huR : R ≤ ‖u - x‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      simpa only [norm_sub_rev x u] using (le_of_lt (lt_of_not_ge hu))
    exact (hmin hxball).trans (houtside u huR)

/-- Choose an exact minimizer for the proximal problem at every current point. -/
def bregmanProximalStep (F h : E → ℝ) (dh : E → E) (v : E → E)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ) (x : E) : E :=
  Classical.choose (exists_bregmanProximal_minimizer F h dh x (v x) L μ
    hL hμ hFcont hhcont (hFlower x) hstrong)

theorem bregmanProximalStep_minimizes (F h : E → ℝ) (dh : E → E)
    (v : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ) (x u : E) :
    F (bregmanProximalStep F h dh v L μ hL hμ hFcont hhcont
      hFlower hstrong x) +
      L * bregmanD h dh x
        (bregmanProximalStep F h dh v L μ hL hμ hFcont hhcont
          hFlower hstrong x) ≤ F u + L * bregmanD h dh x u := by
  exact Classical.choose_spec
    (exists_bregmanProximal_minimizer F h dh x (v x) L μ
      hL hμ hFcont hhcont (hFlower x) hstrong) u

/-- Every iterate of this recursively defined proximal trajectory exists. -/
def bregmanProximalIterate (F h : E → ℝ) (dh : E → E)
    (v : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => bregmanProximalStep F h dh v L μ hL hμ hFcont hhcont
      hFlower hstrong (bregmanProximalIterate F h dh v L μ hL hμ
        hFcont hhcont hFlower hstrong x₀ k)

theorem bregmanProximalIterate_minimizes (F h : E → ℝ) (dh : E → E)
    (v : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ) (x₀ : E)
    (k : ℕ) (u : E) :
    let x := bregmanProximalIterate F h dh v L μ hL hμ hFcont
      hhcont hFlower hstrong x₀
    F (x (k + 1)) + L * bregmanD h dh (x k) (x (k + 1)) ≤
      F u + L * bregmanD h dh (x k) u := by
  exact bregmanProximalStep_minimizes F h dh v L μ hL hμ hFcont
    hhcont hFlower hstrong _ u

/-- The constructed proximal trajectory satisfies the variational condition
used by the convergence theorems when the kernel is differentiable. -/
theorem bregmanProximalIterate_optimality (F h : E → ℝ) (dh : E → E)
    (v : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ)
    (hhgrad : ∀ z, HasGradientAt h (dh z) z) (x₀ : E) (k : ℕ) :
    let x := bregmanProximalIterate F h dh v L μ hL hμ hFcont
      hhcont hFlower hstrong x₀
    BregmanProximalOptimality F h dh L (x k) (x (k + 1)) := by
  apply bregmanProximalOptimality_of_minimizes F h dh L
    _ _ (convexOn_of_affine_support F v hFlower) (hhgrad _)
  exact bregmanProximalIterate_minimizes F h dh v L μ hL hμ hFcont
    hhcont hFlower hstrong x₀ k

/-- The recursively constructed Bregman proximal iterates satisfy the
`O(1/k)` objective bound, with no supplied sequence or step oracle. -/
theorem bregmanProximalIterate_convex_rate (F h : E → ℝ) (dh : E → E)
    (v : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ)
    (hhgrad : ∀ z, HasGradientAt h (dh z) z) (x₀ u : E) (k : ℕ) :
    let x := bregmanProximalIterate F h dh v L μ hL hμ hFcont
      hhcont hFlower hstrong x₀
    ((k + 1 : ℕ) : ℝ) * (F (x (k + 1)) - F u) ≤
      L * bregmanD h dh x₀ u := by
  have hkernel : ConvexFirstOrder h dh := by
    intro x y
    have hs := hstrong x y
    have hnonneg : 0 ≤ μ / 2 * ‖y - x‖ ^ 2 := by positivity
    linarith
  exact bregmanProximal_convex_rate F h dh L hL.le hkernel
    _ u (bregmanProximalIterate_optimality F h dh v L μ hL hμ hFcont
      hhcont hFlower hstrong hhgrad x₀) k

/-- Objective values of the constructed trajectory converge to the minimum. -/
theorem bregmanProximalIterate_tendsto (F h : E → ℝ) (dh : E → E)
    (v : E → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : Continuous F) (hhcont : Continuous h)
    (hFlower : ∀ x z, F x + inner ℝ (v x) (z - x) ≤ F z)
    (hstrong : StrongConvexFirstOrder h dh μ)
    (hhgrad : ∀ z, HasGradientAt h (dh z) z) (x₀ u : E)
    (hmin : ∀ z, F u ≤ F z) :
    let x := bregmanProximalIterate F h dh v L μ hL hμ hFcont
      hhcont hFlower hstrong x₀
    Filter.Tendsto (fun k => F (x k)) Filter.atTop (nhds (F u)) := by
  apply bregman_rate_tendsto F h dh L _ u hmin
  exact bregmanProximalIterate_convex_rate F h dh v L μ hL hμ hFcont
    hhcont hFlower hstrong hhgrad x₀ u

/-- Existence for a changing proximal objective, such as the linearized
composite model in proximal gradient descent. -/
theorem exists_bregmanProximal_steps
    (F : ℕ → E → ℝ) (h : E → ℝ) (dh : E → E)
    (x v : ℕ → E) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hFcont : ∀ k, Continuous (F k)) (hhcont : Continuous h)
    (hFlower : ∀ k z, F k (x k) +
      inner ℝ (v k) (z - x k) ≤ F k z)
    (hstrong : StrongConvexFirstOrder h dh μ) :
    ∃ z : ℕ → E, ∀ k u,
      F k (z k) + L * bregmanD h dh (x k) (z k) ≤
        F k u + L * bregmanD h dh (x k) u := by
  have hstep (k : ℕ) : ∃ z : E, ∀ u,
      F k z + L * bregmanD h dh (x k) z ≤
        F k u + L * bregmanD h dh (x k) u :=
    exists_bregmanProximal_minimizer (F k) h dh (x k) (v k)
      L μ hL hμ (hFcont k) hhcont (hFlower k) hstrong
  exact ⟨fun k => Classical.choose (hstep k),
    fun k u => Classical.choose_spec (hstep k) u⟩

end QuasiNewtonConvergence

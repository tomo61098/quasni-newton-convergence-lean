import QuasiNewtonConvergence.Bregman
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Continuous

set_option maxHeartbeats 10000

/-!
# Existence of finite-dimensional Bregman proximal steps

An affine lower bound for the objective and strong convexity of the kernel
make each proximal objective coercive. Continuity then gives a minimizer.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

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

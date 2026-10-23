module

public import QuasiNewtonConvergence.FrankWolfe
public import QuasiNewtonConvergence.FrankWolfeLineSearch
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.Module

@[expose] public section
noncomputable section
namespace QuasiNewtonConvergence
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The usual analytical hypotheses imply both first-order inequalities. -/
theorem frankWolfe_first_order (S : Set E) (f : E → ℝ) (G : E → E)
    (L : ℝ≥0) (hc : ConvexOn ℝ S f)
    (hg : ∀ x ∈ S, HasGradientAt f (G x) x)
    (hl : LipschitzOnWith L G S) (x : E) (hx : x ∈ S) (y : E) (hy : y ∈ S) :
    (f x + inner ℝ (G x) (y - x) ≤ f y) ∧
    (f y ≤ f x + inner ℝ (G x) (y - x) + (L : ℝ) / 2 * ‖y - x‖ ^ 2) := by
  let z : ℝ → E := fun t => x + t • (y - x)
  have hz (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : z t ∈ S :=
    hc.1.add_smul_sub_mem hx hy ht
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (z t)) (inner ℝ (G (z t)) (y - x)) t := by
    convert (hg (z t) (hz t ht)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (y - x) |>.const_add x) using 1 <;>
      simp [Function.comp_def, z]
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (z t)) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro a ha b hb u v hu hv huv
    have h := hc.2 (hz a ha) (hz b hb) hu hv huv
    have he : u • z a + v • z b = z (u • a + v • b) := by
      calc
        _ = (u + v) • x + (u * a + v * b) • (y - x) := by dsimp [z]; module
        _ = _ := by rw [huv]; simp [z]
    rwa [he] at h
  have hsupport := hconv.le_slope_of_hasDerivAt (by simp) (by simp)
    (by norm_num : (0 : ℝ) < 1) (hd 0 (by simp))
  have hs : f x + inner ℝ (G x) (y - x) ≤ f y := by
    have h : inner ℝ (G x) (y - x) ≤ f y - f x := by simpa [slope, z] using hsupport
    linarith
  refine ⟨hs, ?_⟩
  let B : ℝ → ℝ := fun t => f x + t * inner ℝ (G x) (y - x) +
    (L : ℝ) / 2 * ‖y - x‖ ^ 2 * t ^ 2
  have hB (t : ℝ) : HasDerivAt B
      (inner ℝ (G x) (y - x) + (L : ℝ) * ‖y - x‖ ^ 2 * t) t := by
    convert (((hasDerivAt_id t).mul_const (inner ℝ (G x) (y - x))).const_add (f x)).add
      (((hasDerivAt_id t).pow 2).const_mul ((L : ℝ) / 2 * ‖y - x‖ ^ 2)) using 1
    · ext q
      simp only [B, Pi.add_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      inner ℝ (G (z t)) (y - x) ≤
        inner ℝ (G x) (y - x) + (L : ℝ) * ‖y - x‖ ^ 2 * t := by
    have hn := hl.norm_sub_le (hz t ⟨ht.1, ht.2.le⟩) hx
    have hi := real_inner_le_norm (G (z t) - G x) (y - x)
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg (y - x))
    simp only [z, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1] at hm
    rw [inner_sub_left] at hi
    dsimp [z] at hi ⊢
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (show f (z 0) ≤ B 0 by simp [z, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hb (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  simpa [z, B] using h

namespace FrankWolfeProblem
/-- Construct the problem from convexity, genuine gradients, and their
Lipschitz bound; the diameter and first-order inequalities are all derived. -/
def ofGradient (S : Set E) (hcompact : IsCompact S) (f : E → ℝ) (G : E → E)
    (L : ℝ≥0) (hc : ConvexOn ℝ S f)
    (hg : ∀ x ∈ S, HasGradientAt f (G x) x)
    (hl : LipschitzOnWith L G S) : FrankWolfeProblem E :=
  ofCompact S hcompact hc.1 f G L L.coe_nonneg
    (fun x hx y hy => (frankWolfe_first_order S f G L hc hg hl x hx y hy).2)
    (fun x hx y hy => (frankWolfe_first_order S f G L hc hg hl x hx y hy).1)
end FrankWolfeProblem

/-- End-to-end line-search convergence under conventional analytical
hypotheses, including existence and the zero-gap stopping rule. -/
theorem frankWolfe_lineSearch_converges (S : Set E) (hcompact : IsCompact S)
    (f : E → ℝ) (G : E → E) (L : ℝ≥0) (hc : ConvexOn ℝ S f)
    (hg : ∀ x ∈ S, HasGradientAt f (G x) x) (hl : LipschitzOnWith L G S)
    (x₀ : E) (hx₀ : x₀ ∈ S) :
    let P := FrankWolfeProblem.ofGradient S hcompact f G L hc hg hl
    ∃ r : P.StepRun, r.x 0 = x₀ ∧ r.IsLineSearch ∧
      (∀ k, r.gap k = 0 → r.α k = 0) ∧
      ∃ u ∈ S, (∀ y ∈ S, f u ≤ f y) ∧
        (∀ k, f (r.x (k + 1)) - f u ≤
          2 * (L : ℝ) * Metric.diam S ^ 2 / ((k : ℝ) + 3)) ∧
        Filter.Tendsto (fun k => f (r.x k)) Filter.atTop (nhds (f u)) := by
  let P := FrankWolfeProblem.ofGradient S hcompact f G L hc hg hl
  have hcont : ContinuousOn f S := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  obtain ⟨r, hr, hls, hstop⟩ := P.exists_lineSearch_run hcompact hcont x₀ hx₀
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn ⟨x₀, hx₀⟩ hcont
  exact ⟨r, hr, hls, hstop, u, hu, hmin, r.lineSearch_rate hls u hu,
    r.lineSearch_values_tendsto hls u hu hmin⟩
end QuasiNewtonConvergence

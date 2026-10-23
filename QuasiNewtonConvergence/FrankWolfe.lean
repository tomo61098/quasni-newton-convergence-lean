module

public import QuasiNewtonConvergence.GradientDescent
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# Frank–Wolfe convergence

Exact linear minimization and steps `2 / (k + 2)` give the objective bound
`f(xₖ) - f(u) ≤ 2 L D² / (k + 2)` for `k ≥ 1`. The first-order smoothness
and convexity inequalities are needed only on the feasible set. No interior
minimizer or vanishing gradient at the constrained optimum is required.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth convex constrained problem with a supplied diameter bound.
The gradient map is specified by its first-order inequalities on the set. -/
structure FrankWolfeProblem (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  feasible : Set E
  objective : E → ℝ
  gradient : E → E
  L : ℝ
  D : ℝ
  L_nonneg : 0 ≤ L
  D_nonneg : 0 ≤ D
  convex : Convex ℝ feasible
  smooth : ∀ x ∈ feasible, ∀ y ∈ feasible,
    objective y ≤ objective x + inner ℝ (gradient x) (y - x) +
      L / 2 * ‖y - x‖ ^ 2
  support : ∀ x ∈ feasible, ∀ y ∈ feasible,
    objective x + inner ℝ (gradient x) (y - x) ≤ objective y
  diameter_bound : ∀ x ∈ feasible, ∀ y ∈ feasible, ‖y - x‖ ≤ D

/-- The standard open-loop Frank–Wolfe step schedule, indexed from zero. -/
def frankWolfeStepSize (k : ℕ) : ℝ := 2 / ((k : ℝ) + 2)

theorem frankWolfeStepSize_mem (k : ℕ) :
    0 ≤ frankWolfeStepSize k ∧ frankWolfeStepSize k ≤ 1 := by
  constructor
  · unfold frankWolfeStepSize; positivity
  · unfold frankWolfeStepSize
    exact (div_le_one (by positivity)).2 (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith)

/-- Any exact oracle choices are allowed, including ties. -/
structure FrankWolfeProblem.Run (P : FrankWolfeProblem E) where
  x : ℕ → E
  s : ℕ → E
  initial_mem : x 0 ∈ P.feasible
  oracle_mem : ∀ k, s k ∈ P.feasible
  oracle_min : ∀ k, ∀ y ∈ P.feasible,
    inner ℝ (P.gradient (x k)) (s k) ≤ inner ℝ (P.gradient (x k)) y
  step : ∀ k, x (k + 1) = x k + frankWolfeStepSize k • (s k - x k)

namespace FrankWolfeProblem

/-- Compact feasible sets supply their own finite diameter bound. -/
def ofCompact (S : Set E) (hcompact : IsCompact S) (hconvex : Convex ℝ S)
    (f : E → ℝ) (gradient : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hsmooth : ∀ x ∈ S, ∀ y ∈ S,
      f y ≤ f x + inner ℝ (gradient x) (y - x) + L / 2 * ‖y - x‖ ^ 2)
    (hsupport : ∀ x ∈ S, ∀ y ∈ S,
      f x + inner ℝ (gradient x) (y - x) ≤ f y) : FrankWolfeProblem E where
  feasible := S
  objective := f
  gradient := gradient
  L := L
  D := Metric.diam S
  L_nonneg := hL
  D_nonneg := Metric.diam_nonneg
  convex := hconvex
  smooth := hsmooth
  support := hsupport
  diameter_bound := by
    intro x hx y hy
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hcompact.isBounded hy hx

variable {P : FrankWolfeProblem E} (r : P.Run)

/-- Every iterate remains feasible. -/
theorem Run.feasible (k : ℕ) : r.x k ∈ P.feasible := by
  induction k with
  | zero => exact r.initial_mem
  | succ k ih =>
    rw [r.step k]
    exact P.convex.add_smul_sub_mem ih (r.oracle_mem k) (frankWolfeStepSize_mem k)

/-- The computable Frank–Wolfe gap. -/
def Run.gap (k : ℕ) : ℝ :=
  inner ℝ (P.gradient (r.x k)) (r.x k - r.s k)

/-- The oracle gap certifies the objective error against any feasible point. -/
theorem Run.error_le_gap (u : E) (hu : u ∈ P.feasible) (k : ℕ) :
    P.objective (r.x k) - P.objective u ≤ r.gap k := by
  have hs := P.support (r.x k) (r.feasible k) u hu
  have ho := r.oracle_min k u hu
  simp only [inner_sub_right, Run.gap] at *
  linarith

/-- Smoothness along the feasible segment gives the standard curvature bound. -/
theorem Run.descent (k : ℕ) :
    P.objective (r.x (k + 1)) ≤ P.objective (r.x k) -
      frankWolfeStepSize k * r.gap k +
        (P.L * P.D ^ 2 / 2) * frankWolfeStepSize k ^ 2 := by
  have hs := P.smooth (r.x k) (r.feasible k)
    (r.x (k + 1)) (r.feasible (k + 1))
  have hd := P.diameter_bound (r.x k) (r.feasible k) (r.s k) (r.oracle_mem k)
  have hsq : ‖r.s k - r.x k‖ ^ 2 ≤ P.D ^ 2 := by
    nlinarith [norm_nonneg (r.s k - r.x k)]
  have hsub : r.x (k + 1) - r.x k =
      frankWolfeStepSize k • (r.s k - r.x k) := by rw [r.step k]; abel
  rw [hsub, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs] at hs
  have hgap : inner ℝ (P.gradient (r.x k)) (r.s k - r.x k) = -r.gap k := by
    simp only [Run.gap, inner_sub_right]; ring
  rw [hgap] at hs
  have hb := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (div_nonneg P.L_nonneg (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg (frankWolfeStepSize k)))
  nlinarith

/-- The scalar objective-error recurrence is derived from the actual update. -/
theorem Run.error_recurrence (u : E) (hu : u ∈ P.feasible) (k : ℕ) :
    P.objective (r.x (k + 1)) - P.objective u ≤
      (1 - frankWolfeStepSize k) * (P.objective (r.x k) - P.objective u) +
        (P.L * P.D ^ 2 / 2) * frankWolfeStepSize k ^ 2 := by
  have hd := r.descent k
  have hg := mul_le_mul_of_nonneg_left (r.error_le_gap u hu k)
    (frankWolfeStepSize_mem k).1
  nlinarith

end FrankWolfeProblem

/-- The standard `O(1/k)` induction. The unit first step removes dependence
on the initial error, so no assumption on `e 0` is needed. -/
theorem frankWolfe_scalar_rate (e : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrec : ∀ k, e (k + 1) ≤ (1 - frankWolfeStepSize k) * e k +
      C / 2 * frankWolfeStepSize k ^ 2) (k : ℕ) :
    e (k + 1) ≤ 2 * C / ((k : ℝ) + 3) := by
  induction k with
  | zero =>
    have h := hrec 0
    norm_num [frankWolfeStepSize] at h ⊢
    linarith
  | succ k ih =>
    have hc := (frankWolfeStepSize_mem (k + 1)).2
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hc)
    have hr := hrec (k + 1)
    have hbound :
        (1 - frankWolfeStepSize (k + 1)) * (2 * C / ((k : ℝ) + 3)) +
          C / 2 * frankWolfeStepSize (k + 1) ^ 2 ≤
            2 * C / (((k + 1 : ℕ) : ℝ) + 3) := by
      simp only [frankWolfeStepSize, Nat.cast_add, Nat.cast_one]
      have hp : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have hq : (0 : ℝ) < (k : ℝ) + 1 + 3 := by positivity
      field_simp
      nlinarith
    linarith

namespace FrankWolfeProblem

variable {P : FrankWolfeProblem E} (r : P.Run)

/-- Last-iterate objective rate, valid against any feasible comparator.
In the usual indexing this is `2 L D² / (n + 2)` for `n ≥ 1`. -/
theorem Run.rate (u : E) (hu : u ∈ P.feasible) (k : ℕ) :
    P.objective (r.x (k + 1)) - P.objective u ≤
      2 * P.L * P.D ^ 2 / ((k : ℝ) + 3) := by
  simpa only [mul_assoc] using frankWolfe_scalar_rate
    (fun k => P.objective (r.x k) - P.objective u) (P.L * P.D ^ 2)
    (mul_nonneg P.L_nonneg (sq_nonneg _)) (r.error_recurrence u hu) k

/-- Objective values converge to the constrained minimum. -/
theorem Run.values_tendsto (u : E) (hu : u ∈ P.feasible)
    (hmin : ∀ y ∈ P.feasible, P.objective u ≤ P.objective y) :
    Filter.Tendsto (fun k => P.objective (r.x k)) Filter.atTop
      (nhds (P.objective u)) := by
  have hupper : Filter.Tendsto
      (fun k : ℕ => 2 * P.L * P.D ^ 2 / ((k : ℝ) + 3))
      Filter.atTop (nhds 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 3
        (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [div_eq_mul_inv, Function.comp_def] using hi.const_mul (2 * P.L * P.D ^ 2)
  have hgap : Filter.Tendsto
      (fun k => P.objective (r.x (k + 1)) - P.objective u)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact sub_nonneg.mpr (hmin _ (r.feasible (k + 1)))
    · exact r.rate u hu
  have hshift := hgap.add_const (P.objective u)
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 (by simpa using hshift)

/-- A quadratic growth condition at the constrained optimum also gives
convergence of the iterates. -/
theorem Run.iterates_tendsto_of_quadratic_growth (u : E) (hu : u ∈ P.feasible)
    (hmin : ∀ y ∈ P.feasible, P.objective u ≤ P.objective y)
    (μ : ℝ) (hμ : 0 < μ)
    (hgrowth : ∀ y ∈ P.feasible,
      μ / 2 * ‖y - u‖ ^ 2 ≤ P.objective y - P.objective u) :
    Filter.Tendsto r.x Filter.atTop (nhds u) := by
  have hgap : Filter.Tendsto (fun k => P.objective (r.x k) - P.objective u)
      Filter.atTop (nhds 0) := by
    simpa using (r.values_tendsto u hu hmin).sub_const (P.objective u)
  have hsquare : Filter.Tendsto (fun k => ‖r.x k - u‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hupper : Filter.Tendsto
        (fun k => (2 / μ) * (P.objective (r.x k) - P.objective u))
        Filter.atTop (nhds 0) := by simpa using hgap.const_mul (2 / μ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact sq_nonneg _
    · intro k
      have h := hgrowth (r.x k) (r.feasible k)
      calc
        _ ≤ (2 * (P.objective (r.x k) - P.objective u)) / μ :=
          (le_div_iff₀ hμ).2 (by nlinarith)
        _ = _ := by ring
  have hnorm : Filter.Tendsto (fun k => ‖r.x k - u‖) Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsquare
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Compactness ensures that every exact linear subproblem is attained,
and hence that a Frank–Wolfe run exists from any feasible starting point. -/
theorem exists_run (P : FrankWolfeProblem E) (hcompact : IsCompact P.feasible) (x₀ : E)
    (hx₀ : x₀ ∈ P.feasible) : ∃ r : P.Run, r.x 0 = x₀ := by
  have hex (x : E) : ∃ s ∈ P.feasible,
      ∀ y ∈ P.feasible, inner ℝ (P.gradient x) s ≤ inner ℝ (P.gradient x) y := by
    exact hcompact.exists_isMinOn ⟨x₀, hx₀⟩
      (show Continuous (fun y => inner ℝ (P.gradient x) y) from
        continuous_const.inner continuous_id).continuousOn
  choose oracle hmem hmin using hex
  let x : ℕ → E := fun n => Nat.rec x₀
    (fun k z => z + frankWolfeStepSize k • (oracle z - z)) n
  refine ⟨{ x := x
            s := fun k => oracle (x k)
            initial_mem := hx₀
            oracle_mem := fun k => hmem (x k)
            oracle_min := fun k => hmin (x k)
            step := fun k => rfl }, rfl⟩

/-- On a compact feasible set with a continuous objective, a constrained
minimizer exists and every exact Frank–Wolfe run converges in value to it. -/
theorem Run.compact_converges (hcompact : IsCompact P.feasible)
    (hcontinuous : ContinuousOn P.objective P.feasible) :
    ∃ u ∈ P.feasible,
      (∀ y ∈ P.feasible, P.objective u ≤ P.objective y) ∧
      (∀ k, P.objective (r.x (k + 1)) - P.objective u ≤
        2 * P.L * P.D ^ 2 / ((k : ℝ) + 3)) ∧
      Filter.Tendsto (fun k => P.objective (r.x k)) Filter.atTop
        (nhds (P.objective u)) := by
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn ⟨r.x 0, r.initial_mem⟩ hcontinuous
  exact ⟨u, hu, hmin, r.rate u hu, r.values_tendsto u hu hmin⟩

end FrankWolfeProblem

end QuasiNewtonConvergence

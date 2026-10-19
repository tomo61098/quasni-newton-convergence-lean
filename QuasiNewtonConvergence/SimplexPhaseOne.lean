module

public import QuasiNewtonConvergence.KarmarkarProjective
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Phase I of the simplex method

For `Ax = b`, `x ≥ 0`, artificial variables `a ≥ 0` give the auxiliary
system `Ax + a = b`. If `b ≥ 0`, the point `(x,a) = (0,b)` is feasible.
The minimum auxiliary objective `∑ aᵢ` is zero exactly when the original
system is feasible. The all-zero vector is generally not feasible.
-/

namespace QuasiNewtonConvergence

open scoped BigOperators

variable {n m : ℕ}

/-- Feasibility for a standard-form linear program. -/
def phaseOneOriginalFeasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ A x = b

/-- Feasibility after adding nonnegative artificial variables. -/
def phaseOneAuxiliaryFeasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) (a : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∀ i, 0 ≤ a i) ∧
    ∀ i, A x i + a i = b i

/-- The Phase I objective: drive all artificial variables to zero. -/
def phaseOneObjective (a : Fin m → ℝ) : ℝ := ∑ i, a i

/-- With nonnegative right-hand sides, original variables zero and
artificial variables equal to `b` give an explicit feasible start. -/
theorem phaseOne_initial_feasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) :
    phaseOneAuxiliaryFeasible A b 0 b := by
  refine ⟨fun j => le_refl 0, hb, ?_⟩
  intro i
  simp

/-- The *entire* zero vector solves the auxiliary equations only when
`b = 0`. In the usual Phase I start, only the original variables are zero. -/
theorem phaseOne_all_zero_iff_rhs_zero
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) :
    phaseOneAuxiliaryFeasible A b 0 0 ↔ b = 0 := by
  constructor
  · intro h
    ext i
    simpa using (h.2.2 i).symm
  · intro hb
    subst b
    exact phaseOne_initial_feasible A 0 (fun i => le_refl 0)

/-- The inequality formulation for which ordinary slack variables are
introduced. -/
def phaseOneInequalityFeasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, A x i ≤ b i

/-- Ordinary nonnegative slacks convert `Ax ≤ b` into `Ax + s = b`.
No Phase I objective is involved in this equivalence. -/
theorem simplex_slack_iff_inequality
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    phaseOneInequalityFeasible A b x ↔
      ∃ s, phaseOneAuxiliaryFeasible A b x s := by
  constructor
  · rintro ⟨hx, hAx⟩
    refine ⟨fun i => b i - A x i, hx, ?_, ?_⟩
    · intro i
      exact sub_nonneg.mpr (hAx i)
    · intro i
      ring
  · rintro ⟨s, hx, hs, hAx⟩
    refine ⟨hx, ?_⟩
    intro i
    have := hAx i
    linarith [hs i]

theorem phaseOne_objective_nonneg
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ phaseOneObjective a := by
  unfold phaseOneObjective
  exact Finset.sum_nonneg (fun i hi => ha i)

/-- A zero sum of nonnegative artificial variables forces each one to zero. -/
theorem phaseOne_artificials_zero
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hzero : phaseOneObjective a = 0) (i : Fin m) :
    a i = 0 := by
  unfold phaseOneObjective at hzero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => ha j)).mp hzero i (Finset.mem_univ i)

/-- An auxiliary feasible solution with objective zero gives an original
feasible solution by discarding its artificial variables. -/
theorem phaseOne_zero_gives_original
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) (a : Fin m → ℝ)
    (haux : phaseOneAuxiliaryFeasible A b x a)
    (hzero : phaseOneObjective a = 0) :
    phaseOneOriginalFeasible A b x := by
  rcases haux with ⟨hx, ha, hAx⟩
  refine ⟨hx, ?_⟩
  ext i
  have hai := phaseOne_artificials_zero a ha hzero i
  have hi := hAx i
  linarith

/-- Every original feasible point extends to an auxiliary feasible point
of zero Phase I cost. -/
theorem phaseOne_original_gives_zero
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : phaseOneOriginalFeasible A b x) :
    phaseOneAuxiliaryFeasible A b x 0 ∧
      phaseOneObjective (0 : Fin m → ℝ) = 0 := by
  rcases hx with ⟨hpos, hAx⟩
  constructor
  · refine ⟨hpos, fun i => le_refl 0, ?_⟩
    intro i
    simp [hAx]
  · simp [phaseOneObjective]

/-- The precise Phase I feasibility equivalence. -/
theorem phaseOne_feasible_iff_zero_objective
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) :
    (∃ x, phaseOneOriginalFeasible A b x) ↔
      ∃ x a, phaseOneAuxiliaryFeasible A b x a ∧
        phaseOneObjective a = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, 0, phaseOne_original_gives_zero A b x hx⟩
  · rintro ⟨x, a, haux, hzero⟩
    exact ⟨x, phaseOne_zero_gives_original A b x a haux hzero⟩

/-- If the attained auxiliary optimum is positive, the original system
has no feasible point. -/
theorem phaseOne_positive_optimum_infeasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (astar : Fin m → ℝ)
    (hmin : ∀ x a, phaseOneAuxiliaryFeasible A b x a →
      phaseOneObjective astar ≤ phaseOneObjective a)
    (hpos : 0 < phaseOneObjective astar) :
    ¬ ∃ x, phaseOneOriginalFeasible A b x := by
  rintro ⟨x, hx⟩
  obtain ⟨haux, hzero⟩ := phaseOne_original_gives_zero A b x hx
  have hle := hmin x 0 haux
  rw [hzero] at hle
  exact (not_le_of_gt hpos) hle

/-- For an attained Phase I optimum, zero optimal value is equivalent to
feasibility of the original equality-constrained problem. -/
theorem phaseOne_optimum_zero_iff_original_feasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (xstar : Fin n → ℝ) (astar : Fin m → ℝ)
    (hstar : phaseOneAuxiliaryFeasible A b xstar astar)
    (hmin : ∀ x a, phaseOneAuxiliaryFeasible A b x a →
      phaseOneObjective astar ≤ phaseOneObjective a) :
    phaseOneObjective astar = 0 ↔
      ∃ x, phaseOneOriginalFeasible A b x := by
  constructor
  · intro hzero
    exact ⟨xstar, phaseOne_zero_gives_original A b xstar astar hstar hzero⟩
  · rintro ⟨x, hx⟩
    obtain ⟨haux, hzero⟩ := phaseOne_original_gives_zero A b x hx
    have hle := hmin x 0 haux
    rw [hzero] at hle
    have hnonneg := phaseOne_objective_nonneg astar hstar.2.1
    linarith

/-! A two-artificial-variable version works without changing signs of rows. -/

def phaseOnePositivePart (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => max (b i) 0

def phaseOneNegativePart (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => max (-b i) 0

theorem phaseOne_positive_negative_parts (b : Fin m → ℝ) (i : Fin m) :
    phaseOnePositivePart b i - phaseOneNegativePart b i = b i := by
  dsimp [phaseOnePositivePart, phaseOneNegativePart]
  by_cases h : 0 ≤ b i
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    simp
  · have h' : b i ≤ 0 := le_of_not_ge h
    rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
    simp

/-- Auxiliary feasibility using a positive and a negative artificial
variable in every row, with no sign assumption on `b`. -/
def phaseOneSignedAuxiliaryFeasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (p q : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ q i) ∧
    ∀ i, A x i + p i - q i = b i

def phaseOneSignedObjective (p q : Fin m → ℝ) : ℝ :=
  ∑ i, (p i + q i)

theorem phaseOne_signed_initial_feasible
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) :
    phaseOneSignedAuxiliaryFeasible A b 0
      (phaseOnePositivePart b) (phaseOneNegativePart b) := by
  refine ⟨fun j => le_refl 0, ?_, ?_, ?_⟩
  · intro i
    exact le_max_right _ _
  · intro i
    exact le_max_right _ _
  · intro i
    simpa using phaseOne_positive_negative_parts b i

theorem phaseOne_signed_zero_gives_original
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) (p q : Fin m → ℝ)
    (haux : phaseOneSignedAuxiliaryFeasible A b x p q)
    (hzero : phaseOneSignedObjective p q = 0) :
    phaseOneOriginalFeasible A b x := by
  rcases haux with ⟨hx, hp, hq, hAx⟩
  have hpair (i : Fin m) : p i + q i = 0 := by
    unfold phaseOneSignedObjective at hzero
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => add_nonneg (hp j) (hq j))).mp hzero i (Finset.mem_univ i)
  refine ⟨hx, ?_⟩
  ext i
  have hpi := hp i
  have hqi := hq i
  have hsum := hpair i
  have hi := hAx i
  linarith

theorem phaseOne_signed_original_gives_zero
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : phaseOneOriginalFeasible A b x) :
    phaseOneSignedAuxiliaryFeasible A b x 0 0 ∧
      phaseOneSignedObjective (0 : Fin m → ℝ) 0 = 0 := by
  rcases hx with ⟨hpos, hAx⟩
  constructor
  · refine ⟨hpos, fun i => le_refl 0, fun i => le_refl 0, ?_⟩
    intro i
    simp [hAx]
  · simp [phaseOneSignedObjective]

theorem phaseOne_signed_feasible_iff_zero_objective
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) :
    (∃ x, phaseOneOriginalFeasible A b x) ↔
      ∃ x p q, phaseOneSignedAuxiliaryFeasible A b x p q ∧
        phaseOneSignedObjective p q = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, 0, 0, phaseOne_signed_original_gives_zero A b x hx⟩
  · rintro ⟨x, p, q, haux, hzero⟩
    exact ⟨x, phaseOne_signed_zero_gives_original A b x p q haux hzero⟩

end QuasiNewtonConvergence

module
public import QuasiNewtonConvergence.FrankWolfe
@[expose] public section
noncomputable section
namespace QuasiNewtonConvergence.FrankWolfeProblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : FrankWolfeProblem E}

/-- Frank–Wolfe with arbitrary feasible step lengths. -/
structure StepRun (P : FrankWolfeProblem E) where
  x : ℕ → E
  s : ℕ → E
  α : ℕ → ℝ
  initial_mem : x 0 ∈ P.feasible
  oracle_mem : ∀ k, s k ∈ P.feasible
  oracle_min : ∀ k, ∀ y ∈ P.feasible,
    inner ℝ (P.gradient (x k)) (s k) ≤ inner ℝ (P.gradient (x k)) y
  alpha_mem : ∀ k, α k ∈ Set.Icc 0 1
  step : ∀ k, x (k + 1) = x k + α k • (s k - x k)

def Run.toStepRun (r : P.Run) : P.StepRun where
  x := r.x
  s := r.s
  α := frankWolfeStepSize
  initial_mem := r.initial_mem
  oracle_mem := r.oracle_mem
  oracle_min := r.oracle_min
  alpha_mem := frankWolfeStepSize_mem
  step := r.step

namespace StepRun
variable (r : P.StepRun)
theorem feasible (k : ℕ) : r.x k ∈ P.feasible := by
  induction k with
  | zero => exact r.initial_mem
  | succ k ih =>
    rw [r.step k]
    exact P.convex.add_smul_sub_mem ih (r.oracle_mem k) (r.alpha_mem k)

def gap (k : ℕ) : ℝ := inner ℝ (P.gradient (r.x k)) (r.x k - r.s k)

theorem error_le_gap (u : E) (hu : u ∈ P.feasible) (k : ℕ) :
    P.objective (r.x k) - P.objective u ≤ r.gap k := by
  have hs := P.support (r.x k) (r.feasible k) u hu
  have ho := r.oracle_min k u hu
  simp only [gap, inner_sub_right] at *
  linarith

/-- A zero oracle gap certifies global constrained optimality. -/
theorem optimal_of_gap_zero (k : ℕ) (h : r.gap k = 0) :
    ∀ y ∈ P.feasible, P.objective (r.x k) ≤ P.objective y := by
  intro y hy
  have he := r.error_le_gap y hy k
  rw [h] at he
  linarith

/-- Curvature bound for any trial step on the oracle segment. -/
theorem trial_bound (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    P.objective (r.x k + t • (r.s k - r.x k)) ≤ P.objective (r.x k) -
      t * r.gap k + P.L * P.D ^ 2 / 2 * t ^ 2 := by
  have hs := P.smooth (r.x k) (r.feasible k) _
    (P.convex.add_smul_sub_mem (r.feasible k) (r.oracle_mem k) ht)
  have hd := P.diameter_bound (r.x k) (r.feasible k) (r.s k) (r.oracle_mem k)
  have hsq : ‖r.s k - r.x k‖ ^ 2 ≤ P.D ^ 2 := by
    nlinarith [norm_nonneg (r.s k - r.x k)]
  simp only [add_sub_cancel_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hg : inner ℝ (P.gradient (r.x k)) (r.s k - r.x k) = -r.gap k := by
    simp only [gap, inner_sub_right]; ring
  rw [hg] at hs
  have hb := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (div_nonneg P.L_nonneg (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg t))
  nlinarith

theorem descent (k : ℕ) :
    P.objective (r.x (k + 1)) ≤ P.objective (r.x k) -
      r.α k * r.gap k + P.L * P.D ^ 2 / 2 * r.α k ^ 2 := by
  rw [r.step k]
  exact r.trial_bound k _ (r.alpha_mem k)

/-- Exact minimization over the feasible segment. -/
def IsLineSearch : Prop := ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
  P.objective (r.x (k + 1)) ≤ P.objective (r.x k + t • (r.s k - r.x k))

/-- Zero-gap stopping makes all subsequent iterates equal, even if the
linear oracle resolves ties differently at subsequent indices. -/
theorem stays_of_gap_zero (hstop : ∀ k, r.gap k = 0 → r.α k = 0)
    (k : ℕ) (hz : r.gap k = 0) (n : ℕ) : r.x (k + n) = r.x k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg : r.gap (k + n) = 0 := by
      have h₁ := r.oracle_min (k + n) (r.s k) (r.oracle_mem k)
      have h₂ := r.oracle_min k (r.s (k + n)) (r.oracle_mem (k + n))
      rw [ih] at h₁
      dsimp [gap] at hz ⊢
      rw [ih]
      simp only [inner_sub_right] at *
      linarith
    rw [Nat.add_succ, r.step (k + n), hstop _ hg, zero_smul, add_zero]
    exact ih

theorem monotone_values (hls : r.IsLineSearch) (k : ℕ) :
    P.objective (r.x (k + 1)) ≤ P.objective (r.x k) := by
  simpa using hls k 0 (by simp)

/-- Any step at least as good as the prescribed trial step has the same rate. -/
theorem rate (hbetter : ∀ k, P.objective (r.x (k + 1)) ≤
      P.objective (r.x k + frankWolfeStepSize k • (r.s k - r.x k)))
    (u : E) (hu : u ∈ P.feasible) (k : ℕ) :
    P.objective (r.x (k + 1)) - P.objective u ≤
      2 * P.L * P.D ^ 2 / ((k : ℝ) + 3) := by
  apply frankWolfe_scalar_rate (fun k => P.objective (r.x k) - P.objective u)
    (P.L * P.D ^ 2) (mul_nonneg P.L_nonneg (sq_nonneg _)) _ k |>.trans_eq
      (by ring)
  intro j
  have hd := (hbetter j).trans (r.trial_bound j _ (frankWolfeStepSize_mem j))
  have hg := mul_le_mul_of_nonneg_left (r.error_le_gap u hu j)
    (frankWolfeStepSize_mem j).1
  nlinarith

theorem lineSearch_rate (hls : r.IsLineSearch) (u : E) (hu : u ∈ P.feasible) (k : ℕ) :
    P.objective (r.x (k + 1)) - P.objective u ≤
      2 * P.L * P.D ^ 2 / ((k : ℝ) + 3) :=
  r.rate (fun j => hls j _ (frankWolfeStepSize_mem j)) u hu k

theorem lineSearch_values_tendsto (hls : r.IsLineSearch) (u : E) (hu : u ∈ P.feasible)
    (hmin : ∀ y ∈ P.feasible, P.objective u ≤ P.objective y) :
    Filter.Tendsto (fun k => P.objective (r.x k)) Filter.atTop (nhds (P.objective u)) := by
  have hi := tendsto_inv_atTop_zero.comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop 3
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hup : Filter.Tendsto (fun k : ℕ => 2 * P.L * P.D ^ 2 / ((k : ℝ) + 3))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using hi.const_mul (2 * P.L * P.D ^ 2)
  have he : Filter.Tendsto (fun k => P.objective (r.x (k + 1)) - P.objective u)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    · intro k; exact sub_nonneg.mpr (hmin _ (r.feasible _))
    · exact r.lineSearch_rate hls u hu
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 (by simpa using he.add_const (P.objective u))
end StepRun

/-- Compactness supplies both exact oracles and exact segment minimizers.
The chosen step is zero whenever the oracle gap is zero. -/
theorem exists_lineSearch_run (P : FrankWolfeProblem E)
    (hcompact : IsCompact P.feasible) (hcont : ContinuousOn P.objective P.feasible)
    (x₀ : E) (hx₀ : x₀ ∈ P.feasible) :
    ∃ r : P.StepRun, r.x 0 = x₀ ∧ r.IsLineSearch ∧
      (∀ k, r.gap k = 0 → r.α k = 0) := by
  have horacle (x : E) : ∃ s ∈ P.feasible, ∀ y ∈ P.feasible,
      inner ℝ (P.gradient x) s ≤ inner ℝ (P.gradient x) y := by
    exact hcompact.exists_isMinOn ⟨x₀, hx₀⟩
      (show Continuous (fun y => inner ℝ (P.gradient x) y) from
        continuous_const.inner continuous_id).continuousOn
  choose oracle hmem hmin using horacle
  let phi (x : {x // x ∈ P.feasible}) (t : ℝ) :=
    P.objective (x.val + t • (oracle x.val - x.val))
  have hchoice (x : {x // x ∈ P.feasible}) : ∃ a ∈ Set.Icc (0 : ℝ) 1,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, phi x a ≤ phi x t) ∧
      (inner ℝ (P.gradient x.val) (x.val - oracle x.val) = 0 → a = 0) := by
    by_cases hz : inner ℝ (P.gradient x.val) (x.val - oracle x.val) = 0
    · refine ⟨0, by simp, ?_, fun _ => rfl⟩
      intro t ht
      have hs := P.support x.val x.property
        (x.val + t • (oracle x.val - x.val))
        (P.convex.add_smul_sub_mem x.property (hmem x.val) ht)
      have he : inner ℝ (P.gradient x.val) (oracle x.val - x.val) = 0 := by
        simp only [inner_sub_right] at hz ⊢
        linarith
      simpa [phi, real_inner_smul_right, he] using hs
    · have hc : ContinuousOn (phi x) (Set.Icc (0 : ℝ) 1) := by
        apply hcont.comp (continuous_const.add
          (continuous_id.smul continuous_const)).continuousOn
        intro t ht
        exact P.convex.add_smul_sub_mem x.property (hmem x.val) ht
      obtain ⟨a, ha, hm⟩ := isCompact_Icc.exists_isMinOn
        (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hc
      exact ⟨a, ha, hm, fun h => (hz h).elim⟩
  choose alpha ham hamin hastop using hchoice
  let next (x : {x // x ∈ P.feasible}) : {x // x ∈ P.feasible} :=
    ⟨x.val + alpha x • (oracle x.val - x.val),
      P.convex.add_smul_sub_mem x.property (hmem x.val) (ham x)⟩
  let xs : ℕ → {x // x ∈ P.feasible} := fun n =>
    Nat.rec ⟨x₀, hx₀⟩ (fun _ x => next x) n
  let r : P.StepRun := {
    x := fun k => (xs k).val
    s := fun k => oracle (xs k).val
    α := fun k => alpha (xs k)
    initial_mem := hx₀
    oracle_mem := fun k => hmem (xs k).val
    oracle_min := fun k => hmin (xs k).val
    alpha_mem := fun k => ham (xs k)
    step := fun k => rfl }
  exact ⟨r, rfl, fun k => hamin (xs k), fun k => hastop (xs k)⟩
end QuasiNewtonConvergence.FrankWolfeProblem

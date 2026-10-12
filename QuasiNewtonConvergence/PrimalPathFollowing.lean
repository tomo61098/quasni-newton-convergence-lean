import QuasiNewtonConvergence.KarmarkarProjective
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Primal path following with a logarithmic barrier

For a standard-form linear program, the central path minimizes
`t * cᵀx - ∑ i, log (x i)` over `Ax = b`, `x > 0`. Its stationarity equation
gives a primal objective gap of at most `n / t`. The results below also give
the geometric rate for a growing sequence of barrier parameters.
-/

noncomputable section
namespace QuasiNewtonConvergence

open scoped BigOperators

/-- The primal logarithmic barrier objective on the positive orthant. -/
def primalLogBarrierObjective {n : ℕ} (c x : Fin n → ℝ) (t : ℝ) : ℝ :=
  t * karmarkarCost c x - ∑ i, Real.log (x i)

/-- The tangent form of the central-path first-order equation. -/
def PrimalCentralStationarity {n : ℕ}
    (c x : Fin n → ℝ) (t : ℝ)
    (feasible : (Fin n → ℝ) → Prop) : Prop :=
  ∀ z, feasible z →
    ∑ i, (t * c i - (x i)⁻¹) * (x i - z i) = 0

/-- A stationary positive point of the log-barrier subproblem is within
`n / t` in objective value of every nonnegative feasible point. -/
theorem primal_log_barrier_gap
    {n : ℕ} (c x z : Fin n → ℝ) (t : ℝ)
    (ht : 0 < t) (hx : ∀ i, 0 < x i) (hz : ∀ i, 0 ≤ z i)
    (hstationary :
      ∑ i, (t * c i - (x i)⁻¹) * (x i - z i) = 0) :
    karmarkarCost c x - karmarkarCost c z ≤ (n : ℝ) / t := by
  have hsum : t * (karmarkarCost c x - karmarkarCost c z) =
      (n : ℝ) - ∑ i, z i / x i := by
    have hterm (i : Fin n) :
        (t * c i - (x i)⁻¹) * (x i - z i) =
          t * (c i * x i - c i * z i) - (1 - z i / x i) := by
      have hxi : x i ≠ 0 := ne_of_gt (hx i)
      field_simp [hxi]
    simp_rw [hterm] at hstationary
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hstationary
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hstationary
    unfold karmarkarCost
    linarith
  have hnonneg : 0 ≤ ∑ i, z i / x i :=
    Finset.sum_nonneg (fun i hi => div_nonneg (hz i) (hx i).le)
  apply (le_div_iff₀ ht).mpr
  linarith

/-- Coordinatewise centrality residual for a feasible positive point.
At an exact barrier minimizer, the residual `e` is zero. -/
def PrimalApproxCentralStationarity {n : ℕ}
    (c x : Fin n → ℝ) (t β : ℝ)
    (feasible : (Fin n → ℝ) → Prop) : Prop :=
  ∃ e : Fin n → ℝ,
    (∀ i, |e i| ≤ β) ∧
    ∀ z, feasible z →
      ∑ i, (t * c i - (1 + e i) / x i) * (x i - z i) = 0

/-- Approximate centrality still gives an `O(n / t)` primal gap. -/
theorem primal_approx_log_barrier_gap
    {n : ℕ} (c x z e : Fin n → ℝ) (t β : ℝ)
    (ht : 0 < t) (hβ : β < 1)
    (hx : ∀ i, 0 < x i) (hz : ∀ i, 0 ≤ z i)
    (he : ∀ i, |e i| ≤ β)
    (hstationary :
      ∑ i, (t * c i - (1 + e i) / x i) * (x i - z i) = 0) :
    karmarkarCost c x - karmarkarCost c z ≤
      (n : ℝ) * (1 + β) / t := by
  have hsum : t * (karmarkarCost c x - karmarkarCost c z) =
      (∑ i, (1 + e i)) - ∑ i, (1 + e i) * (z i / x i) := by
    have hterm (i : Fin n) :
        (t * c i - (1 + e i) / x i) * (x i - z i) =
          t * (c i * x i - c i * z i) -
            ((1 + e i) - (1 + e i) * (z i / x i)) := by
      have hxi : x i ≠ 0 := ne_of_gt (hx i)
      field_simp [hxi]
    simp_rw [hterm] at hstationary
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hstationary
    unfold karmarkarCost
    linarith
  have hpositive (i : Fin n) : 0 ≤ 1 + e i := by
    have := (abs_le.mp (he i)).1
    linarith
  have hupper (i : Fin n) : 1 + e i ≤ 1 + β := by
    have := (abs_le.mp (he i)).2
    linarith
  have hnonneg : 0 ≤ ∑ i, (1 + e i) * (z i / x i) :=
    Finset.sum_nonneg (fun i hi =>
      mul_nonneg (hpositive i) (div_nonneg (hz i) (hx i).le))
  have hsumle : (∑ i, (1 + e i)) ≤ (n : ℝ) * (1 + β) := by
    calc
      (∑ i, (1 + e i)) ≤ ∑ _i : Fin n, (1 + β) :=
        Finset.sum_le_sum (fun i hi => hupper i)
      _ = (n : ℝ) * (1 + β) := by simp; ring
  apply (le_div_iff₀ ht).mpr
  linarith

/-- The central-path gap bound in a reusable feasible-set formulation. -/
theorem primal_central_path_gap
    {n : ℕ} (c x z : Fin n → ℝ) (t : ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (ht : 0 < t) (hx : ∀ i, 0 < x i) (hz : ∀ i, 0 ≤ z i)
    (hzfeas : feasible z)
    (hcentral : PrimalCentralStationarity c x t feasible) :
    karmarkarCost c x - karmarkarCost c z ≤ (n : ℝ) / t :=
  primal_log_barrier_gap c x z t ht hx hz (hcentral z hzfeas)

/-- A fixed multiplicative increase in the barrier parameter. -/
def primalBarrierParameter (t₀ growth : ℝ) (k : ℕ) : ℝ :=
  t₀ * (1 + growth) ^ k

/-- Exact central-path iterates have a geometric primal objective gap under
a multiplicative barrier-parameter schedule. -/
theorem primal_central_path_geometric_rate
    {n : ℕ} (c z : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (t₀ growth : ℝ) (ht₀ : 0 < t₀) (hgrowth : 0 < growth)
    (hz : ∀ i, 0 ≤ z i) (hzfeas : feasible z)
    (hx : ∀ k i, 0 < x k i)
    (hcentral : ∀ k, PrimalCentralStationarity c (x k)
      (primalBarrierParameter t₀ growth k) feasible)
    (k : ℕ) :
    karmarkarCost c (x k) - karmarkarCost c z ≤
      ((n : ℝ) / t₀) * (1 / (1 + growth)) ^ k := by
  have hbase : 0 < 1 + growth := by linarith
  have hpow : 0 < (1 + growth) ^ k := pow_pos hbase _
  have hgap := primal_central_path_gap c (x k) z
    (primalBarrierParameter t₀ growth k) feasible
    (mul_pos ht₀ hpow) (hx k) hz hzfeas (hcentral k)
  calc
    karmarkarCost c (x k) - karmarkarCost c z ≤
        (n : ℝ) / primalBarrierParameter t₀ growth k := hgap
    _ = ((n : ℝ) / t₀) * (1 / (1 + growth)) ^ k := by
      unfold primalBarrierParameter
      rw [one_div, inv_pow]
      field_simp [ne_of_gt ht₀, ne_of_gt hbase]

/-- An explicit logarithmic iteration threshold for the barrier-parameter
schedule. -/
theorem primal_barrier_parameter_accuracy
    {n : ℕ} (hn : 1 ≤ n) (t₀ growth ε : ℝ)
    (ht₀ : 0 < t₀) (hgrowth : 0 < growth) (hε : 0 < ε)
    (k : ℕ)
    (hk : Real.log ((n : ℝ) / (ε * t₀)) ≤
      (k : ℝ) * Real.log (1 + growth)) :
    (n : ℝ) / primalBarrierParameter t₀ growth k ≤ ε := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le (by omega : 0 < 1) hn)
  have hbase : 0 < 1 + growth := by linarith
  have hpow : 0 < (1 + growth) ^ k := pow_pos hbase _
  have hA : 0 < (n : ℝ) / (ε * t₀) :=
    div_pos hnreal (mul_pos hε ht₀)
  have hAle : (n : ℝ) / (ε * t₀) ≤ (1 + growth) ^ k := by
    apply (Real.log_le_log_iff hA hpow).mp
    simpa [Real.log_pow, mul_comm] using hk
  have hmul := (div_le_iff₀ (mul_pos hε ht₀)).mp hAle
  unfold primalBarrierParameter
  apply (div_le_iff₀ (mul_pos ht₀ hpow)).mpr
  nlinarith [hmul]

/-- The same threshold calculation for an arbitrary positive gap constant. -/
theorem primal_barrier_parameter_accuracy_real
    (M t₀ growth ε : ℝ)
    (hM : 0 < M) (ht₀ : 0 < t₀)
    (hgrowth : 0 < growth) (hε : 0 < ε)
    (k : ℕ)
    (hk : Real.log (M / (ε * t₀)) ≤
      (k : ℝ) * Real.log (1 + growth)) :
    M / primalBarrierParameter t₀ growth k ≤ ε := by
  have hbase : 0 < 1 + growth := by linarith
  have hpow : 0 < (1 + growth) ^ k := pow_pos hbase _
  have hA : 0 < M / (ε * t₀) := div_pos hM (mul_pos hε ht₀)
  have hAle : M / (ε * t₀) ≤ (1 + growth) ^ k := by
    apply (Real.log_le_log_iff hA hpow).mp
    simpa [Real.log_pow, mul_comm] using hk
  have hmul := (div_le_iff₀ (mul_pos hε ht₀)).mp hAle
  unfold primalBarrierParameter
  apply (div_le_iff₀ (mul_pos ht₀ hpow)).mpr
  nlinarith [hmul]

/-- Residual-controlled primal iterates retain a logarithmic iteration
threshold, with gap constant `n * (1 + β)`. -/
theorem primal_approx_central_path_accuracy
    {n : ℕ} (hn : 1 ≤ n) (c z : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (t₀ growth β ε : ℝ)
    (ht₀ : 0 < t₀) (hgrowth : 0 < growth)
    (hβnonneg : 0 ≤ β) (hβ : β < 1) (hε : 0 < ε)
    (hz : ∀ i, 0 ≤ z i) (hzfeas : feasible z)
    (hx : ∀ k i, 0 < x k i)
    (hcentral : ∀ k, PrimalApproxCentralStationarity c (x k)
      (primalBarrierParameter t₀ growth k) β feasible)
    (k : ℕ)
    (hk : Real.log (((n : ℝ) * (1 + β)) / (ε * t₀)) ≤
      (k : ℝ) * Real.log (1 + growth)) :
    karmarkarCost c (x k) - karmarkarCost c z ≤ ε := by
  obtain ⟨e, he, hstationary⟩ := hcentral k
  have hbase : 0 < 1 + growth := by linarith
  have hgap := primal_approx_log_barrier_gap c (x k) z e
    (primalBarrierParameter t₀ growth k) β
    (mul_pos ht₀ (pow_pos hbase _)) hβ (hx k) hz he
    (hstationary z hzfeas)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM : 0 < (n : ℝ) * (1 + β) := by positivity
  exact hgap.trans (primal_barrier_parameter_accuracy_real
    ((n : ℝ) * (1 + β)) t₀ growth ε hM ht₀ hgrowth hε k hk)

/-- Exact central-path iterates reach primal accuracy `ε` after the
logarithmic barrier-parameter threshold. -/
theorem primal_central_path_accuracy
    {n : ℕ} (hn : 1 ≤ n) (c z : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (t₀ growth ε : ℝ)
    (ht₀ : 0 < t₀) (hgrowth : 0 < growth) (hε : 0 < ε)
    (hz : ∀ i, 0 ≤ z i) (hzfeas : feasible z)
    (hx : ∀ k i, 0 < x k i)
    (hcentral : ∀ k, PrimalCentralStationarity c (x k)
      (primalBarrierParameter t₀ growth k) feasible)
    (k : ℕ)
    (hk : Real.log ((n : ℝ) / (ε * t₀)) ≤
      (k : ℝ) * Real.log (1 + growth)) :
    karmarkarCost c (x k) - karmarkarCost c z ≤ ε := by
  have hbase : 0 < 1 + growth := by linarith
  have hgap := primal_central_path_gap c (x k) z
    (primalBarrierParameter t₀ growth k) feasible
    (mul_pos ht₀ (pow_pos hbase _)) (hx k) hz hzfeas (hcentral k)
  exact hgap.trans (primal_barrier_parameter_accuracy hn t₀ growth ε
    ht₀ hgrowth hε k hk)

/-- The standard short-step parameter increase has logarithm at least
`1 / (8 √n)`. -/
theorem primal_short_step_log_growth {n : ℕ} (hn : 1 ≤ n) :
    1 / (8 * Real.sqrt (n : ℝ)) ≤
      Real.log (1 + 1 / (4 * Real.sqrt (n : ℝ))) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hnreal
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  let δ : ℝ := 1 / (4 * Real.sqrt (n : ℝ))
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 2 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).mpr
    nlinarith
  have hlog := Real.le_log_one_add_of_nonneg hδpos.le
  have hhalf : δ / 2 ≤ 2 * δ / (δ + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < δ + 2)).mpr
    nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hδle)]
  have heq : δ / 2 = 1 / (8 * Real.sqrt (n : ℝ)) := by
    dsimp [δ]
    field_simp [ne_of_gt hspos]
    ring
  rw [← heq]
  exact hhalf.trans hlog

/-- With the short-step growth factor, a logarithmic number of exact
central-path subproblems suffices for accuracy `ε`. -/
theorem primal_short_step_central_path_accuracy
    {n : ℕ} (hn : 1 ≤ n) (c z : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (t₀ ε : ℝ) (ht₀ : 0 < t₀) (hε : 0 < ε)
    (hz : ∀ i, 0 ≤ z i) (hzfeas : feasible z)
    (hx : ∀ k i, 0 < x k i)
    (hcentral : ∀ k, PrimalCentralStationarity c (x k)
      (primalBarrierParameter t₀
        (1 / (4 * Real.sqrt (n : ℝ))) k) feasible)
    (k : ℕ)
    (hk : 8 * Real.sqrt (n : ℝ) *
      Real.log ((n : ℝ) / (ε * t₀)) ≤ (k : ℝ)) :
    karmarkarCost c (x k) - karmarkarCost c z ≤ ε := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := by
    have hs' : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hnreal
    linarith
  have hden : 0 < 8 * Real.sqrt (n : ℝ) := by positivity
  have hgrowth : 0 < 1 / (4 * Real.sqrt (n : ℝ)) := by positivity
  have hlog := primal_short_step_log_growth hn
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ k by positivity)
  have hthreshold : Real.log ((n : ℝ) / (ε * t₀)) ≤
      (k : ℝ) * Real.log
        (1 + 1 / (4 * Real.sqrt (n : ℝ))) := by
    calc
      Real.log ((n : ℝ) / (ε * t₀)) ≤
          (k : ℝ) / (8 * Real.sqrt (n : ℝ)) := by
        apply (le_div_iff₀ hden).mpr
        nlinarith [hk]
      _ = (k : ℝ) * (1 / (8 * Real.sqrt (n : ℝ))) := by ring
      _ ≤ (k : ℝ) * Real.log
          (1 + 1 / (4 * Real.sqrt (n : ℝ))) := hmul
  exact primal_central_path_accuracy hn c z x feasible t₀
    (1 / (4 * Real.sqrt (n : ℝ))) ε ht₀ hgrowth hε
    hz hzfeas hx hcentral k hthreshold

/-- The short-step iteration threshold for any positive gap constant. -/
theorem primal_short_step_log_threshold
    {n : ℕ} (hn : 1 ≤ n) (M t₀ ε : ℝ) (k : ℕ)
    (hk : 8 * Real.sqrt (n : ℝ) *
      Real.log (M / (ε * t₀)) ≤ (k : ℝ)) :
    Real.log (M / (ε * t₀)) ≤
      (k : ℝ) * Real.log
        (1 + 1 / (4 * Real.sqrt (n : ℝ))) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := by
    have hs' : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hnreal
    linarith
  have hden : 0 < 8 * Real.sqrt (n : ℝ) := by positivity
  have hlog := primal_short_step_log_growth hn
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ k by positivity)
  calc
    Real.log (M / (ε * t₀)) ≤
        (k : ℝ) / (8 * Real.sqrt (n : ℝ)) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [hk]
    _ = (k : ℝ) * (1 / (8 * Real.sqrt (n : ℝ))) := by ring
    _ ≤ (k : ℝ) * Real.log
        (1 + 1 / (4 * Real.sqrt (n : ℝ))) := hmul

/-- Residual-controlled short-step iterates have the same
`O(√n log(n/(ε t₀)))` iteration threshold. -/
theorem primal_short_step_approx_accuracy
    {n : ℕ} (hn : 1 ≤ n) (c z : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (t₀ β ε : ℝ) (ht₀ : 0 < t₀)
    (hβnonneg : 0 ≤ β) (hβ : β < 1) (hε : 0 < ε)
    (hz : ∀ i, 0 ≤ z i) (hzfeas : feasible z)
    (hx : ∀ k i, 0 < x k i)
    (hcentral : ∀ k, PrimalApproxCentralStationarity c (x k)
      (primalBarrierParameter t₀
        (1 / (4 * Real.sqrt (n : ℝ))) k) β feasible)
    (k : ℕ)
    (hk : 8 * Real.sqrt (n : ℝ) *
      Real.log (((n : ℝ) * (1 + β)) / (ε * t₀)) ≤ (k : ℝ)) :
    karmarkarCost c (x k) - karmarkarCost c z ≤ ε := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := by
    have hs' : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hnreal
    linarith
  have hgrowth : 0 < 1 / (4 * Real.sqrt (n : ℝ)) := by positivity
  exact primal_approx_central_path_accuracy hn c z x feasible t₀
    (1 / (4 * Real.sqrt (n : ℝ))) β ε ht₀ hgrowth
    hβnonneg hβ hε hz hzfeas hx hcentral k
    (primal_short_step_log_threshold hn ((n : ℝ) * (1 + β)) t₀ ε k hk)

/-- The smaller update used by a Newton short-step method has logarithmic
growth at least `1 / (32 √n)`. -/
theorem primal_newton_short_step_log_growth {n : ℕ} (hn : 1 ≤ n) :
    1 / (32 * Real.sqrt (n : ℝ)) ≤
      Real.log (1 + 1 / (16 * Real.sqrt (n : ℝ))) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hnreal
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  let δ : ℝ := 1 / (16 * Real.sqrt (n : ℝ))
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 2 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 16 * Real.sqrt (n : ℝ))).mpr
    nlinarith
  have hlog := Real.le_log_one_add_of_nonneg hδpos.le
  have hhalf : δ / 2 ≤ 2 * δ / (δ + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < δ + 2)).mpr
    nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hδle)]
  have heq : δ / 2 = 1 / (32 * Real.sqrt (n : ℝ)) := by
    dsimp [δ]
    field_simp [ne_of_gt hspos]
    ring
  rw [← heq]
  exact hhalf.trans hlog

/-- Conditional complexity bound for approximately centered iterates using
the Newton-compatible parameter growth `1 + 1/(16√n)`. -/
theorem primal_newton_short_step_approx_accuracy
    {n : ℕ} (hn : 1 ≤ n) (c z : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (t₀ β ε : ℝ) (ht₀ : 0 < t₀)
    (hβnonneg : 0 ≤ β) (hβ : β < 1) (hε : 0 < ε)
    (hz : ∀ i, 0 ≤ z i) (hzfeas : feasible z)
    (hx : ∀ k i, 0 < x k i)
    (hcentral : ∀ k, PrimalApproxCentralStationarity c (x k)
      (primalBarrierParameter t₀
        (1 / (16 * Real.sqrt (n : ℝ))) k) β feasible)
    (k : ℕ)
    (hk : 32 * Real.sqrt (n : ℝ) *
      Real.log (((n : ℝ) * (1 + β)) / (ε * t₀)) ≤ (k : ℝ)) :
    karmarkarCost c (x k) - karmarkarCost c z ≤ ε := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := by
    have hs' : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hnreal
    linarith
  have hden : 0 < 32 * Real.sqrt (n : ℝ) := by positivity
  have hgrowth : 0 < 1 / (16 * Real.sqrt (n : ℝ)) := by positivity
  have hlog := primal_newton_short_step_log_growth hn
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ k by positivity)
  have hthreshold : Real.log (((n : ℝ) * (1 + β)) / (ε * t₀)) ≤
      (k : ℝ) * Real.log
        (1 + 1 / (16 * Real.sqrt (n : ℝ))) := by
    calc
      Real.log (((n : ℝ) * (1 + β)) / (ε * t₀)) ≤
          (k : ℝ) / (32 * Real.sqrt (n : ℝ)) := by
        apply (le_div_iff₀ hden).mpr
        nlinarith [hk]
      _ = (k : ℝ) * (1 / (32 * Real.sqrt (n : ℝ))) := by ring
      _ ≤ (k : ℝ) * Real.log
          (1 + 1 / (16 * Real.sqrt (n : ℝ))) := hmul
  exact primal_approx_central_path_accuracy hn c z x feasible t₀
    (1 / (16 * Real.sqrt (n : ℝ))) β ε ht₀ hgrowth
    hβnonneg hβ hε hz hzfeas hx hcentral k hthreshold

end QuasiNewtonConvergence

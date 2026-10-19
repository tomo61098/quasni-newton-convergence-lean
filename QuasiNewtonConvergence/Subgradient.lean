module

public import QuasiNewtonConvergence.DiminishingGradientDescent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

@[expose] public section

/-!
# Subgradient descent for convex objectives

The method may use any selected subgradient at each iterate. With bounded
subgradients and diminishing steps, the best objective value approaches the
minimum. This does not claim convergence of every iterate.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsSubgradient (f : E → ℝ) (x g : E) : Prop :=
  ∀ y, f y ≥ f x + inner ℝ g (y - x)

/-- One subgradient step has a squared-distance error proportional to `α²G²`. -/
theorem subgradient_step_potential (f : E → ℝ) (x minimizer g : E)
    (α G : ℝ) (hα : 0 ≤ α) (hG : 0 ≤ G)
    (hsub : IsSubgradient f x g) (hbound : ‖g‖ ≤ G) :
    2 * α * (f x - f minimizer) ≤
      ‖x - minimizer‖ ^ 2 -
        ‖gradientStepSize (fun _ => g) α x - minimizer‖ ^ 2 +
          α ^ 2 * G ^ 2 := by
  have hinner : f x - f minimizer ≤ inner ℝ g (x - minimizer) := by
    have h := hsub minimizer
    have heq : minimizer - x = -(x - minimizer) := by abel
    rw [heq, inner_neg_right] at h
    linarith
  have hnorm : ‖g‖ ^ 2 ≤ G ^ 2 := by nlinarith [norm_nonneg g]
  have hdist : ‖gradientStepSize (fun _ => g) α x - minimizer‖ ^ 2 =
      ‖x - minimizer‖ ^ 2 - 2 * α * inner ℝ g (x - minimizer) +
        α ^ 2 * ‖g‖ ^ 2 := by
    have heq : gradientStepSize (fun _ => g) α x - minimizer =
        (x - minimizer) + -(α • g) := by
      simp [gradientStepSize, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [heq, norm_add_sq_real, inner_neg_right, real_inner_smul_right,
      real_inner_comm (x - minimizer) g,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow]
    rw [sq_abs]
    ring
  have hmul := mul_le_mul_of_nonneg_left hinner
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hα)
  have hGmul := mul_le_mul_of_nonneg_left hnorm (sq_nonneg α)
  nlinarith

/-- The standard weighted objective-gap bound after `n` subgradient steps. -/
theorem subgradient_weighted_gap_bound (f : E → ℝ) (x g : ℕ → E)
    (minimizer : E) (α : ℕ → ℝ) (G : ℝ)
    (hα : ∀ k, 0 ≤ α k) (hG : 0 ≤ G)
    (hsub : ∀ k, IsSubgradient f (x k) (g k))
    (hbound : ∀ k, ‖g k‖ ≤ G)
    (hstep : ∀ k, x (k + 1) = gradientStepSize (fun _ => g k) (α k) (x k))
    (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, α k * (f (x k) - f minimizer)) ≤
      ‖x 0 - minimizer‖ ^ 2 +
        G ^ 2 * (∑ k ∈ Finset.range n, α k ^ 2) := by
  have hpot (n : ℕ) :
      2 * (∑ k ∈ Finset.range n, α k * (f (x k) - f minimizer)) +
        ‖x n - minimizer‖ ^ 2 ≤
          ‖x 0 - minimizer‖ ^ 2 +
            G ^ 2 * (∑ k ∈ Finset.range n, α k ^ 2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := subgradient_step_potential f (x n) minimizer (g n)
        (α n) G (hα n) hG (hsub n) (hbound n)
      rw [← hstep n] at hs
      simp only [Finset.sum_range_succ]
      nlinarith
  have h := hpot n
  nlinarith [sq_nonneg ‖x n - minimizer‖]

/-- When total step length diverges but squared steps are negligible relative
to it, some iterate among the first `n` is eventually arbitrarily optimal. -/
theorem subgradient_best_eventually (f : E → ℝ) (x g : ℕ → E)
    (minimizer : E) (α : ℕ → ℝ) (G : ℝ)
    (hα : ∀ k, 0 ≤ α k) (hG : 0 ≤ G)
    (hsub : ∀ k, IsSubgradient f (x k) (g k))
    (hbound : ∀ k, ‖g k‖ ≤ G)
    (hstep : ∀ k, x (k + 1) = gradientStepSize (fun _ => g k) (α k) (x k))
    (hdiv : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, α k)
      Filter.atTop Filter.atTop)
    (hratio : Filter.Tendsto (fun n =>
      (∑ k ∈ Finset.range n, α k ^ 2) /
        (∑ k ∈ Finset.range n, α k)) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ k < n, f (x k) - f minimizer < ε := by
  intro ε hε
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, α k
  let Q : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, α k ^ 2
  let D : ℝ := ‖x 0 - minimizer‖ ^ 2
  have hSpos : ∀ᶠ n in Filter.atTop, 0 < S n :=
    hdiv.eventually (Filter.eventually_gt_atTop 0)
  have herror : Filter.Tendsto (fun n => D / S n + G ^ 2 * (Q n / S n))
      Filter.atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hdiv
    have hfirst : Filter.Tendsto (fun n => D / S n) Filter.atTop (nhds 0) := by
      simpa [D, S, div_eq_mul_inv, Function.comp_def] using hinv.const_mul D
    have hsecond : Filter.Tendsto (fun n => G ^ 2 * (Q n / S n))
        Filter.atTop (nhds 0) := by
      simpa [Q, S] using hratio.const_mul (G ^ 2)
    simpa using hfirst.add hsecond
  have hevent : ∀ᶠ n in Filter.atTop,
      D / S n + G ^ 2 * (Q n / S n) < 2 * ε :=
    herror.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hSpos, hevent] with n hn he
  by_contra hnone
  have hall (k : ℕ) (hk : k < n) : ε ≤ f (x k) - f minimizer :=
    le_of_not_gt (fun h => hnone ⟨k, hk, h⟩)
  have hsum : ε * S n ≤
      ∑ k ∈ Finset.range n, α k * (f (x k) - f minimizer) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    calc
      ε * α k = α k * ε := by ring
      _ ≤ α k * (f (x k) - f minimizer) :=
        mul_le_mul_of_nonneg_left (hall k (Finset.mem_range.mp hk)) (hα k)
  have hb := subgradient_weighted_gap_bound f x g minimizer α G
    hα hG hsub hbound hstep n
  have hscaled : 2 * ε ≤ D / S n + G ^ 2 * (Q n / S n) := by
    calc
      2 * ε ≤ (D + G ^ 2 * Q n) / S n := by
        apply (le_div_iff₀ hn).2
        dsimp [D, Q, S] at hb ⊢
        nlinarith
      _ = D / S n + G ^ 2 * (Q n / S n) := by ring
  linarith

/-- For `αₖ = 1/√(k+1)`, the accumulated squared steps are negligible
relative to the accumulated steps. -/
theorem sqrtStepSize_square_sum_ratio_tendsto_zero :
    Filter.Tendsto (fun n =>
      (∑ k ∈ Finset.range n, sqrtStepSize k ^ 2) /
        (∑ k ∈ Finset.range n, sqrtStepSize k))
      Filter.atTop (nhds 0) := by
  have hsmall : (fun k => sqrtStepSize k ^ 2) =o[Filter.atTop]
      sqrtStepSize := by
    apply (Asymptotics.isLittleO_iff_tendsto
      (fun k hk => by simp [hk])).2
    convert sqrtStepSize_tendsto_zero using 1
    ext k
    have hk : sqrtStepSize k ≠ 0 := ne_of_gt (sqrtStepSize_pos k)
    field_simp
  exact (hsmall.sum_range (fun k => (sqrtStepSize_pos k).le)
    sqrtStepSize_sum_diverges).tendsto_div_nhds_zero

/-- With bounded subgradients and square-root step lengths, the best objective
value among the first `n` iterates tends to the minimum. The statement uses
the equivalent eventual ε characterization. -/
theorem subgradient_sqrt_best_eventually (f : E → ℝ) (x g : ℕ → E)
    (minimizer : E) (G : ℝ) (hG : 0 ≤ G)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hsub : ∀ k, IsSubgradient f (x k) (g k))
    (hbound : ∀ k, ‖g k‖ ≤ G)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize (fun _ => g k) (sqrtStepSize k) (x k)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ k < n,
        0 ≤ f (x k) - f minimizer ∧ f (x k) - f minimizer < ε := by
  intro ε hε
  have hh := subgradient_best_eventually f x g minimizer sqrtStepSize G
    (fun k => (sqrtStepSize_pos k).le) hG hsub hbound hstep
    sqrtStepSize_sum_diverges sqrtStepSize_square_sum_ratio_tendsto_zero
    ε hε
  filter_upwards [hh] with n ⟨k, hk, hgap⟩
  exact ⟨k, hk, sub_nonneg.mpr (hmin (x k)), hgap⟩

/-- A scalar decay lemma for nonsummable steps whose sizes tend to zero. -/
private theorem scalar_subgradient_decay (e α : ℕ → ℝ) (c B : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B)
    (he : ∀ k, 0 ≤ e k) (hα : ∀ k, 0 ≤ α k)
    (hzero : Filter.Tendsto α Filter.atTop (nhds 0))
    (htail : ∀ K, Filter.Tendsto (fun n =>
      ∑ j ∈ Finset.range n, α (K + j)) Filter.atTop Filter.atTop)
    (hrec : ∀ k, e (k + 1) ≤ e k - c * α k * e k + B * α k ^ 2) :
    Filter.Tendsto e Filter.atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun k => lt_of_lt_of_le ha (he k))
  · intro a ha
    let ε : ℝ := a / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hδ : 0 < c * ε / 2 := by positivity
    have hsmallB : ∀ᶠ k in Filter.atTop, B * α k < c * ε / 2 := by
      have h := hzero.const_mul B
      simpa using h.eventually (eventually_lt_nhds (by simpa using hδ))
    have hsmallC : ∀ᶠ k in Filter.atTop, c * α k < 1 := by
      have h := hzero.const_mul c
      simpa using h.eventually (eventually_lt_nhds (by norm_num : c * (0 : ℝ) < 1))
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (hsmallB.and hsmallC)
    have hdrop (k : ℕ) (hk : K ≤ k) (hlarge : ε ≤ e k) :
        e (k + 1) + (c * ε / 2) * α k ≤ e k := by
      have hs := (hK k hk).1
      have hsq : B * α k ^ 2 ≤ (c * ε / 2) * α k := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs.le) (hα k)]
      have hprod : c * α k * ε ≤ c * α k * e k :=
        mul_le_mul_of_nonneg_left hlarge (mul_nonneg hc.le (hα k))
      nlinarith [hrec k]
    have hcross : ∃ N, K ≤ N ∧ e N < ε := by
      by_contra hnone
      have hlarge (n : ℕ) : ε ≤ e (K + n) :=
        le_of_not_gt (fun h => hnone ⟨K + n, Nat.le_add_right K n, h⟩)
      have htel (n : ℕ) :
          e (K + n) + (c * ε / 2) *
            (∑ j ∈ Finset.range n, α (K + j)) ≤ e K := by
        induction n with
        | zero => simp
        | succ n ih =>
          have hd := hdrop (K + n) (Nat.le_add_right K n) (hlarge n)
          simp only [Finset.sum_range_succ, Nat.add_succ]
          nlinarith [hd, ih]
      have hbig : ∀ᶠ n in Filter.atTop,
          e K / (c * ε / 2) < ∑ j ∈ Finset.range n, α (K + j) :=
        (htail K).eventually (Filter.eventually_gt_atTop _)
      obtain ⟨n, hn⟩ := hbig.exists
      have h := htel n
      have hh := mul_lt_mul_of_pos_left hn hδ
      have hcancel : (c * ε / 2) * (e K / (c * ε / 2)) = e K :=
        mul_div_cancel₀ _ (ne_of_gt hδ)
      nlinarith [he (K + n)]
    obtain ⟨N, hNK, hN⟩ := hcross
    have hstay (n : ℕ) : e (N + n) ≤ ε := by
      induction n with
      | zero => simpa using hN.le
      | succ n ih =>
        have hk : K ≤ N + n := le_trans hNK (Nat.le_add_right N n)
        have hsB := (hK (N + n) hk).1
        have hsC := (hK (N + n) hk).2
        have hcoef : 0 ≤ 1 - c * α (N + n) := by linarith
        have hmul := mul_le_mul_of_nonneg_left ih hcoef
        have hsq : B * α (N + n) ^ 2 ≤
            (c * ε / 2) * α (N + n) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hsB.le) (hα (N + n))]
        have hr := hrec (N + n)
        simp only [Nat.add_succ]
        nlinarith [hmul, hsq, hr, mul_nonneg hc.le (hα (N + n))]
    apply Filter.eventually_atTop.2
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hstay (n - N)
    have heq : N + (n - N) = n := Nat.add_sub_of_le hn
    rw [heq] at hh
    exact lt_of_le_of_lt hh (by dsimp [ε]; linarith)

/-- A subgradient inequality with the quadratic term of strong convexity. -/
def IsStrongSubgradient (f : E → ℝ) (μ : ℝ) (x g : E) : Prop :=
  ∀ y, f y ≥ f x + inner ℝ g (y - x) + (μ / 2) * ‖y - x‖ ^ 2

/-- Strong convexity gives a contraction in squared distance, up to the
quadratic step error. -/
theorem strong_subgradient_step_bound (f : E → ℝ) (x minimizer g : E)
    (α G μ : ℝ) (hα : 0 ≤ α) (hG : 0 ≤ G)
    (hmin : f minimizer ≤ f x)
    (hstrong : IsStrongSubgradient f μ x g) (hbound : ‖g‖ ≤ G) :
    ‖gradientStepSize (fun _ => g) α x - minimizer‖ ^ 2 ≤
      (1 - μ * α) * ‖x - minimizer‖ ^ 2 + G ^ 2 * α ^ 2 := by
  have hinner : μ * ‖x - minimizer‖ ^ 2 ≤
      2 * inner ℝ g (x - minimizer) := by
    have h := hstrong minimizer
    have heq : minimizer - x = -(x - minimizer) := by abel
    rw [heq, inner_neg_right, norm_neg] at h
    nlinarith
  have hnorm : ‖g‖ ^ 2 ≤ G ^ 2 := by nlinarith [norm_nonneg g]
  have hdist : ‖gradientStepSize (fun _ => g) α x - minimizer‖ ^ 2 =
      ‖x - minimizer‖ ^ 2 - 2 * α * inner ℝ g (x - minimizer) +
        α ^ 2 * ‖g‖ ^ 2 := by
    have heq : gradientStepSize (fun _ => g) α x - minimizer =
        (x - minimizer) + -(α • g) := by
      simp [gradientStepSize, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [heq, norm_add_sq_real, inner_neg_right, real_inner_smul_right,
      real_inner_comm (x - minimizer) g,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow]
    rw [sq_abs]
    ring
  have hmul := mul_le_mul_of_nonneg_left hinner hα
  have hGmul := mul_le_mul_of_nonneg_left hnorm (sq_nonneg α)
  nlinarith

/-- Bounded strong subgradients and `1/√(k+1)` steps make all iterates
converge to the minimizer. No differentiability or smoothness is assumed. -/
theorem subgradient_sqrt_strong_iterates_tendsto
    (f : E → ℝ) (x g : ℕ → E) (minimizer : E) (G μ : ℝ)
    (hG : 0 ≤ G) (hμ : 0 < μ)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hstrong : ∀ k, IsStrongSubgradient f μ (x k) (g k))
    (hbound : ∀ k, ‖g k‖ ≤ G)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize (fun _ => g k) (sqrtStepSize k) (x k)) :
    Filter.Tendsto x Filter.atTop (nhds minimizer) := by
  have hrec (k : ℕ) :
      ‖x (k + 1) - minimizer‖ ^ 2 ≤
        ‖x k - minimizer‖ ^ 2 -
          μ * sqrtStepSize k * ‖x k - minimizer‖ ^ 2 +
            G ^ 2 * sqrtStepSize k ^ 2 := by
    rw [hstep k]
    have h := strong_subgradient_step_bound f (x k) minimizer (g k)
      (sqrtStepSize k) G μ (sqrtStepSize_pos k).le hG
      (hmin (x k)) (hstrong k) (hbound k)
    nlinarith
  have hsq : Filter.Tendsto (fun k => ‖x k - minimizer‖ ^ 2)
      Filter.atTop (nhds 0) :=
    scalar_subgradient_decay (fun k => ‖x k - minimizer‖ ^ 2)
      sqrtStepSize μ (G ^ 2) hμ (sq_nonneg G)
      (fun k => sq_nonneg _) (fun k => (sqrtStepSize_pos k).le)
      sqrtStepSize_tendsto_zero sqrtStepSize_tail_sum_diverges hrec
  have hnorm : Filter.Tendsto (fun k => ‖x k - minimizer‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Under the same assumptions, the objective values converge as well. -/
theorem subgradient_sqrt_strong_values_tendsto
    (f : E → ℝ) (x g : ℕ → E) (minimizer : E) (G μ : ℝ)
    (hG : 0 ≤ G) (hμ : 0 < μ)
    (hmin : ∀ y, f minimizer ≤ f y)
    (hstrong : ∀ k, IsStrongSubgradient f μ (x k) (g k))
    (hbound : ∀ k, ‖g k‖ ≤ G)
    (hstep : ∀ k, x (k + 1) =
      gradientStepSize (fun _ => g k) (sqrtStepSize k) (x k)) :
    Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds (f minimizer)) := by
  have hx := subgradient_sqrt_strong_iterates_tendsto f x g minimizer G μ
    hG hμ hmin hstrong hbound hstep
  have hnorm : Filter.Tendsto (fun k => ‖x k - minimizer‖)
      Filter.atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hgap : Filter.Tendsto (fun k => f (x k) - f minimizer)
      Filter.atTop (nhds 0) := by
    have hupper : Filter.Tendsto (fun k => G * ‖x k - minimizer‖)
        Filter.atTop (nhds 0) := by simpa using hnorm.const_mul G
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; exact sub_nonneg.mpr (hmin (x k))
    · intro k
      have hs := hstrong k minimizer
      have heq : minimizer - x k = -(x k - minimizer) := by abel
      rw [heq, inner_neg_right, norm_neg] at hs
      have hinner := real_inner_le_norm (g k) (x k - minimizer)
      have hprod := mul_le_mul_of_nonneg_right (hbound k)
        (norm_nonneg (x k - minimizer))
      have hquad : 0 ≤ (μ / 2) * ‖x k - minimizer‖ ^ 2 := by positivity
      nlinarith
  have hval := hgap.add_const (f minimizer)
  simpa only [sub_add_cancel, zero_add] using hval

end QuasiNewtonConvergence

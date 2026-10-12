import QuasiNewtonConvergence.DennisMoreProximal
import QuasiNewtonConvergence.BFGSGlobal
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The dissipative part of the Nocedal–Wright BFGS argument

Theorem 6.6 uses a nonnegative trace–logdet potential. Its change is bounded
by a summable secant error minus two nonnegative geometric defects. The
telescoping argument below proves that each defect vanishes. The finite-
dimensional determinant identity needed to establish this potential inequality
for `bfgsUpdateMap` is a separate, currently missing step.
-/

noncomputable section

namespace QuasiNewtonConvergence

open Filter

/-- The exact scalar form of Nocedal–Wright (6.50). The trace and determinant
equalities are deliberately explicit inputs; this result does not assume
the matrix determinant formula for `bfgsUpdateMap`. -/
theorem bfgs_scalar_potential_identity
    (T Tnext D Dnext a q cosine M : ℝ)
    (hD : 0 < D) (ha : 0 < a) (hq : 0 < q) (hc : 0 < cosine)
    (htrace : Tnext = T - q / cosine ^ 2 + M)
    (hdet : Dnext = D * a / q) :
    Tnext - Real.log Dnext + (-Real.log (cosine ^ 2)) +
        (q / cosine ^ 2 - 1 - Real.log (q / cosine ^ 2)) =
      T - Real.log D + (M - Real.log a - 1) := by
  have hc2 : 0 < cosine ^ 2 := sq_pos_of_pos hc
  have hlogdet : Real.log Dnext = Real.log D + Real.log a - Real.log q := by
    rw [hdet, Real.log_div (mul_ne_zero (ne_of_gt hD) (ne_of_gt ha))
      (ne_of_gt hq), Real.log_mul (ne_of_gt hD) (ne_of_gt ha)]
  have hqsplit : Real.log q =
      Real.log (q / cosine ^ 2) + Real.log (cosine ^ 2) := by
    have heq : q = q / cosine ^ 2 * cosine ^ 2 := by field_simp
    calc
      Real.log q = Real.log (q / cosine ^ 2 * cosine ^ 2) := congrArg Real.log heq
      _ = _ := Real.log_mul (ne_of_gt (div_pos hq hc2)) (ne_of_gt hc2)
  rw [htrace, hlogdet, hqsplit]
  ring

/-- The two defects in (6.60) are nonnegative, and the scalar potential
decreases by their sum up to the secant error. -/
theorem bfgs_scalar_potential_dissipation
    (T Tnext D Dnext a q cosine M error : ℝ)
    (hD : 0 < D) (ha : 0 < a) (hq : 0 < q)
    (hc : 0 < cosine) (hc_le : cosine ≤ 1)
    (htrace : Tnext = T - q / cosine ^ 2 + M)
    (hdet : Dnext = D * a / q)
    (herror : M - Real.log a - 1 ≤ error) :
    0 ≤ -Real.log (cosine ^ 2) ∧
    0 ≤ q / cosine ^ 2 - 1 - Real.log (q / cosine ^ 2) ∧
    (Tnext - Real.log Dnext) + (-Real.log (cosine ^ 2)) +
        (q / cosine ^ 2 - 1 - Real.log (q / cosine ^ 2)) ≤
      (T - Real.log D) + error := by
  have hc2 : cosine ^ 2 ≤ 1 := by nlinarith [sq_nonneg (cosine - 1)]
  have hangle := Real.log_nonpos (le_of_lt (sq_pos_of_pos hc)) hc2
  have hradial := Real.log_le_sub_one_of_pos
    (div_pos hq (sq_pos_of_pos hc))
  have hid := bfgs_scalar_potential_identity T Tnext D Dnext a q cosine M
    hD ha hq hc htrace hdet
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- A lower-bounded potential with summable errors has summable dissipation.
This is the telescoping step in the proof of Nocedal–Wright, Theorem 6.6. -/
theorem bfgs_potential_dissipation_summable
    (potential error defect : ℕ → ℝ)
    (hpot : ∀ k, 0 ≤ potential k)
    (herr : ∀ k, 0 ≤ error k)
    (hdef : ∀ k, 0 ≤ defect k)
    (hsum : Summable error)
    (hstep : ∀ k, potential (k + 1) + defect k ≤
      potential k + error k) :
    Summable defect := by
  have htel : ∀ n, (∑ k ∈ Finset.range n, defect k) + potential n ≤
      potential 0 + ∑ k ∈ Finset.range n, error k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      linarith [hstep n]
  apply summable_of_sum_range_le (c := potential 0 + ∑' k, error k) hdef
  intro n
  have herrsum : (∑ k ∈ Finset.range n, error k) ≤ ∑' k, error k :=
    hsum.sum_le_tsum (Finset.range n) (fun k _ => herr k)
  linarith [htel n, hpot n]

/-- Both geometric defects in the BFGS trace–logdet recurrence vanish. -/
theorem bfgs_potential_defects_tendsto_zero
    (potential error angle radial : ℕ → ℝ)
    (hpot : ∀ k, 0 ≤ potential k)
    (herr : ∀ k, 0 ≤ error k)
    (hangle : ∀ k, 0 ≤ angle k)
    (hradial : ∀ k, 0 ≤ radial k)
    (hsum : Summable error)
    (hstep : ∀ k, potential (k + 1) + angle k + radial k ≤
      potential k + error k) :
    Tendsto angle atTop (nhds 0) ∧ Tendsto radial atTop (nhds 0) := by
  have hdef : Summable (fun k => angle k + radial k) :=
    bfgs_potential_dissipation_summable potential error
      (fun k => angle k + radial k) hpot herr
      (fun k => add_nonneg (hangle k) (hradial k)) hsum (by
        intro k
        simpa only [add_assoc] using hstep k)
  have ha : Summable angle :=
    Summable.of_nonneg_of_le hangle
      (fun k => le_add_of_nonneg_right (hradial k)) hdef
  have hr : Summable radial :=
    Summable.of_nonneg_of_le hradial
      (fun k => le_add_of_nonneg_left (hangle k)) hdef
  exact ⟨ha.tendsto_atTop_zero, hr.tendsto_atTop_zero⟩

/-- The indexed scalar trace and determinant formulas imply the two limits
in Nocedal–Wright (6.61), expressed as vanishing defects. The formulas are
the exact point where the finite-dimensional BFGS update must be connected. -/
theorem bfgs_scalar_trace_det_defects_tendsto_zero
    (trace determinant m M q cosine error : ℕ → ℝ)
    (hD : ∀ k, 0 < determinant k)
    (ha : ∀ k, 0 < m k)
    (hq : ∀ k, 0 < q k)
    (hc : ∀ k, 0 < cosine k)
    (hc_le : ∀ k, cosine k ≤ 1)
    (hpot : ∀ k, 0 ≤ trace k - Real.log (determinant k))
    (herr : ∀ k, 0 ≤ error k)
    (hsum : Summable error)
    (htrace : ∀ k, trace (k + 1) =
      trace k - q k / cosine k ^ 2 + M k)
    (hdet : ∀ k, determinant (k + 1) =
      determinant k * m k / q k)
    (herror : ∀ k, M k - Real.log (m k) - 1 ≤ error k) :
    Tendsto (fun k => -Real.log (cosine k ^ 2)) atTop (nhds 0) ∧
    Tendsto (fun k => q k / cosine k ^ 2 - 1 -
      Real.log (q k / cosine k ^ 2)) atTop (nhds 0) := by
  let angle : ℕ → ℝ := fun k => -Real.log (cosine k ^ 2)
  let radial : ℕ → ℝ := fun k =>
    q k / cosine k ^ 2 - 1 - Real.log (q k / cosine k ^ 2)
  have hscalar : ∀ k, 0 ≤ angle k ∧ 0 ≤ radial k ∧
      (trace (k + 1) - Real.log (determinant (k + 1))) +
          angle k + radial k ≤
        (trace k - Real.log (determinant k)) + error k := by
    intro k
    exact bfgs_scalar_potential_dissipation
      (trace k) (trace (k + 1)) (determinant k) (determinant (k + 1))
      (m k) (q k) (cosine k) (M k) (error k)
      (hD k) (ha k) (hq k) (hc k) (hc_le k)
      (htrace k) (hdet k) (herror k)
  exact bfgs_potential_defects_tendsto_zero
    (fun k => trace k - Real.log (determinant k)) error angle radial
    hpot herr (fun k => (hscalar k).1) (fun k => (hscalar k).2.1)
    hsum (fun k => (hscalar k).2.2)

/-- The final algebraic step of Nocedal–Wright (6.61): once the two
dimensionless geometric ratios tend to one, the normalized directional
error tends to zero. -/
theorem bfgs_geometric_error_tendsto_zero
    (q angleSq error : ℕ → ℝ)
    (hq : Tendsto q atTop (nhds 1))
    (hangle : Tendsto angleSq atTop (nhds 1))
    (hnonneg : ∀ k, 0 ≤ error k)
    (hidentity : ∀ k, error k ^ 2 =
      q k ^ 2 / angleSq k - 2 * q k + 1) :
    Tendsto error atTop (nhds 0) := by
  have hsq : Tendsto (fun k => error k ^ 2) atTop (nhds 0) := by
    have hquot : Tendsto (fun k => q k ^ 2 / angleSq k)
        atTop (nhds (1 : ℝ)) := by
      convert (hq.pow 2).div hangle (by norm_num : (1 : ℝ) ≠ 0) using 1
      norm_num
    have hformula : Tendsto
        (fun k => q k ^ 2 / angleSq k - 2 * q k + 1)
        atTop (nhds (0 : ℝ)) := by
      convert (hquot.sub (tendsto_const_nhds.mul hq)).add
        tendsto_const_nhds using 1
      norm_num
    exact hformula.congr' (Filter.Eventually.of_forall
      (fun k => (hidentity k).symm))
  have hsqrt := Real.continuous_sqrt.tendsto 0 |>.comp hsq
  have heq : (fun k => Real.sqrt (error k ^ 2)) = error := by
    funext k
    exact Real.sqrt_sq_eq_abs (error k) |>.trans (abs_of_nonneg (hnonneg k))
  have hsqrt' : Tendsto (fun k => Real.sqrt (error k ^ 2))
      atTop (nhds 0) := by simpa only [Real.sqrt_zero, Function.comp_def] using hsqrt
  rwa [heq] at hsqrt'

/-- The radial defect has a unique zero at one. The quantitative bound
`(√t - 1)² ≤ t - 1 - log t` proves the needed inverse limit without a
compactness argument. -/
theorem bfgs_radial_defect_tendsto_one
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (hdef : Tendsto (fun k => t k - 1 - Real.log (t k)) atTop (nhds 0)) :
    Tendsto t atTop (nhds 1) := by
  have hbound : ∀ k, (Real.sqrt (t k) - 1) ^ 2 ≤
      t k - 1 - Real.log (t k) := by
    intro k
    have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (ht k))
    rw [Real.log_sqrt (le_of_lt (ht k))] at hlog
    nlinarith [Real.sq_sqrt (le_of_lt (ht k))]
  have hsq : Tendsto (fun k => (Real.sqrt (t k) - 1) ^ 2)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdef
      (fun k => sq_nonneg _) hbound
  have habs : Tendsto (fun k => |Real.sqrt (t k) - 1|)
      atTop (nhds 0) := by
    have h := Real.continuous_sqrt.tendsto 0 |>.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h
  have hrootdiff : Tendsto (fun k => Real.sqrt (t k) - 1)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  have hroot : Tendsto (fun k => Real.sqrt (t k)) atTop (nhds 1) := by
    convert hrootdiff.add_const 1 using 1 <;> norm_num
  have hpow := hroot.pow 2
  convert hpow using 1
  · ext k
    exact (Real.sq_sqrt (le_of_lt (ht k))).symm
  · norm_num

/-- The two vanishing defects imply the normalized Dennis–Moré error,
provided the standard squared-error identity (6.47) holds. -/
theorem bfgs_defects_imply_directional_error
    (q angleSq error : ℕ → ℝ)
    (hq : ∀ k, 0 < q k)
    (hanglePos : ∀ k, 0 < angleSq k)
    (hangle : Tendsto (fun k => -Real.log (angleSq k)) atTop (nhds 0))
    (hradial : Tendsto (fun k => q k / angleSq k - 1 -
      Real.log (q k / angleSq k)) atTop (nhds 0))
    (hnonneg : ∀ k, 0 ≤ error k)
    (hidentity : ∀ k, error k ^ 2 =
      q k ^ 2 / angleSq k - 2 * q k + 1) :
    Tendsto error atTop (nhds 0) := by
  have hlog : Tendsto (fun k => Real.log (angleSq k)) atTop (nhds 0) := by
    convert hangle.neg using 1 <;> norm_num
  have hangleOne : Tendsto angleSq atTop (nhds 1) := by
    have hexp := Real.continuous_exp.tendsto 0 |>.comp hlog
    convert hexp using 1
    · ext k
      exact (Real.exp_log (hanglePos k)).symm
    · norm_num
  have hratio : Tendsto (fun k => q k / angleSq k) atTop (nhds 1) :=
    bfgs_radial_defect_tendsto_one (fun k => q k / angleSq k)
      (fun k => div_pos (hq k) (hanglePos k)) hradial
  have hqOne : Tendsto q atTop (nhds 1) := by
    have hmul := hratio.mul hangleOne
    convert hmul using 1
    · ext k
      exact (div_mul_cancel₀ (q k) (ne_of_gt (hanglePos k))).symm
    · norm_num
  exact bfgs_geometric_error_tendsto_zero q angleSq error
    hqOne hangleOne hnonneg hidentity

/-- Scalar form of the BFGS-to-Dennis–Moré implication. The input identities
are precisely the trace update, determinant update, and geometric expansion
from Nocedal–Wright (6.44), (6.45), and (6.47). -/
theorem bfgs_scalar_trace_det_dennis_more
    (trace determinant m M q cosine secantError directionalError : ℕ → ℝ)
    (hD : ∀ k, 0 < determinant k)
    (hm : ∀ k, 0 < m k)
    (hq : ∀ k, 0 < q k)
    (hc : ∀ k, 0 < cosine k)
    (hc_le : ∀ k, cosine k ≤ 1)
    (hpot : ∀ k, 0 ≤ trace k - Real.log (determinant k))
    (herr : ∀ k, 0 ≤ secantError k)
    (hsum : Summable secantError)
    (htrace : ∀ k, trace (k + 1) =
      trace k - q k / cosine k ^ 2 + M k)
    (hdet : ∀ k, determinant (k + 1) =
      determinant k * m k / q k)
    (herror : ∀ k, M k - Real.log (m k) - 1 ≤ secantError k)
    (hdirectional : ∀ k, 0 ≤ directionalError k)
    (hgeometry : ∀ k, directionalError k ^ 2 =
      q k ^ 2 / cosine k ^ 2 - 2 * q k + 1) :
    Tendsto directionalError atTop (nhds 0) := by
  obtain ⟨hangle, hradial⟩ :=
    bfgs_scalar_trace_det_defects_tendsto_zero
      trace determinant m M q cosine secantError
      hD hm hq hc hc_le hpot herr hsum htrace hdet herror
  exact bfgs_defects_imply_directional_error q
    (fun k => cosine k ^ 2) directionalError hq
    (fun k => sq_pos_of_pos (hc k)) hangle hradial
    hdirectional hgeometry

/-- The geometric expansion (6.47), stated directly for a step `s` and its
image `u = B s`. Positivity of their inner product makes every denominator
nonzero. -/
theorem bfgs_geometric_identity {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u s : E) (ha : 0 < inner ℝ u s) :
    (‖u - s‖ / ‖s‖) ^ 2 =
      ((inner ℝ u s / ‖s‖ ^ 2) ^ 2) /
        ((inner ℝ u s) ^ 2 / (‖u‖ ^ 2 * ‖s‖ ^ 2)) -
      2 * (inner ℝ u s / ‖s‖ ^ 2) + 1 := by
  have hs : s ≠ 0 := by
    intro h
    simp [h] at ha
  have hu : u ≠ 0 := by
    intro h
    simp [h] at ha
  have hns : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hia : inner ℝ u s ≠ 0 := ne_of_gt ha
  rw [div_pow, norm_sub_sq_real]
  field_simp

end QuasiNewtonConvergence

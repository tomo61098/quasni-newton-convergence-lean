import QuasiNewtonConvergence.KarmarkarProjective
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# The projected-cost estimate in Karmarkar's projective step

The hypotheses `ℓ p = ⟪p,p⟫` and `ℓ u = ⟪p,u-z⟫` are the two
orthogonal-projection identities on the transformed feasible tangent space.
-/

noncomputable section
namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Optimizing the transformed linear objective along its projected
negative-gradient direction reduces it by at least the inscribed-radius to
circumscribed-radius ratio. -/
theorem karmarkar_projected_cost_ratio
    (ℓ : E →ₗ[ℝ] ℝ) (u z p : E) (α r R : ℝ)
    (hα : 0 < α) (hr : 0 < r) (hR : 0 < R)
    (hz : ℓ z = 0) (hu : 0 < ℓ u)
    (hprojection : ℓ (u - z) = inner ℝ p (u - z))
    (hprojectedDirection : ℓ p = inner ℝ p p)
    (hradius : ‖u - z‖ ≤ R) :
    ℓ (u - (α * r / ‖p‖) • p) / ℓ u ≤ 1 - α * r / R := by
  have hcost : ℓ u = inner ℝ p (u - z) := by
    have hlin : ℓ (u - z) = ℓ u := by simp [map_sub, hz]
    exact hlin.symm.trans hprojection
  have hp : p ≠ 0 := by
    intro hp0
    simp [hp0] at hcost
    exact (ne_of_gt hu) hcost
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have houter : ℓ u ≤ ‖p‖ * R := by
    rw [hcost]
    exact (real_inner_le_norm p (u - z)).trans
      (mul_le_mul_of_nonneg_left hradius (norm_nonneg p))
  have hpr : ℓ u / R ≤ ‖p‖ := by
    apply (div_le_iff₀ hR).mpr
    simpa [mul_comm] using houter
  have hβ : 0 < α * r := mul_pos hα hr
  have hβpr := mul_le_mul_of_nonneg_left hpr hβ.le
  have hstep : ℓ (u - (α * r / ‖p‖) • p) =
      ℓ u - α * r * ‖p‖ := by
    rw [map_sub, map_smul, hprojectedDirection,
      real_inner_self_eq_norm_sq]
    have hpn0 : ‖p‖ ≠ 0 := ne_of_gt hpn
    have hnorm : ‖p‖ ^ 2 * ‖p‖⁻¹ = ‖p‖ := by
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hpn0, mul_one]
    simp only [smul_eq_mul, div_eq_mul_inv]
    calc
      ℓ u - α * r * ‖p‖⁻¹ * ‖p‖ ^ 2 =
          ℓ u - α * r * (‖p‖ ^ 2 * ‖p‖⁻¹) := by ring
      _ = ℓ u - α * r * ‖p‖ := by rw [hnorm]
  rw [hstep]
  apply (div_le_iff₀ hu).mpr
  rw [show (1 - α * r / R) * ℓ u =
    ℓ u - α * r * (ℓ u / R) by ring]
  linarith [hβpr]

/-- The quarter-radius choice and the simplex radius ratio give precisely
the objective-ratio hypothesis in `karmarkar_projective_step_drop`. -/
theorem karmarkar_projected_cost_ratio_quarter
    (ℓ : E →ₗ[ℝ] ℝ) (u z p : E) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R)
    (hz : ℓ z = 0) (hu : 0 < ℓ u)
    (hprojection : ℓ (u - z) = inner ℝ p (u - z))
    (hprojectedDirection : ℓ p = inner ℝ p p)
    (hradius : ‖u - z‖ ≤ R)
    (n : ℕ) (hn : 2 ≤ n)
    (hratio : r / R = 1 / ((n : ℝ) - 1)) :
    ℓ (u - ((1 / 4 : ℝ) * r / ‖p‖) • p) / ℓ u ≤
      1 - 1 / (4 * ((n : ℝ) - 1)) := by
  have h := karmarkar_projected_cost_ratio ℓ u z p (1 / 4 : ℝ) r R
    (by norm_num) hr hR hz hu hprojection hprojectedDirection hradius
  calc
    ℓ (u - ((1 / 4 : ℝ) * r / ‖p‖) • p) / ℓ u ≤
        1 - (1 / 4 : ℝ) * r / R := h
    _ = 1 - 1 / (4 * ((n : ℝ) - 1)) := by
      rw [show (1 / 4 : ℝ) * r / R = (1 / 4 : ℝ) * (r / R) by ring,
        hratio]
      have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (n : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hn0]

/-- The zero-sum tangent-space condition sharpens the coordinate estimate
from a squared-radius bound by the factor `(n-1)/n`. -/
theorem karmarkar_coordinate_lower_of_radius
    {n : ℕ} (hn : 2 ≤ n) (t : Fin n → ℝ)
    (hsum : ∑ i, t i = 0)
    (hradius : ∑ i, (t i) ^ 2 ≤
      (n : ℝ) / (16 * ((n : ℝ) - 1)))
    (i : Fin n) : -(1 / 4 : ℝ) ≤ t i := by
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnm1 : 0 < (n : ℝ) - 1 := by linarith
  have hcard : ((Finset.univ.erase i) : Finset (Fin n)).card = n - 1 := by
    simp
  have hsumErase : ∑ j ∈ (Finset.univ.erase i), t j = -t i := by
    have h := Finset.sum_erase_add Finset.univ t (Finset.mem_univ i)
    rw [hsum] at h
    linarith
  have hsqErase : ∑ j ∈ (Finset.univ.erase i), (t j) ^ 2 =
      (∑ j, (t j) ^ 2) - (t i) ^ 2 := by
    have h := Finset.sum_erase_add Finset.univ (fun j => (t j) ^ 2)
      (Finset.mem_univ i)
    linarith
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ.erase i) (f := t)
  rw [hsumErase, hcard, hsqErase] at hCS
  have hnonneg : 0 ≤ ∑ j, (t j) ^ 2 :=
    Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hscaled : (n : ℝ) * (t i) ^ 2 ≤
      ((n : ℝ) - 1) * (∑ j, (t j) ^ 2) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast] at hCS
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hradius hnm1.le
  have hbound : (t i) ^ 2 ≤ (1 / 16 : ℝ) := by
    have hcancel : ((n : ℝ) / (16 * ((n : ℝ) - 1))) *
        ((n : ℝ) - 1) = (n : ℝ) / 16 := by
      field_simp [ne_of_gt hnm1]
    apply le_of_mul_le_mul_left ?_ (by linarith : 0 < (n : ℝ))
    nlinarith [hscaled, hmul, hcancel]
  nlinarith [hbound]

/-- The quarter-inscribed-radius displacement has the coordinate bounds
needed for the logarithmic barrier estimate. The direction is normalized and
lies in the simplex tangent space. -/
theorem karmarkar_quarter_step_coordinates
    {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ) (r : ℝ)
    (hpsum : ∑ i, p i = 0)
    (hpnorm : ∑ i, (p i) ^ 2 = 1)
    (hrsq : r ^ 2 = 1 / ((n : ℝ) * ((n : ℝ) - 1))) :
    let y : Fin n → ℝ := fun i =>
      karmarkarCenter n i - (1 / 4 : ℝ) * r * p i
    (∀ i, 0 < y i) ∧ (∑ i, y i = 1) ∧
    (∀ i, -(1 / 4 : ℝ) ≤ (n : ℝ) * y i - 1) ∧
    (∑ i, ((n : ℝ) * y i - 1) ^ 2 ≤ (1 / 8 : ℝ)) := by
  have : NeZero n := ⟨by omega⟩
  let y : Fin n → ℝ := fun i =>
    karmarkarCenter n i - (1 / 4 : ℝ) * r * p i
  let t : Fin n → ℝ := fun i => (n : ℝ) * y i - 1
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hnm1 : 0 < (n : ℝ) - 1 := by linarith
  have hnt (i : Fin n) : t i = -((n : ℝ) / 4 * r) * p i := by
    dsimp [t, y, karmarkarCenter]
    field_simp [ne_of_gt hnpos]
    ring
  have htsum : ∑ i, t i = 0 := by
    simp_rw [hnt]
    rw [← Finset.mul_sum, hpsum]
    ring
  have hsqexact : ∑ i, (t i) ^ 2 =
      (n : ℝ) / (16 * ((n : ℝ) - 1)) := by
    calc
      ∑ i, (t i) ^ 2 =
          ((n : ℝ) / 4 * r) ^ 2 * (∑ i, (p i) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hnt]
        ring
      _ = ((n : ℝ) / 4 * r) ^ 2 := by rw [hpnorm, mul_one]
      _ = (n : ℝ) / (16 * ((n : ℝ) - 1)) := by
        rw [mul_pow, hrsq]
        field_simp [ne_of_gt hnpos, ne_of_gt hnm1]
        ring
  have hlower (i : Fin n) : -(1 / 4 : ℝ) ≤ t i := by
    apply karmarkar_coordinate_lower_of_radius hn t htsum
    rw [hsqexact]
  have hypos (i : Fin n) : 0 < y i := by
    by_contra h
    have hy0 : y i ≤ 0 := le_of_not_gt h
    have hmul := mul_nonpos_of_nonneg_of_nonpos hnpos.le hy0
    have ht := hlower i
    dsimp [t] at ht
    linarith
  have hysum : ∑ i, y i = 1 := by
    dsimp [y]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
      karmarkarCenter_sum, hpsum, mul_zero, sub_zero]
  have hsq : ∑ i, (t i) ^ 2 ≤ (1 / 8 : ℝ) := by
    rw [hsqexact]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hnm1)).mpr
    nlinarith
  exact ⟨hypos, hysum, hlower, hsq⟩

end QuasiNewtonConvergence

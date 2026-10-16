import QuasiNewtonConvergence.KarmarkarProjective
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A full Newton step for the logarithmic barrier

The central algebraic identity is special to the log barrier: after a full
Newton correction, each scaled stationarity residual is the negative square
of the corresponding scaled Newton direction. The theorem below proves
positivity, the explicit residual identity, and a Euclidean residual bound
from a certified Newton direction. Orthogonality of the scaled multiplier
then transfers that bound to the projected gradient at the new point.
The construction and local-norm bound for the direction remain separate.
-/

noncomputable section
namespace QuasiNewtonConvergence

open scoped BigOperators

/-- Orthogonal projection gives the local-dual-norm perturbation estimate
behind a short-step barrier-parameter increase. -/
theorem orthogonalProjection_parameter_perturb_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (v e : E) (s : ℝ) (hs : 0 ≤ s) :
    ‖U.starProjection (v + s • (v + e))‖ ≤
      ‖U.starProjection v‖ +
        s * (‖U.starProjection v‖ + ‖e‖) := by
  have hproj : ‖U.starProjection e‖ ≤ ‖e‖ :=
    U.norm_starProjection_apply_le e
  calc
    ‖U.starProjection (v + s • (v + e))‖ =
        ‖U.starProjection v + s •
          (U.starProjection v + U.starProjection e)‖ := by
      simp [map_add, map_smul]
    _ ≤ ‖U.starProjection v‖ +
        ‖s • (U.starProjection v + U.starProjection e)‖ :=
      norm_add_le _ _
    _ = ‖U.starProjection v‖ +
        s * ‖U.starProjection v + U.starProjection e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ ‖U.starProjection v‖ +
        s * (‖U.starProjection v‖ + ‖U.starProjection e‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖U.starProjection v‖ +
        s * (‖U.starProjection v‖ + ‖e‖) := by
      gcongr

/-- The all-ones vector has Euclidean norm `√n`. -/
theorem logBarrier_ones_norm (n : ℕ) :
    ‖(WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)) :
      EuclideanSpace ℝ (Fin n))‖ = Real.sqrt (n : ℝ) := by
  let e : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))
  have hsq : ‖e‖ ^ 2 = (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [e]
  calc
    ‖e‖ = Real.sqrt (‖e‖ ^ 2) := (Real.sqrt_sq (norm_nonneg e)).symm
    _ = Real.sqrt (n : ℝ) := by rw [hsq]

/-- The projected cost perturbation for the log barrier, with its
`√n` barrier-gradient constant made explicit. -/
theorem logBarrier_projected_cost_perturb_bound
    {n : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [U.HasOrthogonalProjection]
    (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) (hs : 0 ≤ s) :
    let e : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))
    ‖U.starProjection (v + s • (v + e))‖ ≤
      ‖U.starProjection v‖ +
        s * (‖U.starProjection v‖ + Real.sqrt (n : ℝ)) := by
  let e : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))
  have h := orthogonalProjection_parameter_perturb_bound U v e s hs
  simpa only [show ‖e‖ = Real.sqrt (n : ℝ) from logBarrier_ones_norm n] using h

/-- Exact scalar identity behind the log-barrier Newton residual. -/
theorem logBarrier_newton_residual_identity
    (x d : ℝ) (hx : x ≠ 0) (hnew : x + d ≠ 0) :
    (1 - (d / x) ^ 2) / (x + d) = 1 / x - d / x ^ 2 := by
  field_simp [hx, hnew]
  ring

/-- A scaled direction smaller than one keeps the full step positive. -/
theorem logBarrier_newton_coordinate_pos
    (x d ρ : ℝ) (hx : 0 < x) (hρ : ρ < 1)
    (hbound : |d / x| ≤ ρ) :
    0 < x + d := by
  have hlow : -1 < d / x := by
    have := (abs_le.mp hbound).1
    linarith
  have hrepr : x + d = x * (1 + d / x) := by
    field_simp [ne_of_gt hx]
  rw [hrepr]
  exact mul_pos hx (by linarith)

/-- A bound on the squared local norm bounds every scaled coordinate. -/
theorem logBarrier_local_norm_coordinate_bound
    {n : ℕ} (u : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hnorm : ∑ i, (u i) ^ 2 ≤ ρ ^ 2) (i : Fin n) :
    |u i| ≤ ρ := by
  have hi : (u i) ^ 2 ≤ ∑ j, (u j) ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (u j))
      (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg (u i)) hρ).mp
  simpa only [sq_abs] using hi.trans hnorm

/-- The Euclidean norm of the squared scaled-step residual is at most the
square of the original local Newton norm. -/
theorem logBarrier_squared_residual_norm_bound
    {n : ℕ} (u : Fin n → ℝ) :
    (∑ i, ((u i) ^ 2) ^ 2) ≤
      (∑ i, (u i) ^ 2) ^ 2 := by
  exact Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun i hi => sq_nonneg (u i))

/-- The explicit Newton residual has Euclidean norm at most the square of
the pre-step local norm. Keeping this norm bound, rather than only the
coordinatewise bound, allows it to feed the next short-step estimate. -/
theorem logBarrier_full_newton_euclidean_residual_invariant
    {n : ℕ} (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (hx : ∀ i, 0 < x i) (hρ : 0 ≤ ρ) (hρone : ρ < 1)
    (hnorm : ∑ i, (d i / x i) ^ 2 ≤ ρ ^ 2)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i) :
    let xnew : Fin n → ℝ := fun i => x i + d i
    let e : Fin n → ℝ := fun i => -(d i / x i) ^ 2
    (∀ i, 0 < xnew i) ∧
      (∀ i, xnew i * (t * c i - 1 / xnew i - q i) = e i) ∧
      ‖(WithLp.toLp 2 e : EuclideanSpace ℝ (Fin n))‖ ≤ ρ ^ 2 ∧
      (∀ i, t * c i - (1 + e i) / xnew i = q i) := by
  let xnew : Fin n → ℝ := fun i => x i + d i
  let e : Fin n → ℝ := fun i => -(d i / x i) ^ 2
  have hxnew (i : Fin n) : 0 < xnew i :=
    logBarrier_newton_coordinate_pos (x i) (d i) ρ (hx i) hρone
      (logBarrier_local_norm_coordinate_bound
        (fun j => d j / x j) ρ hρ hnorm i)
  have hstationary (i : Fin n) :
      t * c i - (1 + e i) / xnew i = q i := by
    have hid := logBarrier_newton_residual_identity (x i) (d i)
      (ne_of_gt (hx i)) (ne_of_gt (hxnew i))
    dsimp [e, xnew]
    rw [show 1 + -(d i / x i) ^ 2 = 1 - (d i / x i) ^ 2 by ring, hid]
    linarith [hnewton i]
  have hresidual (i : Fin n) :
      xnew i * (t * c i - 1 / xnew i - q i) = e i := by
    rw [← hstationary i]
    field_simp [ne_of_gt (hxnew i)]
    ring
  have hsumnonneg : 0 ≤ ∑ i, (d i / x i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hsum_sq : (∑ i, (d i / x i) ^ 2) ^ 2 ≤ (ρ ^ 2) ^ 2 :=
    (sq_le_sq₀ hsumnonneg (sq_nonneg ρ)).mpr hnorm
  have henorm : ‖(WithLp.toLp 2 e : EuclideanSpace ℝ (Fin n))‖ ≤ ρ ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (sq_nonneg ρ)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [e] using
      (logBarrier_squared_residual_norm_bound (fun i => d i / x i)).trans hsum_sq
  exact ⟨hxnew, hresidual, henorm, hstationary⟩

/-- A multiplier orthogonal to the scaled feasible tangent space disappears
under projection. Thus a Euclidean residual bound controls the projected
scaled gradient, which is the quantity used by the short-step theorem. -/
theorem logBarrier_projected_gradient_of_residual
    {n : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [U.HasOrthogonalProjection]
    (c x q e : Fin n → ℝ) (t β : ℝ)
    (hx : ∀ i, x i ≠ 0)
    (hstationary : ∀ i, t * c i - (1 + e i) / x i = q i)
    (horth : (WithLp.toLp 2 (fun i => x i * q i) :
      EuclideanSpace ℝ (Fin n)) ∈ Uᗮ)
    (he : ‖(WithLp.toLp 2 e : EuclideanSpace ℝ (Fin n))‖ ≤ β) :
    ‖U.starProjection (WithLp.toLp 2 (fun i => t * x i * c i - 1))‖ ≤ β := by
  have hdecomp :
      (WithLp.toLp 2 (fun i => t * x i * c i - 1) :
        EuclideanSpace ℝ (Fin n)) =
      WithLp.toLp 2 e + WithLp.toLp 2 (fun i => x i * q i) := by
    ext i
    change t * x i * c i - 1 = e i + x i * q i
    rw [← hstationary i]
    field_simp [hx i]
    <;> ring
  have hqzero : U.starProjection
      (WithLp.toLp 2 (fun i => x i * q i)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).mpr horth
  rw [hdecomp, map_add, hqzero, add_zero]
  exact (U.norm_starProjection_apply_le _).trans he

/-- The Euclidean Newton residual controls the projected gradient at the
new point. Here `U` is the tangent space scaled by the new positive point,
and the scaled equality multiplier belongs to its orthogonal complement. -/
theorem logBarrier_full_newton_projected_invariant
    {n : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [U.HasOrthogonalProjection]
    (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (hx : ∀ i, 0 < x i) (hρ : 0 ≤ ρ) (hρone : ρ < 1)
    (hnorm : ∑ i, (d i / x i) ^ 2 ≤ ρ ^ 2)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i)
    (horth : (WithLp.toLp 2 (fun i => (x i + d i) * q i) :
      EuclideanSpace ℝ (Fin n)) ∈ Uᗮ) :
    (∀ i, 0 < x i + d i) ∧
      ‖U.starProjection
        (WithLp.toLp 2 (fun i => t * (x i + d i) * c i - 1))‖ ≤ ρ ^ 2 := by
  obtain ⟨hxnew, _, he, hstationary⟩ :=
    logBarrier_full_newton_euclidean_residual_invariant c x d q t ρ
      hx hρ hρone hnorm hnewton
  exact ⟨hxnew, logBarrier_projected_gradient_of_residual U c
    (fun i => x i + d i) q (fun i => -(d i / x i) ^ 2) t (ρ ^ 2)
    (fun i => ne_of_gt (hxnew i)) hstationary horth he⟩

/-- A certified full Newton step keeps a coordinatewise centrality
neighborhood. The new residual is exactly `-(dᵢ/xᵢ)^2`. -/
theorem logBarrier_full_newton_residual_invariant
    {n : ℕ} (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (hx : ∀ i, 0 < x i) (hρ : 0 ≤ ρ) (hρone : ρ < 1)
    (hscaled : ∀ i, |d i / x i| ≤ ρ)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i)
    (horth : ∀ z, feasible z →
      ∑ i, q i * ((x i + d i) - z i) = 0) :
    let xnew : Fin n → ℝ := fun i => x i + d i
    (∀ i, 0 < xnew i) ∧
      ∃ e : Fin n → ℝ,
        (∀ i, |e i| ≤ ρ ^ 2) ∧
        ∀ z, feasible z →
          ∑ i, (t * c i - (1 + e i) / xnew i) *
            (xnew i - z i) = 0 := by
  let xnew : Fin n → ℝ := fun i => x i + d i
  let e : Fin n → ℝ := fun i => -(d i / x i) ^ 2
  have hxnew (i : Fin n) : 0 < xnew i := by
    exact logBarrier_newton_coordinate_pos (x i) (d i) ρ
      (hx i) hρone (hscaled i)
  have he (i : Fin n) : |e i| ≤ ρ ^ 2 := by
    have hu := hscaled i
    have hsq := (sq_le_sq₀ (abs_nonneg (d i / x i)) hρ).mpr hu
    dsimp [e]
    simpa only [abs_neg, abs_pow, abs_abs, sq_abs] using hsq
  have hnewton' (i : Fin n) :
      t * c i - (1 + e i) / xnew i = q i := by
    have hid := logBarrier_newton_residual_identity (x i) (d i)
      (ne_of_gt (hx i)) (ne_of_gt (hxnew i))
    dsimp [e, xnew]
    rw [show 1 + -(d i / x i) ^ 2 = 1 - (d i / x i) ^ 2 by ring, hid]
    linarith [hnewton i]
  refine ⟨hxnew, ⟨e, he, ?_⟩⟩
  intro z hz
  change ∑ i, (t * c i - (1 + e i) / xnew i) *
    (xnew i - z i) = 0
  simp_rw [hnewton']
  exact horth z hz

/-- The full-step invariant stated with the usual squared local Newton
norm instead of coordinatewise bounds. -/
theorem logBarrier_full_newton_local_norm_invariant
    {n : ℕ} (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (hx : ∀ i, 0 < x i) (hρ : 0 ≤ ρ) (hρone : ρ < 1)
    (hnorm : ∑ i, (d i / x i) ^ 2 ≤ ρ ^ 2)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i)
    (horth : ∀ z, feasible z →
      ∑ i, q i * ((x i + d i) - z i) = 0) :
    let xnew : Fin n → ℝ := fun i => x i + d i
    (∀ i, 0 < xnew i) ∧
      ∃ e : Fin n → ℝ,
        (∀ i, |e i| ≤ ρ ^ 2) ∧
        ∀ z, feasible z →
          ∑ i, (t * c i - (1 + e i) / xnew i) *
            (xnew i - z i) = 0 := by
  exact logBarrier_full_newton_residual_invariant c x d q t ρ
    feasible hx hρ hρone
    (fun i => logBarrier_local_norm_coordinate_bound
      (fun j => d j / x j) ρ hρ hnorm i)
    hnewton horth

/-- The short-step parameter change keeps the pre-Newton decrement below
`21/64`, provided its standard local-dual-norm perturbation estimate holds. -/
theorem logBarrier_short_step_pre_newton_bound
    (s lam ρ : ℝ) (hs : 1 ≤ s)
    (hlam : 0 ≤ lam) (hlamquarter : lam ≤ 1 / 4)
    (hperturb : ρ ≤ lam + (1 / (16 * s)) * (s + lam)) :
    ρ ≤ 21 / 64 := by
  have hspos : 0 < s := by linarith
  have hlams : lam ≤ s / 4 := by linarith
  have hfrac : lam / (16 * s) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * s)).mpr
    nlinarith [hlams]
  have hident : (1 / (16 * s)) * (s + lam) =
      1 / 16 + lam / (16 * s) := by
    field_simp [ne_of_gt hspos]
  rw [hident] at hperturb
  linarith

/-- A short barrier-parameter update takes a projected decrement at most
`1/4` to a pre-Newton decrement at most `21/64`. -/
theorem logBarrier_short_step_projection_bound
    {n : ℕ} (hn : 1 ≤ n)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [U.HasOrthogonalProjection]
    (v : EuclideanSpace ℝ (Fin n))
    (hcurrent : ‖U.starProjection v‖ ≤ (1 / 4 : ℝ)) :
    let e : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))
    let s : ℝ := 1 / (16 * Real.sqrt (n : ℝ))
    ‖U.starProjection (v + s • (v + e))‖ ≤ 21 / 64 := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hnreal
  have hs : 0 ≤ 1 / (16 * Real.sqrt (n : ℝ)) := by positivity
  have hperturb := logBarrier_projected_cost_perturb_bound U v
    (1 / (16 * Real.sqrt (n : ℝ))) hs
  dsimp at hperturb
  have hperturb' :
      ‖U.starProjection (v +
        (1 / (16 * Real.sqrt (n : ℝ))) •
          (v + WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))))‖ ≤
      ‖U.starProjection v‖ +
        (1 / (16 * Real.sqrt (n : ℝ))) *
          (Real.sqrt (n : ℝ) + ‖U.starProjection v‖) := by
    convert hperturb using 1
    ring
  exact logBarrier_short_step_pre_newton_bound
    (Real.sqrt (n : ℝ)) ‖U.starProjection v‖
    ‖U.starProjection (v +
      (1 / (16 * Real.sqrt (n : ℝ))) •
        (v + WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))))‖
    hsqrt (norm_nonneg _) hcurrent hperturb'

/-- A full Newton step with local norm at most `21/64` restores the
projected Euclidean neighborhood needed by the next parameter update. -/
theorem logBarrier_full_newton_projected_quarter_invariant
    {n : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [U.HasOrthogonalProjection]
    (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (hx : ∀ i, 0 < x i) (hρ : 0 ≤ ρ) (hρbound : ρ ≤ 21 / 64)
    (hnorm : ∑ i, (d i / x i) ^ 2 ≤ ρ ^ 2)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i)
    (horth : (WithLp.toLp 2 (fun i => (x i + d i) * q i) :
      EuclideanSpace ℝ (Fin n)) ∈ Uᗮ) :
    (∀ i, 0 < x i + d i) ∧
      ‖U.starProjection
        (WithLp.toLp 2 (fun i => t * (x i + d i) * c i - 1))‖ ≤ 1 / 4 := by
  have hρone : ρ < 1 := by linarith
  have hρsq : ρ ^ 2 ≤ (1 / 4 : ℝ) := by
    have hsq := (sq_le_sq₀ hρ (by norm_num : (0 : ℝ) ≤ 21 / 64)).mpr hρbound
    nlinarith
  obtain ⟨hxnew, hprojected⟩ := logBarrier_full_newton_projected_invariant
    U c x d q t ρ hx hρ hρone hnorm hnewton horth
  exact ⟨hxnew, hprojected.trans hρsq⟩

/-- The restored projected neighborhood supplies the next short-step
parameter bound without a dimension-dependent loss from coordinate bounds. -/
theorem logBarrier_full_newton_next_short_step_bound
    {n : ℕ} (hn : 1 ≤ n)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [U.HasOrthogonalProjection]
    (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (hx : ∀ i, 0 < x i) (hρ : 0 ≤ ρ) (hρbound : ρ ≤ 21 / 64)
    (hnorm : ∑ i, (d i / x i) ^ 2 ≤ ρ ^ 2)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i)
    (horth : (WithLp.toLp 2 (fun i => (x i + d i) * q i) :
      EuclideanSpace ℝ (Fin n)) ∈ Uᗮ) :
    (∀ i, 0 < x i + d i) ∧
      ‖U.starProjection (WithLp.toLp 2 (fun i =>
        ((1 + 1 / (16 * Real.sqrt (n : ℝ))) * t) *
          (x i + d i) * c i - 1))‖ ≤ 21 / 64 := by
  obtain ⟨hxnew, hprojected⟩ :=
    logBarrier_full_newton_projected_quarter_invariant U c x d q t ρ
      hx hρ hρbound hnorm hnewton horth
  have hnext := logBarrier_short_step_projection_bound hn U
    (WithLp.toLp 2 (fun i => t * (x i + d i) * c i - 1)) hprojected
  refine ⟨hxnew, ?_⟩
  convert hnext using 2
  congr 1
  ext i
  change ((1 + 1 / (16 * Real.sqrt (n : ℝ))) * t) *
      (x i + d i) * c i - 1 =
    (t * (x i + d i) * c i - 1) +
      (1 / (16 * Real.sqrt (n : ℝ))) *
        ((t * (x i + d i) * c i - 1) + 1)
  ring

/-- The exact log-barrier Newton residual is below `1/4` after a step
whose local norm is at most `21/64`. -/
theorem logBarrier_full_newton_quarter_invariant
    {n : ℕ} (c x d q : Fin n → ℝ) (t ρ : ℝ)
    (feasible : (Fin n → ℝ) → Prop)
    (hx : ∀ i, 0 < x i)
    (hρ : 0 ≤ ρ) (hρbound : ρ ≤ 21 / 64)
    (hnorm : ∑ i, (d i / x i) ^ 2 ≤ ρ ^ 2)
    (hnewton : ∀ i,
      t * c i - 1 / x i + d i / (x i) ^ 2 = q i)
    (horth : ∀ z, feasible z →
      ∑ i, q i * ((x i + d i) - z i) = 0) :
    let xnew : Fin n → ℝ := fun i => x i + d i
    (∀ i, 0 < xnew i) ∧
      ∃ e : Fin n → ℝ,
        (∀ i, |e i| ≤ 1 / 4) ∧
        ∀ z, feasible z →
          ∑ i, (t * c i - (1 + e i) / xnew i) *
            (xnew i - z i) = 0 := by
  have hρone : ρ < 1 := by linarith
  have hρsq : ρ ^ 2 ≤ (1 / 4 : ℝ) := by
    have hsq := (sq_le_sq₀ hρ (by norm_num : (0 : ℝ) ≤ 21 / 64)).mpr hρbound
    nlinarith
  obtain ⟨hpos, e, he, hstationary⟩ :=
    logBarrier_full_newton_local_norm_invariant c x d q t ρ
      feasible hx hρ hρone hnorm hnewton horth
  exact ⟨hpos, e, (fun i => (he i).trans hρsq), hstationary⟩

end QuasiNewtonConvergence

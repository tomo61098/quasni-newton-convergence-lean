module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The projective map in Karmarkar's algorithm

These statements concern the fractional projective map used in the original
algorithm. They are independent of a choice of projected descent direction.
-/

noncomputable section
namespace QuasiNewtonConvergence

open scoped BigOperators

variable {n : ℕ}

def karmarkarDenominator (a y : Fin n → ℝ) : ℝ :=
  ∑ i, a i * y i

def karmarkarInverse (a y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a i * y i / karmarkarDenominator a y

def karmarkarForward (a x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (x i / a i) / (∑ j, x j / a j)

theorem karmarkarDenominator_pos (a y : Fin n → ℝ)
    [NeZero n] (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i) :
    0 < karmarkarDenominator a y := by
  unfold karmarkarDenominator
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (ha i) (hy i)
  · exact Finset.univ_nonempty

theorem karmarkarInverse_sum (a y : Fin n → ℝ)
    (hden : karmarkarDenominator a y ≠ 0) :
    ∑ i, karmarkarInverse a y i = 1 := by
  calc
    ∑ i, karmarkarInverse a y i =
        (∑ i, a i * y i) / karmarkarDenominator a y := by
      simp [karmarkarInverse, div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by rw [show (∑ i, a i * y i) = karmarkarDenominator a y from rfl,
      div_self hden]

theorem karmarkarInverse_pos (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (hden : 0 < karmarkarDenominator a y) (i : Fin n) :
    0 < karmarkarInverse a y i :=
  div_pos (mul_pos (ha i) (hy i)) hden

theorem karmarkarInverse_linear_constraint
    {m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a y : Fin n → ℝ)
    (hAy : A (fun i => a i * y i) = 0) :
    A (karmarkarInverse a y) = 0 := by
  have hrepr : karmarkarInverse a y =
      (1 / karmarkarDenominator a y) • (fun i => a i * y i) := by
    ext i
    simp [karmarkarInverse, div_eq_mul_inv, mul_comm]
  rw [hrepr, map_smul, hAy, smul_zero]

theorem karmarkarForward_inverse (a x : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0)
    (hsum : ∑ i, x i = 1)
    (hT : (∑ i, x i / a i) ≠ 0) :
    karmarkarInverse a (karmarkarForward a x) = x := by
  let T : ℝ := ∑ i, x i / a i
  have hden : karmarkarDenominator a (karmarkarForward a x) = 1 / T := by
    have hnum : (∑ i, a i * (x i / a i)) = 1 := by
      convert hsum using 1
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [ha i]
    calc
      karmarkarDenominator a (karmarkarForward a x) =
          (∑ i, a i * (x i / a i)) / T := by
        simp only [karmarkarDenominator, karmarkarForward, T,
          div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 1 / T := by rw [hnum]
  ext i
  simp only [karmarkarInverse, karmarkarForward, hden]
  dsimp [T]
  field_simp [ha i, hT]

theorem karmarkarInverse_forward (a y : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0)
    (hy : ∑ i, y i = 1)
    (hS : karmarkarDenominator a y ≠ 0) :
    karmarkarForward a (karmarkarInverse a y) = y := by
  let S : ℝ := karmarkarDenominator a y
  have hden : (∑ j, karmarkarInverse a y j / a j) = 1 / S := by
    have hterm (j : Fin n) : karmarkarInverse a y j / a j = y j / S := by
      simp only [karmarkarInverse]
      dsimp [S]
      field_simp [ha j, hS]
    calc
      (∑ j, karmarkarInverse a y j / a j) = ∑ j, y j / S := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      _ = (∑ j, y j) / S := by
        simp [div_eq_mul_inv, Finset.sum_mul]
      _ = 1 / S := by rw [hy]
  ext i
  change (karmarkarInverse a y i / a i) /
    (∑ j, karmarkarInverse a y j / a j) = y i
  rw [hden]
  dsimp [S, karmarkarInverse]
  field_simp [ha i, hS]

def karmarkarCost (c x : Fin n → ℝ) : ℝ := ∑ i, c i * x i

def karmarkarWeightedCost (a c y : Fin n → ℝ) : ℝ :=
  ∑ i, c i * a i * y i

def karmarkarPotential (c x : Fin n → ℝ) : ℝ :=
  (n : ℝ) * Real.log (karmarkarCost c x) -
    ∑ i, Real.log (x i)

theorem karmarkarCost_inverse (a c y : Fin n → ℝ) :
    karmarkarCost c (karmarkarInverse a y) =
      karmarkarWeightedCost a c y / karmarkarDenominator a y := by
  simp only [karmarkarCost, karmarkarInverse,
    karmarkarWeightedCost, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The projective denominator cancels exactly from Karmarkar's logarithmic
potential. This is the invariant-potential step of the original algorithm. -/
theorem karmarkarPotential_inverse (a c y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (hS : 0 < karmarkarDenominator a y)
    (hW : 0 < karmarkarWeightedCost a c y) :
    karmarkarPotential c (karmarkarInverse a y) =
      (n : ℝ) * Real.log (karmarkarWeightedCost a c y) -
        (∑ i, Real.log (a i)) - ∑ i, Real.log (y i) := by
  have hcoord (i : Fin n) :
      Real.log (karmarkarInverse a y i) =
        Real.log (a i) + Real.log (y i) -
          Real.log (karmarkarDenominator a y) := by
    rw [karmarkarInverse, Real.log_div
      (ne_of_gt (mul_pos (ha i) (hy i))) (ne_of_gt hS),
      Real.log_mul (ne_of_gt (ha i)) (ne_of_gt (hy i))]
  simp only [karmarkarPotential, karmarkarCost_inverse]
  rw [Real.log_div (ne_of_gt hW) (ne_of_gt hS)]
  simp_rw [hcoord]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

def karmarkarCenter (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

theorem karmarkarCenter_sum [NeZero n] :
    ∑ i, karmarkarCenter n i = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp [karmarkarCenter, Finset.sum_const, hn]

theorem karmarkarDenominator_center (a : Fin n → ℝ)
    (ha : ∑ i, a i = 1) :
    karmarkarDenominator a (karmarkarCenter n) = 1 / (n : ℝ) := by
  simp [karmarkarDenominator, karmarkarCenter, ← Finset.sum_mul, ha]

theorem karmarkarWeightedCost_center (a c : Fin n → ℝ) :
    karmarkarWeightedCost a c (karmarkarCenter n) =
      karmarkarCost c a / (n : ℝ) := by
  simp only [karmarkarWeightedCost, karmarkarCost, karmarkarCenter,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem karmarkarInverse_center (a : Fin n → ℝ) [NeZero n]
    (ha : ∑ i, a i = 1) :
    karmarkarInverse a (karmarkarCenter n) = a := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  ext i
  rw [karmarkarInverse, karmarkarDenominator_center a ha]
  simp [karmarkarCenter, hn]

/-- The relative potential identity used to analyze the projective step. -/
theorem karmarkarPotential_projective_change (a c y : Fin n → ℝ)
    [NeZero n]
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (hasum : ∑ i, a i = 1)
    (hS : 0 < karmarkarDenominator a y)
    (hW : 0 < karmarkarWeightedCost a c y)
    (hca : 0 < karmarkarCost c a) :
    karmarkarPotential c (karmarkarInverse a y) -
      karmarkarPotential c a =
      (n : ℝ) * (Real.log (karmarkarWeightedCost a c y) -
        Real.log (karmarkarWeightedCost a c (karmarkarCenter n))) -
      ∑ i, (Real.log (y i) - Real.log (karmarkarCenter n i)) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hu : ∀ i : Fin n, 0 < karmarkarCenter n i := by
    intro i
    exact one_div_pos.mpr hn
  have hSu : 0 < karmarkarDenominator a (karmarkarCenter n) := by
    rw [karmarkarDenominator_center a hasum]
    exact one_div_pos.mpr hn
  have hWu : 0 < karmarkarWeightedCost a c (karmarkarCenter n) := by
    rw [karmarkarWeightedCost_center]
    exact div_pos hca hn
  have hcenter := karmarkarPotential_inverse a c (karmarkarCenter n)
    ha hu hSu hWu
  rw [karmarkarInverse_center a hasum] at hcenter
  rw [karmarkarPotential_inverse a c y ha hy hS hW, hcenter]
  rw [Finset.sum_sub_distrib]
  ring

/-- A uniform projective-potential drop telescopes. -/
theorem karmarkarPotential_telescope (φ : ℕ → ℝ) (δ : ℝ)
    (hstep : ∀ k, φ (k + 1) ≤ φ k - δ) (k : ℕ) :
    φ k ≤ φ 0 - (k : ℝ) * δ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hstep k
      push_cast
      linarith

/-- The logarithmic form of the simplex arithmetic–geometric mean bound. -/
theorem karmarkar_simplex_log_bound [NeZero n] (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) :
    ∑ i, Real.log (x i) ≤ -(n : ℝ) * Real.log (n : ℝ) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hi (i : Fin n) : Real.log (n : ℝ) + Real.log (x i) ≤
      (n : ℝ) * x i - 1 := by
    rw [← Real.log_mul (ne_of_gt hn) (ne_of_gt (hx i))]
    exact Real.log_le_sub_one_of_pos (mul_pos hn (hx i))
  have hsumle := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi' => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, hsum] at hsumle
  nlinarith

theorem karmarkarPotential_simplex_lower [NeZero n]
    (c x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1)
    (hcost : 0 < karmarkarCost c x) :
    (n : ℝ) * Real.log ((n : ℝ) * karmarkarCost c x) ≤
      karmarkarPotential c x := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hlog := Real.log_mul (ne_of_gt hn) (ne_of_gt hcost)
  have hsimplex := karmarkar_simplex_log_bound x hx hsum
  dsimp [karmarkarPotential]
  rw [hlog]
  nlinarith

theorem karmarkarPotential_center [NeZero n]
    (c : Fin n → ℝ)
    (hcost : 0 < karmarkarCost c (karmarkarCenter n)) :
    karmarkarPotential c (karmarkarCenter n) =
      (n : ℝ) * Real.log ((n : ℝ) *
        karmarkarCost c (karmarkarCenter n)) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  simp only [karmarkarPotential, karmarkarCenter,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [Real.log_mul (ne_of_gt hn) (ne_of_gt hcost)]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hn)]
  simp
  ring

/-- A uniform quadratic upper bound for the logarithmic barrier remainder.
The constant is deliberately loose; it still gives a fixed decrease for the
quarter-radius projective step. -/
theorem karmarkar_log_remainder (t : ℝ) (ht : -(1 / 4 : ℝ) ≤ t) :
    -Real.log (1 + t) ≤ -t + (4 / 3 : ℝ) * t ^ 2 := by
  have hp : 0 < 1 + t := by linarith
  have hbase := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hbase
  have hquad : 1 / (1 + t) ≤ 1 - t + (4 / 3 : ℝ) * t ^ 2 := by
    apply (div_le_iff₀ hp).mpr
    have hfactor : 0 ≤ t ^ 2 * (1 + 4 * t) :=
      mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith
  rw [one_div] at hquad
  linarith

theorem karmarkar_barrier_bound {m : ℕ} (t : Fin m → ℝ)
    (hlower : ∀ i, -(1 / 4 : ℝ) ≤ t i)
    (hsum : ∑ i, t i = 0)
    (hsq : ∑ i, (t i) ^ 2 ≤ (1 / 8 : ℝ)) :
    -(∑ i, Real.log (1 + t i)) ≤ (1 / 6 : ℝ) := by
  have hterm : ∀ i : Fin m, -Real.log (1 + t i) ≤
      -(t i) + (4 / 3 : ℝ) * (t i) ^ 2 :=
    fun i => karmarkar_log_remainder (t i) (hlower i)
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, hsum, neg_zero, zero_add] at h
  nlinarith

/-- The actual projective potential falls by a fixed amount when the
projected-cost ratio and the logarithmic-barrier error have the geometric
bounds furnished by Karmarkar's inscribed-ball step. -/
theorem karmarkar_projective_step_drop [NeZero n]
    (hn2 : 2 ≤ n) (a c y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (hasum : ∑ i, a i = 1)
    (hS : 0 < karmarkarDenominator a y)
    (hW : 0 < karmarkarWeightedCost a c y)
    (hca : 0 < karmarkarCost c a)
    (hratio : karmarkarWeightedCost a c y /
      karmarkarWeightedCost a c (karmarkarCenter n) ≤
        1 - 1 / (4 * ((n : ℝ) - 1)))
    (hbarrier : -(∑ i, (Real.log (y i) -
      Real.log (karmarkarCenter n i))) ≤ (1 / 6 : ℝ)) :
    karmarkarPotential c (karmarkarInverse a y) ≤
      karmarkarPotential c a - (1 / 12 : ℝ) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnm1 : 0 < (n : ℝ) - 1 := by linarith
  have hWu : 0 < karmarkarWeightedCost a c (karmarkarCenter n) := by
    rw [karmarkarWeightedCost_center]
    exact div_pos hca hn
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hW hWu)
  rw [Real.log_div (ne_of_gt hW) (ne_of_gt hWu)] at hlogratio
  have hlogle : Real.log (karmarkarWeightedCost a c y) -
      Real.log (karmarkarWeightedCost a c (karmarkarCenter n)) ≤
        -(1 / (4 * ((n : ℝ) - 1))) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlogle hn.le
  have hcoeff : (1 / 4 : ℝ) ≤
      (n : ℝ) * (1 / (4 * ((n : ℝ) - 1))) := by
    calc
      (1 / 4 : ℝ) ≤ (n : ℝ) / (4 * ((n : ℝ) - 1)) := by
        apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hnm1)).mpr
        nlinarith
      _ = _ := by ring
  have hchange := karmarkarPotential_projective_change a c y
    ha hy hasum hS hW hca
  linarith

/-- Coordinate and squared-radius bounds imply the logarithmic-barrier
estimate used in the projective one-step theorem. -/
theorem karmarkar_barrier_bound_from_coordinates [NeZero n]
    (y : Fin n → ℝ)
    (hy : ∀ i, 0 < y i) (hsum : ∑ i, y i = 1)
    (hlower : ∀ i, -(1 / 4 : ℝ) ≤ (n : ℝ) * y i - 1)
    (hsq : ∑ i, ((n : ℝ) * y i - 1) ^ 2 ≤ (1 / 8 : ℝ)) :
    -(∑ i, (Real.log (y i) -
      Real.log (karmarkarCenter n i))) ≤ (1 / 6 : ℝ) := by
  let t : Fin n → ℝ := fun i => (n : ℝ) * y i - 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have htsum : ∑ i, t i = 0 := by
    dsimp [t]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul, hsum]
    ring
  have hbarrier := karmarkar_barrier_bound t hlower htsum hsq
  have hlog (i : Fin n) :
      Real.log (y i) - Real.log (karmarkarCenter n i) =
        Real.log (1 + t i) := by
    have hu : 0 < karmarkarCenter n i := one_div_pos.mpr hn
    have hfrac : y i / karmarkarCenter n i = 1 + t i := by
      dsimp [karmarkarCenter, t]
      field_simp [ne_of_gt hn]
      ring
    rw [← Real.log_div (ne_of_gt (hy i)) (ne_of_gt hu), hfrac]
  convert hbarrier using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact hlog i

theorem karmarkar_projective_step_drop_of_coordinates [NeZero n]
    (hn2 : 2 ≤ n) (a c y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (hasum : ∑ i, a i = 1) (hysum : ∑ i, y i = 1)
    (hS : 0 < karmarkarDenominator a y)
    (hW : 0 < karmarkarWeightedCost a c y)
    (hca : 0 < karmarkarCost c a)
    (hratio : karmarkarWeightedCost a c y /
      karmarkarWeightedCost a c (karmarkarCenter n) ≤
        1 - 1 / (4 * ((n : ℝ) - 1)))
    (hlower : ∀ i, -(1 / 4 : ℝ) ≤ (n : ℝ) * y i - 1)
    (hsq : ∑ i, ((n : ℝ) * y i - 1) ^ 2 ≤ (1 / 8 : ℝ)) :
    karmarkarPotential c (karmarkarInverse a y) ≤
      karmarkarPotential c a - (1 / 12 : ℝ) :=
  karmarkar_projective_step_drop hn2 a c y ha hy hasum hS hW hca
    hratio (karmarkar_barrier_bound_from_coordinates y hy hysum hlower hsq)

/-- The objective bound from the potential drop and the proved simplex
logarithm bound. The one-step decrease remains an explicit hypothesis. -/
theorem karmarkar_objective_exponential_rate
    [NeZero n] (c : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (δ : ℝ)
    (hpos : ∀ k i, 0 < x k i)
    (hsum : ∀ k, ∑ i, x k i = 1)
    (hcost : ∀ k, 0 < karmarkarCost c (x k))
    (hcenter : karmarkarPotential c (x 0) =
      (n : ℝ) * Real.log ((n : ℝ) * karmarkarCost c (x 0)))
    (hstep : ∀ k, karmarkarPotential c (x (k + 1)) ≤
      karmarkarPotential c (x k) - δ) (k : ℕ) :
    karmarkarCost c (x k) ≤ karmarkarCost c (x 0) *
      Real.exp (-(k : ℝ) * δ / (n : ℝ)) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have htel := karmarkarPotential_telescope
    (fun j => karmarkarPotential c (x j)) δ hstep k
  have hlog : Real.log ((n : ℝ) * karmarkarCost c (x k)) ≤
      Real.log ((n : ℝ) * karmarkarCost c (x 0)) -
        (k : ℝ) * δ / (n : ℝ) := by
    rw [hcenter] at htel
    have hbound := karmarkarPotential_simplex_lower c (x k)
      (hpos k) (hsum k) (hcost k)
    apply (le_sub_iff_add_le).mpr
    apply le_of_mul_le_mul_left ?_ hn
    have hcancel : ((k : ℝ) * δ / (n : ℝ)) * (n : ℝ) =
        (k : ℝ) * δ := div_mul_cancel₀ _ (ne_of_gt hn)
    nlinarith
  have hexp : (n : ℝ) * karmarkarCost c (x k) ≤
      (n : ℝ) * karmarkarCost c (x 0) *
        Real.exp (-(k : ℝ) * δ / (n : ℝ)) := by
    calc
      (n : ℝ) * karmarkarCost c (x k) =
          Real.exp (Real.log ((n : ℝ) * karmarkarCost c (x k))) :=
        (Real.exp_log (mul_pos hn (hcost k))).symm
      _ ≤ Real.exp (Real.log ((n : ℝ) * karmarkarCost c (x 0)) -
          (k : ℝ) * δ / (n : ℝ)) := Real.exp_le_exp.mpr hlog
      _ = (n : ℝ) * karmarkarCost c (x 0) *
          Real.exp (-(k : ℝ) * δ / (n : ℝ)) := by
        rw [show Real.log ((n : ℝ) * karmarkarCost c (x 0)) -
          (k : ℝ) * δ / (n : ℝ) =
          Real.log ((n : ℝ) * karmarkarCost c (x 0)) +
            (-(k : ℝ) * δ / (n : ℝ)) by ring,
          Real.exp_add, Real.exp_log (mul_pos hn (hcost 0))]
  apply le_of_mul_le_mul_left ?_ hn
  convert hexp using 1
  ring

/-- Conditional iteration theorem for actual inverse-projective updates.
The remaining geometric hypotheses are the projected-cost ratio and the
quarter-radius coordinate bounds for each projected step. -/
theorem karmarkar_projective_run_rate [NeZero n]
    (hn2 : 2 ≤ n) (c : Fin n → ℝ)
    (x y : ℕ → Fin n → ℝ)
    (hinit : x 0 = karmarkarCenter n)
    (hstep : ∀ k, x (k + 1) = karmarkarInverse (x k) (y k))
    (hxpos : ∀ k i, 0 < x k i)
    (hypos : ∀ k i, 0 < y k i)
    (hxsum : ∀ k, ∑ i, x k i = 1)
    (hysum : ∀ k, ∑ i, y k i = 1)
    (hcost : ∀ k, 0 < karmarkarCost c (x k))
    (hS : ∀ k, 0 < karmarkarDenominator (x k) (y k))
    (hW : ∀ k, 0 < karmarkarWeightedCost (x k) c (y k))
    (hratio : ∀ k, karmarkarWeightedCost (x k) c (y k) /
      karmarkarWeightedCost (x k) c (karmarkarCenter n) ≤
        1 - 1 / (4 * ((n : ℝ) - 1)))
    (hlower : ∀ k i, -(1 / 4 : ℝ) ≤ (n : ℝ) * y k i - 1)
    (hsq : ∀ k, ∑ i, ((n : ℝ) * y k i - 1) ^ 2 ≤ (1 / 8 : ℝ))
    (k : ℕ) :
    karmarkarCost c (x k) ≤ karmarkarCost c (x 0) *
      Real.exp (-(k : ℝ) / (12 * (n : ℝ))) := by
  have hdrop (j : ℕ) :
      karmarkarPotential c (x (j + 1)) ≤
        karmarkarPotential c (x j) - (1 / 12 : ℝ) := by
    rw [hstep j]
    exact karmarkar_projective_step_drop_of_coordinates hn2
      (x j) c (y j) (hxpos j) (hypos j) (hxsum j) (hysum j)
      (hS j) (hW j) (hcost j) (hratio j) (hlower j) (hsq j)
  have hcenter : karmarkarPotential c (x 0) =
      (n : ℝ) * Real.log ((n : ℝ) * karmarkarCost c (x 0)) := by
    rw [hinit]
    exact karmarkarPotential_center c (by simpa [hinit] using hcost 0)
  have hrate := karmarkar_objective_exponential_rate c x (1 / 12 : ℝ)
    hxpos hxsum hcost hcenter hdrop k
  have hexp : -(k : ℝ) * (1 / 12 : ℝ) / (n : ℝ) =
      -(k : ℝ) / (12 * (n : ℝ)) := by ring
  simpa only [hexp] using hrate

/-- The explicit threshold calculation behind the polynomial iteration
count. A separate rational-vertex argument must furnish `D`. -/
theorem karmarkar_exponential_crosses_gap [NeZero n]
    (c : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (D : ℝ)
    (hD : 0 < D) (hcost0 : 0 < karmarkarCost c (x 0))
    (hrate : ∀ k, karmarkarCost c (x k) ≤
      karmarkarCost c (x 0) *
        Real.exp (-(k : ℝ) / (12 * (n : ℝ))))
    (k : ℕ)
    (hk : 12 * (n : ℝ) * Real.log (D * karmarkarCost c (x 0)) <
      (k : ℝ)) :
    karmarkarCost c (x k) < 1 / D := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hden : 0 < 12 * (n : ℝ) := by positivity
  have hlog : -(k : ℝ) / (12 * (n : ℝ)) <
      -Real.log (D * karmarkarCost c (x 0)) := by
    have h : Real.log (D * karmarkarCost c (x 0)) <
        (k : ℝ) / (12 * (n : ℝ)) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith [hk]
    convert neg_lt_neg h using 1
    ring
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_neg, Real.exp_log (mul_pos hD hcost0)] at hexp
  have hmul := mul_lt_mul_of_pos_left hexp hcost0
  calc
    karmarkarCost c (x k) ≤ karmarkarCost c (x 0) *
        Real.exp (-(k : ℝ) / (12 * (n : ℝ))) := hrate k
    _ < karmarkarCost c (x 0) * (D * karmarkarCost c (x 0))⁻¹ := hmul
    _ = 1 / D := by
      field_simp [ne_of_gt hD, ne_of_gt hcost0]

end QuasiNewtonConvergence

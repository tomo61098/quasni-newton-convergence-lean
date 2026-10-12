import QuasiNewtonConvergence.KarmarkarProjective
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Perm.Sign

/-!
# Arithmetic bounds used in Karmarkar's bit-complexity proof

These lemmas isolate two discrete facts: a positive objective at a rational
vertex with a common integer denominator has a positive gap, and dyadic
coordinates with bounded numerators have bounded binary storage length.
Cramer's rule supplies the signed common denominator for nonsingular
integer systems. Connecting arbitrary LP vertices to such systems and
implementing finite-precision projective steps are separate obligations.
-/

noncomputable section
namespace QuasiNewtonConvergence

open scoped BigOperators
open scoped Matrix

/-- A rational point with a common positive integer denominator. -/
def karmarkarCommonDenominatorPoint {n : ℕ}
    (q : Fin n → ℤ) (D : ℕ) : Fin n → ℝ :=
  fun i => (q i : ℝ) / (D : ℝ)

/-- An integer objective evaluated at a common-denominator rational point
is an integer divided by that denominator. -/
theorem karmarkar_integer_objective_common_denominator
    {n : ℕ} (c q : Fin n → ℤ) (D : ℕ) :
    karmarkarCost (fun i => (c i : ℝ))
      (karmarkarCommonDenominatorPoint q D) =
      ((∑ i, c i * q i : ℤ) : ℝ) / (D : ℝ) := by
  unfold karmarkarCost karmarkarCommonDenominatorPoint
  calc
    (∑ i, (c i : ℝ) * ((q i : ℝ) / (D : ℝ))) =
        (∑ i, (c i : ℝ) * (q i : ℝ)) / (D : ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ((∑ i, c i * q i : ℤ) : ℝ) / (D : ℝ) := by
      norm_cast

/-- The rational-vertex gap: a positive integer objective numerator is at
least one, hence a positive objective is at least `1 / D`. -/
theorem karmarkar_positive_vertex_gap
    {n : ℕ} (c q : Fin n → ℤ) (D : ℕ)
    (hD : 0 < D)
    (hpositive : 0 < karmarkarCost (fun i => (c i : ℝ))
      (karmarkarCommonDenominatorPoint q D)) :
    1 / (D : ℝ) ≤ karmarkarCost (fun i => (c i : ℝ))
      (karmarkarCommonDenominatorPoint q D) := by
  rw [karmarkar_integer_objective_common_denominator] at hpositive ⊢
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hnumreal : (0 : ℝ) < ((∑ i, c i * q i : ℤ) : ℝ) :=
    (div_pos_iff_of_pos_right hDreal).mp hpositive
  have hnum : 0 < ∑ i, c i * q i := by exact_mod_cast hnumreal
  have hnum1 : (1 : ℤ) ≤ ∑ i, c i * q i := hnum
  have hnumreal : (1 : ℝ) ≤ ((∑ i, c i * q i : ℤ) : ℝ) := by
    exact_mod_cast hnum1
  exact div_le_div_of_nonneg_right hnumreal hDreal.le

/-- Leibniz' determinant formula gives an explicit coefficient-size bound.
It is weaker than Hadamard's inequality but still polynomial in bit length:
the determinant has at most `log₂(n!) + n log₂(B)` bits. -/
theorem karmarkar_integer_determinant_bound
    (n B : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hentry : ∀ i j, |M i j| ≤ (B : ℤ)) :
    |M.det| ≤ ((n.factorial : ℕ) : ℤ) * (B : ℤ) ^ n := by
  have hprod (σ : Equiv.Perm (Fin n)) :
      |∏ i, M (σ i) i| ≤ (B : ℤ) ^ n := by
    rw [Finset.abs_prod]
    calc
      (∏ i, |M (σ i) i|) ≤ ∏ _i : Fin n, (B : ℤ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          exact hentry (σ i) i
      _ = (B : ℤ) ^ n := by simp
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℤ) * ∏ i, M (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin n),
          |((Equiv.Perm.sign σ : ℤ) : ℤ) * ∏ i, M (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (B : ℤ) ^ n := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa [abs_mul, Equiv.Perm.sign_abs] using hprod σ
    _ = ((n.factorial : ℕ) : ℤ) * (B : ℤ) ^ n := by
      simp [Fintype.card_perm]

/-- If every integer matrix entry has at most `b` magnitude bits, its
determinant is bounded by a power of two with a polynomial exponent. -/
theorem karmarkar_determinant_polynomial_bit_bound
    (n B b : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hentry : ∀ i j, |M i j| ≤ (B : ℤ))
    (hB : B ≤ 2 ^ b) :
    |M.det| ≤ ((2 ^ (n * (n + b)) : ℕ) : ℤ) := by
  have hdet := karmarkar_integer_determinant_bound n B M hentry
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have hnat : n.factorial * B ^ n ≤ 2 ^ (n * (n + b)) := by
    calc
      n.factorial * B ^ n ≤ n ^ n * B ^ n :=
        Nat.mul_le_mul_right _ (Nat.factorial_le_pow n)
      _ ≤ n ^ n * (2 ^ b) ^ n := by
        gcongr
      _ ≤ (2 ^ n) ^ n * (2 ^ b) ^ n := by
        gcongr
      _ = 2 ^ (n * (n + b)) := by
        calc
          (2 ^ n) ^ n * (2 ^ b) ^ n =
              (2 ^ n * 2 ^ b) ^ n := (mul_pow _ _ _).symm
          _ = (2 ^ (n + b)) ^ n := by rw [pow_add]
          _ = 2 ^ ((n + b) * n) := by rw [pow_mul]
          _ = 2 ^ (n * (n + b)) := by congr 1; ring
  exact hdet.trans (by exact_mod_cast hnat)

/-- A denominator bounded by `2^P` gives a gap at least `2^{-P}`. -/
theorem karmarkar_positive_gap_from_bit_bound
    {n : ℕ} (c q : Fin n → ℤ) (D P : ℕ)
    (hD : 0 < D) (hDbound : D ≤ 2 ^ P)
    (hpositive : 0 < karmarkarCost (fun i => (c i : ℝ))
      (karmarkarCommonDenominatorPoint q D)) :
    1 / ((2 ^ P : ℕ) : ℝ) ≤
      karmarkarCost (fun i => (c i : ℝ))
        (karmarkarCommonDenominatorPoint q D) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hDboundreal : (D : ℝ) ≤ ((2 ^ P : ℕ) : ℝ) := by
    exact_mod_cast hDbound
  exact (one_div_le_one_div_of_le hDreal hDboundreal).trans
    (karmarkar_positive_vertex_gap c q D hD hpositive)

/-- Cramer's rule supplies a common integer denominator for any solution
of a nonsingular integer linear system. -/
theorem karmarkar_cramer_common_denominator
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℝ)
    (hdet : M.det ≠ 0)
    (hsol : (M.map (Int.castRingHom ℝ)) *ᵥ x =
      (fun i => (b i : ℝ))) :
    ∃ q : Fin n → ℤ,
      ∀ i, x i = (q i : ℝ) / (M.det : ℝ) := by
  let MR : Matrix (Fin n) (Fin n) ℝ := M.map (Int.castRingHom ℝ)
  let bR : Fin n → ℝ := fun i => (b i : ℝ)
  let q : Fin n → ℤ := M.cramer b
  have hqcast (i : Fin n) :
      (q i : ℝ) = (MR.cramer bR) i := by
    change ((M.updateCol i b).det : ℝ) =
      ((M.map (Int.castRingHom ℝ)).updateCol i
        (fun j => (b j : ℝ))).det
    rw [Int.cast_det]
    congr 1
    exact Matrix.map_updateCol (M := M) (j := i) (c := b)
      (Int.castRingHom ℝ)
  have hdetcast : MR.det = (M.det : ℝ) := by
    simpa [MR] using (Int.cast_det M (R := ℝ)).symm
  have hcramer : MR *ᵥ MR.cramer bR = MR.det • bR :=
    Matrix.mulVec_cramer MR bR
  have hMRdet : MR.det ≠ 0 := by
    rw [hdetcast]
    exact_mod_cast hdet
  have hxin : x = (MR.det)⁻¹ • MR.cramer bR := by
    apply Matrix.mulVec_injective_of_det_ne_zero hMRdet
    rw [Matrix.mulVec_smul, hcramer]
    change MR *ᵥ x = MR.det⁻¹ • (MR.det • bR)
    rw [← smul_assoc]
    simp [hMRdet]
    exact hsol
  refine ⟨q, ?_⟩
  intro i
  have hi := congrFun hxin i
  simpa [hqcast, hdetcast, div_eq_mul_inv, mul_comm] using hi

/-- A nonnegative dyadic numerator at most `2^P` is strictly below the
`P+1`-bit threshold. -/
theorem karmarkar_dyadic_numerator_bits
    (P q : ℕ) (hq : q ≤ 2 ^ P) :
    q < 2 ^ (P + 1) := by
  have hp : 0 < 2 ^ P := pow_pos (by decide) _
  rw [pow_succ]
  omega

/-- If a transformed point lies between `3U/5` and `U` in every
coordinate, the inverse projective map keeps at least three fifths of each
old coordinate. This is the interior-margin estimate used when rounding. -/
theorem karmarkar_inverse_coordinate_retention
    {n : ℕ} [NeZero n] (a y : Fin n → ℝ) (U : ℝ)
    (ha : ∀ i, 0 < a i) (hasum : ∑ i, a i = 1)
    (hU : 0 < U)
    (hylower : ∀ i, (3 / 5 : ℝ) * U ≤ y i)
    (hyupper : ∀ i, y i ≤ U)
    (i : Fin n) :
    (3 / 5 : ℝ) * a i ≤ karmarkarInverse a y i := by
  have hypos (j : Fin n) : 0 < y j :=
    lt_of_lt_of_le (mul_pos (by norm_num) hU) (hylower j)
  have hdenpos := karmarkarDenominator_pos a y ha hypos
  have hdenle : karmarkarDenominator a y ≤ U := by
    calc
      karmarkarDenominator a y = ∑ j, a j * y j := rfl
      _ ≤ ∑ j, a j * U :=
        Finset.sum_le_sum (fun j hj =>
          mul_le_mul_of_nonneg_left (hyupper j) (ha j).le)
      _ = U := by rw [← Finset.sum_mul, hasum, one_mul]
  unfold karmarkarInverse
  apply (le_div_iff₀ hdenpos).mpr
  have hnum := mul_le_mul_of_nonneg_left (hylower i) (ha i).le
  have hdenmul := mul_le_mul_of_nonneg_left hdenle
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5) (ha i).le)
  nlinarith [hdenmul]

/-- A repeated three-fifths retention bound prevents any coordinate from
becoming smaller than an exponentially small quantity in the step count. -/
theorem karmarkar_coordinate_margin_after_steps
    {n : ℕ} [NeZero n] (a : ℕ → Fin n → ℝ)
    (hinit : ∀ i, a 0 i = 1 / (n : ℝ))
    (hretain : ∀ k i, (3 / 5 : ℝ) * a k i ≤ a (k + 1) i)
    (k : ℕ) (i : Fin n) :
    (3 / 5 : ℝ) ^ k / (n : ℝ) ≤ a k i := by
  induction k with
  | zero => simpa using (hinit i).ge
  | succ k ih =>
      have hmul := mul_le_mul_of_nonneg_left ih
        (by norm_num : (0 : ℝ) ≤ 3 / 5)
      have hnext := hretain k i
      calc
        (3 / 5 : ℝ) ^ (k + 1) / (n : ℝ) =
            (3 / 5 : ℝ) * ((3 / 5 : ℝ) ^ k / (n : ℝ)) := by
          rw [pow_succ]
          ring
        _ ≤ (3 / 5 : ℝ) * a k i := hmul
        _ ≤ a (k + 1) i := hnext

/-- A simpler binary-scale margin follows from `3/5 ≥ 1/2`. -/
theorem karmarkar_binary_coordinate_margin
    {n : ℕ} [NeZero n] (a : ℕ → Fin n → ℝ)
    (hinit : ∀ i, a 0 i = 1 / (n : ℝ))
    (hretain : ∀ k i, (3 / 5 : ℝ) * a k i ≤ a (k + 1) i)
    (k : ℕ) (i : Fin n) :
    (1 / 2 : ℝ) ^ k / (n : ℝ) ≤ a k i := by
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hpow : (1 / 2 : ℝ) ^ k ≤ (3 / 5 : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 3 / 5) _
  exact (div_le_div_of_nonneg_right hpow hn.le).trans
    (karmarkar_coordinate_margin_after_steps a hinit hretain k i)

end QuasiNewtonConvergence

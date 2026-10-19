module

public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Hessian-form quasi-Newton updates

The Broyden class uses a scalar parameter `φ`: zero gives BFGS and one gives
DFP. SR1 is a separate rank-one formula and can be skipped when its
denominator vanishes.
-/

noncomputable section

namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strict positivity of a Hessian approximation's quadratic form. -/
def PositiveDefinite (B : E →ₗ[ℝ] E) : Prop :=
  ∀ z : E, z ≠ 0 → 0 < inner ℝ (B z) z

/-- The Hessian form of the BFGS rank-two update. -/
def bfgsUpdate (B : E →ₗ[ℝ] E) (s y : E) (z : E) : E :=
  B z - (inner ℝ (B s) z / inner ℝ (B s) s) • B s +
    (inner ℝ y z / inner ℝ y s) • y

/-- BFGS satisfies the secant equation when its denominators are nonzero. -/
theorem bfgsUpdate_secant (B : E →ₗ[ℝ] E) (s y : E)
    (hBs : inner ℝ (B s) s ≠ 0) (hys : inner ℝ y s ≠ 0) :
    bfgsUpdate B s y s = y := by
  simp [bfgsUpdate, div_self hBs, div_self hys]

theorem bfgsUpdate_secant_of_curvature (B : E →ₗ[ℝ] E) (s y : E)
    (hB : PositiveDefinite B) (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) :
    bfgsUpdate B s y s = y :=
  bfgsUpdate_secant B s y (ne_of_gt (hB s hs)) (ne_of_gt hcurv)

/-- The vector orthogonal to the secant displacement in the Broyden correction. -/
def broydenVector (B : E →ₗ[ℝ] E) (s y : E) : E :=
  (1 / inner ℝ y s) • y - (1 / inner ℝ (B s) s) • B s

/-- The Hessian-form Broyden class: `φ = 0` is BFGS and `φ = 1` is DFP. -/
def broydenUpdate (B : E →ₗ[ℝ] E) (s y : E) (φ : ℝ) (z : E) : E :=
  bfgsUpdate B s y z +
    (φ * inner ℝ (B s) s * inner ℝ (broydenVector B s y) z) •
      broydenVector B s y

/-- The DFP Hessian update is the endpoint of the Broyden class. -/
def dfpUpdate (B : E →ₗ[ℝ] E) (s y : E) (z : E) : E :=
  broydenUpdate B s y 1 z

/-- The SR1 Hessian update. Its denominator can have either sign. -/
def sr1Update (B : E →ₗ[ℝ] E) (s y : E) (z : E) : E :=
  let residual := y - B s
  B z + (inner ℝ residual z / inner ℝ residual s) • residual

/-- Skip SR1 when its denominator is zero. -/
def sr1UpdateOrSkip (B : E →ₗ[ℝ] E) (s y : E) (z : E) : E :=
  if inner ℝ (y - B s) s = 0 then B z else sr1Update B s y z

/-- A rank-one linear map built from the real inner product. -/
def rankOne (a b : E) : E →ₗ[ℝ] E where
  toFun z := (inner ℝ a z) • b
  map_add' z w := by simp [inner_add_right, add_smul]
  map_smul' c z := by simp [real_inner_smul_right, smul_smul]

/-- Bundled BFGS Hessian update. -/
def bfgsUpdateMap (B : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  B - (1 / inner ℝ (B s) s) • rankOne (B s) (B s) +
    (1 / inner ℝ y s) • rankOne y y

/-- Bundled Broyden-class Hessian update. -/
def broydenUpdateMap (B : E →ₗ[ℝ] E) (s y : E) (φ : ℝ) : E →ₗ[ℝ] E :=
  bfgsUpdateMap B s y +
    (φ * inner ℝ (B s) s) • rankOne (broydenVector B s y) (broydenVector B s y)

def dfpUpdateMap (B : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  broydenUpdateMap B s y 1

def sr1UpdateMap (B : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  B + (1 / inner ℝ (y - B s) s) • rankOne (y - B s) (y - B s)

def sr1UpdateOrSkipMap (B : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  if inner ℝ (y - B s) s = 0 then B else sr1UpdateMap B s y

/-- Textbook SR1 safeguard: skip when the denominator is too small relative
to the displacement and secant residual. -/
def sr1UpdateSafeguardedMap (ρ : ℝ) (B : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  if ρ * ‖s‖ * ‖y - B s‖ ≤ |inner ℝ (y - B s) s| ∧
      inner ℝ (y - B s) s ≠ 0 then
    sr1UpdateMap B s y
  else B

@[simp] theorem bfgsUpdateMap_apply (B : E →ₗ[ℝ] E) (s y z : E) :
    bfgsUpdateMap B s y z = bfgsUpdate B s y z := by
  simp [bfgsUpdateMap, bfgsUpdate, rankOne, div_eq_mul_inv, smul_smul, mul_comm]

@[simp] theorem broydenUpdateMap_apply (B : E →ₗ[ℝ] E) (s y : E) (φ : ℝ)
    (z : E) : broydenUpdateMap B s y φ z = broydenUpdate B s y φ z := by
  simp [broydenUpdateMap, broydenUpdate, rankOne, smul_smul]

@[simp] theorem dfpUpdateMap_apply (B : E →ₗ[ℝ] E) (s y z : E) :
    dfpUpdateMap B s y z = dfpUpdate B s y z := by
  simp [dfpUpdateMap, dfpUpdate]

@[simp] theorem sr1UpdateMap_apply (B : E →ₗ[ℝ] E) (s y z : E) :
    sr1UpdateMap B s y z = sr1Update B s y z := by
  simp [sr1UpdateMap, sr1Update, rankOne, smul_smul, div_eq_mul_inv, mul_comm]

@[simp] theorem sr1UpdateOrSkipMap_apply (B : E →ₗ[ℝ] E) (s y z : E) :
    sr1UpdateOrSkipMap B s y z = sr1UpdateOrSkip B s y z := by
  by_cases h : inner ℝ (y - B s) s = 0
  · simp [sr1UpdateOrSkipMap, sr1UpdateOrSkip, h]
  · simp [sr1UpdateOrSkipMap, sr1UpdateOrSkip, h]

/-- Update formulas available to a quasi-Newton run. SR1 uses the zero-denominator
skip rule; the Broyden parameter may vary between iterations. -/
inductive HessianUpdateMethod where
  | bfgs
  | dfp
  | sr1 (ρ : ℝ)
  | broyden (φ : ℝ)

def hessianUpdate (method : HessianUpdateMethod)
    (B : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  match method with
  | .bfgs => bfgsUpdateMap B s y
  | .dfp => dfpUpdateMap B s y
  | .sr1 ρ => sr1UpdateSafeguardedMap ρ B s y
  | .broyden φ => broydenUpdateMap B s y φ

theorem broydenVector_orthogonal (B : E →ₗ[ℝ] E) (s y : E)
    (hBs : inner ℝ (B s) s ≠ 0) (hys : inner ℝ y s ≠ 0) :
    inner ℝ (broydenVector B s y) s = 0 := by
  simp [broydenVector, inner_sub_left, real_inner_smul_left,
    one_div, inv_mul_cancel₀ hys, inv_mul_cancel₀ hBs]

theorem broydenUpdate_secant (B : E →ₗ[ℝ] E) (s y : E) (φ : ℝ)
    (hBs : inner ℝ (B s) s ≠ 0) (hys : inner ℝ y s ≠ 0) :
    broydenUpdate B s y φ s = y := by
  simp [broydenUpdate, broydenVector_orthogonal B s y hBs hys,
    bfgsUpdate_secant B s y hBs hys]

theorem dfpUpdate_secant (B : E →ₗ[ℝ] E) (s y : E)
    (hBs : inner ℝ (B s) s ≠ 0) (hys : inner ℝ y s ≠ 0) :
    dfpUpdate B s y s = y :=
  broydenUpdate_secant B s y 1 hBs hys

theorem sr1Update_secant (B : E →ₗ[ℝ] E) (s y : E)
    (hr : inner ℝ (y - B s) s ≠ 0) :
    sr1Update B s y s = y := by
  simp [sr1Update, div_self hr]

theorem sr1UpdateOrSkip_secant (B : E →ₗ[ℝ] E) (s y : E)
    (hr : inner ℝ (y - B s) s ≠ 0) :
    sr1UpdateOrSkip B s y s = y := by
  simp [sr1UpdateOrSkip, hr, sr1Update_secant B s y hr]

theorem sr1UpdateOrSkip_eq_old (B : E →ₗ[ℝ] E) (s y z : E)
    (hr : inner ℝ (y - B s) s = 0) :
    sr1UpdateOrSkip B s y z = B z := by
  simp [sr1UpdateOrSkip, hr]

theorem sr1UpdateSafeguardedMap_secant (ρ : ℝ)
    (B : E →ₗ[ℝ] E) (s y : E)
    (hguard : ρ * ‖s‖ * ‖y - B s‖ ≤ |inner ℝ (y - B s) s| ∧
      inner ℝ (y - B s) s ≠ 0) :
    sr1UpdateSafeguardedMap ρ B s y s = y := by
  simp [sr1UpdateSafeguardedMap, hguard,
    sr1Update_secant B s y hguard.2]

theorem sr1UpdateSafeguardedMap_skip (ρ : ℝ)
    (B : E →ₗ[ℝ] E) (s y : E)
    (hskip : ¬(ρ * ‖s‖ * ‖y - B s‖ ≤ |inner ℝ (y - B s) s| ∧
      inner ℝ (y - B s) s ≠ 0)) :
    sr1UpdateSafeguardedMap ρ B s y = B := by
  simp [sr1UpdateSafeguardedMap, hskip]

/-- Symmetry of a Hessian approximation. -/
def SymmetricHessian (B : E →ₗ[ℝ] E) : Prop :=
  ∀ u v, inner ℝ (B u) v = inner ℝ u (B v)

/-- The BFGS quadratic form is a nonnegative old-metric remainder plus
one strictly positive secant term. -/
theorem bfgs_quadratic_identity (B : E →ₗ[ℝ] E) (s y z : E)
    (hSym : SymmetricHessian B)
    (hBs : inner ℝ (B s) s ≠ 0) :
    inner ℝ (bfgsUpdate B s y z) z =
      inner ℝ (B (z - (inner ℝ (B s) z / inner ℝ (B s) s) • s))
        (z - (inner ℝ (B s) z / inner ℝ (B s) s) • s) +
      (inner ℝ y z) ^ 2 / inner ℝ y s := by
  have hswap : inner ℝ (B z) s = inner ℝ (B s) z := by
    rw [hSym z s, real_inner_comm]
  simp only [bfgsUpdate, inner_add_left, inner_sub_left,
    real_inner_smul_left, map_sub, map_smul, inner_sub_right,
    real_inner_smul_right]
  rw [hswap]
  field_simp
  ring

/-- BFGS preserves positive definiteness when the old Hessian approximation
is symmetric positive definite and the secant pair has positive curvature. -/
theorem bfgsUpdate_positive (B : E →ₗ[ℝ] E) (s y z : E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) (hz : z ≠ 0) :
    0 < inner ℝ (bfgsUpdate B s y z) z := by
  let t : ℝ := inner ℝ (B s) z / inner ℝ (B s) s
  let v : E := z - t • s
  have hBs : inner ℝ (B s) s ≠ 0 := ne_of_gt (hB s hs)
  have hid := bfgs_quadratic_identity B s y z hSym hBs
  change inner ℝ (bfgsUpdate B s y z) z =
    inner ℝ (B v) v + (inner ℝ y z) ^ 2 / inner ℝ y s at hid
  rw [hid]
  by_cases hv : v = 0
  · have hzt : z = t • s := sub_eq_zero.mp hv
    have ht : t ≠ 0 := by
      intro ht
      apply hz
      simpa [ht] using hzt
    have hyz : inner ℝ y z ≠ 0 := by
      rw [hzt, real_inner_smul_right]
      exact mul_ne_zero ht (ne_of_gt hcurv)
    simp only [hv, map_zero, inner_zero_left, zero_add]
    exact div_pos (sq_pos_of_ne_zero hyz) hcurv
  · exact add_pos_of_pos_of_nonneg (hB v hv)
      (div_nonneg (sq_nonneg _) hcurv.le)

/-- A nonnegative Broyden correction cannot spoil positivity of BFGS. -/
theorem broydenUpdate_positive (B : E →ₗ[ℝ] E) (s y z : E) (φ : ℝ)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s)
    (hφ : 0 ≤ φ) (hz : z ≠ 0) :
    0 < inner ℝ (broydenUpdate B s y φ z) z := by
  have hBs : 0 < inner ℝ (B s) s := hB s hs
  have hbase := bfgsUpdate_positive B s y z hB hSym hs hcurv hz
  have hcorrection : 0 ≤ φ * inner ℝ (B s) s *
      inner ℝ (broydenVector B s y) z *
      inner ℝ (broydenVector B s y) z := by
    nlinarith [mul_nonneg (mul_nonneg hφ hBs.le)
      (sq_nonneg (inner ℝ (broydenVector B s y) z))]
  simp only [broydenUpdate, inner_add_left, real_inner_smul_left]
  nlinarith

theorem dfpUpdate_positive (B : E →ₗ[ℝ] E) (s y z : E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) (hz : z ≠ 0) :
    0 < inner ℝ (dfpUpdate B s y z) z := by
  exact broydenUpdate_positive B s y z 1 hB hSym hs hcurv (by norm_num) hz

/-- BFGS preserves symmetry of the Hessian approximation. -/
theorem bfgsUpdate_symmetric (B : E →ₗ[ℝ] E) (s y z w : E)
    (hSym : SymmetricHessian B) :
    inner ℝ (bfgsUpdate B s y z) w =
      inner ℝ z (bfgsUpdate B s y w) := by
  simp only [bfgsUpdate, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hSym z w, real_inner_comm z (B s), real_inner_comm z y]
  ring

/-- Every Broyden-class correction is symmetric. -/
theorem broydenUpdate_symmetric (B : E →ₗ[ℝ] E) (s y z w : E) (φ : ℝ)
    (hSym : SymmetricHessian B) :
    inner ℝ (broydenUpdate B s y φ z) w =
      inner ℝ z (broydenUpdate B s y φ w) := by
  simp only [broydenUpdate, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [bfgsUpdate_symmetric B s y z w hSym,
    real_inner_comm z (broydenVector B s y)]
  ring

theorem dfpUpdate_symmetric (B : E →ₗ[ℝ] E) (s y z w : E)
    (hSym : SymmetricHessian B) :
    inner ℝ (dfpUpdate B s y z) w = inner ℝ z (dfpUpdate B s y w) :=
  broydenUpdate_symmetric B s y z w 1 hSym

theorem sr1Update_symmetric (B : E →ₗ[ℝ] E) (s y z w : E)
    (hSym : SymmetricHessian B) :
    inner ℝ (sr1Update B s y z) w = inner ℝ z (sr1Update B s y w) := by
  simp only [sr1Update, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hSym z w, real_inner_comm z (y - B s)]
  ring

theorem bfgsUpdateMap_positive (B : E →ₗ[ℝ] E) (s y : E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) :
    PositiveDefinite (bfgsUpdateMap B s y) := by
  intro z hz
  simpa using bfgsUpdate_positive B s y z hB hSym hs hcurv hz

theorem broydenUpdateMap_positive (B : E →ₗ[ℝ] E) (s y : E) (φ : ℝ)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) (hφ : 0 ≤ φ) :
    PositiveDefinite (broydenUpdateMap B s y φ) := by
  intro z hz
  simpa using broydenUpdate_positive B s y z φ hB hSym hs hcurv hφ hz

theorem dfpUpdateMap_positive (B : E →ₗ[ℝ] E) (s y : E)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) :
    PositiveDefinite (dfpUpdateMap B s y) := by
  intro z hz
  simpa using dfpUpdate_positive B s y z hB hSym hs hcurv hz

theorem bfgsUpdateMap_symmetric (B : E →ₗ[ℝ] E) (s y : E)
    (hSym : SymmetricHessian B) :
    SymmetricHessian (bfgsUpdateMap B s y) := by
  intro z w
  simpa using bfgsUpdate_symmetric B s y z w hSym

theorem broydenUpdateMap_symmetric (B : E →ₗ[ℝ] E) (s y : E) (φ : ℝ)
    (hSym : SymmetricHessian B) :
    SymmetricHessian (broydenUpdateMap B s y φ) := by
  intro z w
  simpa using broydenUpdate_symmetric B s y z w φ hSym

theorem dfpUpdateMap_symmetric (B : E →ₗ[ℝ] E) (s y : E)
    (hSym : SymmetricHessian B) :
    SymmetricHessian (dfpUpdateMap B s y) := by
  intro z w
  simpa using dfpUpdate_symmetric B s y z w hSym

/-- Methods whose Hessian correction is a nonnegative Broyden correction.
SR1 is excluded because it need not preserve positive definiteness. -/
def NonnegativeBroyden : HessianUpdateMethod → Prop
  | .bfgs => True
  | .dfp => True
  | .sr1 _ => False
  | .broyden φ => 0 ≤ φ

theorem hessianUpdate_positive (method : HessianUpdateMethod)
    (B : E →ₗ[ℝ] E) (s y : E)
    (hmethod : NonnegativeBroyden method)
    (hB : PositiveDefinite B) (hSym : SymmetricHessian B)
    (hs : s ≠ 0) (hcurv : 0 < inner ℝ y s) :
    PositiveDefinite (hessianUpdate method B s y) := by
  cases method with
  | bfgs => exact bfgsUpdateMap_positive B s y hB hSym hs hcurv
  | dfp => exact dfpUpdateMap_positive B s y hB hSym hs hcurv
  | sr1 ρ => exact False.elim hmethod
  | broyden φ =>
    exact broydenUpdateMap_positive B s y φ hB hSym hs hcurv hmethod

theorem hessianUpdate_symmetric (method : HessianUpdateMethod)
    (B : E →ₗ[ℝ] E) (s y : E)
    (hmethod : NonnegativeBroyden method)
    (hSym : SymmetricHessian B) :
    SymmetricHessian (hessianUpdate method B s y) := by
  cases method with
  | bfgs => exact bfgsUpdateMap_symmetric B s y hSym
  | dfp => exact dfpUpdateMap_symmetric B s y hSym
  | sr1 ρ => exact False.elim hmethod
  | broyden φ => exact broydenUpdateMap_symmetric B s y φ hSym

/-- Every update in a nonnegative Broyden sequence remains symmetric
positive definite under positive secant curvature. -/
theorem broydenSequence_positive (B : ℕ → E →ₗ[ℝ] E)
    (method : ℕ → HessianUpdateMethod) (s y : ℕ → E)
    (hinitial : PositiveDefinite (B 0) ∧ SymmetricHessian (B 0))
    (hupdate : ∀ k, B (k + 1) = hessianUpdate (method k) (B k) (s k) (y k))
    (hmethod : ∀ k, NonnegativeBroyden (method k))
    (hs : ∀ k, s k ≠ 0)
    (hcurv : ∀ k, 0 < inner ℝ (y k) (s k)) :
    ∀ k, PositiveDefinite (B k) ∧ SymmetricHessian (B k) := by
  intro k
  induction k with
  | zero => exact hinitial
  | succ k ih =>
    rw [hupdate k]
    exact ⟨hessianUpdate_positive (method k) (B k) (s k) (y k)
      (hmethod k) ih.1 ih.2 (hs k) (hcurv k),
      hessianUpdate_symmetric (method k) (B k) (s k) (y k)
        (hmethod k) ih.2⟩

end QuasiNewtonConvergence

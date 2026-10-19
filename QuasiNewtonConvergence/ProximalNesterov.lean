module

public import QuasiNewtonConvergence.ProximalGradient

@[expose] public section

/-! The estimate-sequence proof for accelerated proximal gradient. -/

noncomputable section
namespace QuasiNewtonConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Jensen's inequality, used for the composite objective. -/
def SegmentConvex (F : E → ℝ) : Prop :=
  ∀ (x u : E) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    F ((1 - θ) • x + θ • u) ≤ (1 - θ) * F x + θ * F u

/-- One estimate-sequence step. The exact weight relation is
`(A+a)Lθ²=1`; the other two equations say `a=(A+a)θ`. -/
theorem proximalNesterov_step (f g : E → ℝ) (gradient : E → E)
    (L A a θ : ℝ) (_hL : 0 < L) (hA : 0 ≤ A) (ha : 0 < a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hweight : (A + a) * θ = a)
    (hexact : (A + a) * L * θ ^ 2 = 1)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hsegment : SegmentConvex (composite f g))
    (x z y x' z' u : E)
    (hy : y = (1 - θ) • x + θ • z)
    (hx : x' = (1 - θ) • x + θ • z')
    (hprox : ProximalOptimality g gradient L y x') :
    (A + a) * (composite f g x' - composite f g u) +
      ‖z' - u‖ ^ 2 / 2 ≤
        A * (composite f g x - composite f g u) + ‖z - u‖ ^ 2 / 2 := by
  let v := (1 - θ) • x + θ • u
  have hthree := proximal_three_point f g gradient L hsmooth hconvex
    y x' v hprox
  have hjensen := hsegment x u θ hθ0 hθ1
  change composite f g v ≤ _ at hjensen
  have hyvec : y - v = θ • (z - u) := by
    dsimp [v]
    rw [hy, smul_sub]
    abel
  have hxvec : x' - v = θ • (z' - u) := by
    dsimp [v]
    rw [hx, smul_sub]
    abel
  rw [hyvec, hxvec, norm_smul, norm_smul] at hthree
  simp only [Real.norm_eq_abs, abs_of_nonneg hθ0] at hthree
  have hAn : 0 ≤ A + a := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hthree hAn
  have hjscaled := mul_le_mul_of_nonneg_left hjensen hAn
  have hsplit : (A + a) * (1 - θ) = A := by nlinarith [hweight]
  have hquad : (A + a) *
      (L / 2 * ((θ * ‖z - u‖) ^ 2 - (θ * ‖z' - u‖) ^ 2)) =
      (‖z - u‖ ^ 2 - ‖z' - u‖ ^ 2) / 2 := by
    calc
      _ = ((A + a) * L * θ ^ 2) *
          ((‖z - u‖ ^ 2 - ‖z' - u‖ ^ 2) / 2) := by ring
      _ = _ := by rw [hexact]; ring
  have hlinear : (A + a) *
      ((1 - θ) * composite f g x + θ * composite f g u) =
      A * composite f g x + a * composite f g u := by
    calc
      _ = ((A + a) * (1 - θ)) * composite f g x +
          ((A + a) * θ) * composite f g u := by ring
      _ = _ := by rw [hsplit, hweight]
  rw [hquad] at hscaled
  rw [hlinear] at hjscaled
  linarith

/-- Telescoping the accelerated potential gives the weighted rate. -/
theorem proximalNesterov_weighted_rate (f g : E → ℝ)
    (gradient : E → E) (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hsegment : SegmentConvex (composite f g))
    (A a θ : ℕ → ℝ) (x z y : ℕ → E) (u : E)
    (hA0 : A 0 = 0) (hz0 : z 0 = x 0)
    (hAn : ∀ k, 0 ≤ A k) (han : ∀ k, 0 < a k)
    (hθ0 : ∀ k, 0 ≤ θ k) (hθ1 : ∀ k, θ k ≤ 1)
    (hAsucc : ∀ k, A (k + 1) = A k + a k)
    (hweight : ∀ k, (A k + a k) * θ k = a k)
    (hexact : ∀ k, (A k + a k) * L * (θ k) ^ 2 = 1)
    (hy : ∀ k, y k = (1 - θ k) • x k + θ k • z k)
    (hx : ∀ k, x (k + 1) = (1 - θ k) • x k + θ k • z (k + 1))
    (hprox : ∀ k, ProximalOptimality g gradient L (y k) (x (k + 1)))
    (n : ℕ) :
    A n * (composite f g (x n) - composite f g u) ≤
      ‖x 0 - u‖ ^ 2 / 2 := by
  have hpot (k : ℕ) : A k * (composite f g (x k) - composite f g u) +
      ‖z k - u‖ ^ 2 / 2 ≤ ‖x 0 - u‖ ^ 2 / 2 := by
    induction k with
    | zero => simp [hA0, hz0]
    | succ k ih =>
      have hs := proximalNesterov_step f g gradient L (A k) (a k) (θ k)
        hL (hAn k) (han k) (hθ0 k) (hθ1 k) (hweight k)
        (hexact k) hsmooth hconvex hsegment
        (x k) (z k) (y k) (x (k + 1)) (z (k + 1)) u
        (hy k) (hx k) (hprox k)
      rw [← hAsucc k] at hs
      linarith
  nlinarith [hpot n, sq_nonneg ‖z n - u‖]

/-- The exact accelerated weight equations force quadratic growth. -/
theorem proximalNesterov_weight_growth (L : ℝ) (hL : 0 < L)
    (A a θ : ℕ → ℝ) (hAn : ∀ k, 0 ≤ A k) (han : ∀ k, 0 < a k)
    (hAsucc : ∀ k, A (k + 1) = A k + a k)
    (hweight : ∀ k, (A k + a k) * θ k = a k)
    (hexact : ∀ k, (A k + a k) * L * (θ k) ^ 2 = 1)
    (n : ℕ) : (n : ℝ) ^ 2 / (4 * L) ≤ A n := by
  have hrec (k : ℕ) : L * (a k) ^ 2 = A (k + 1) := by
    calc
      L * (a k) ^ 2 =
          ((A k + a k) * L * (θ k) ^ 2) * (A k + a k) := by
        conv_lhs => rw [← hweight k]
        ring
      _ = A (k + 1) := by rw [hexact k, one_mul, hAsucc k]
  have hscaled (k : ℕ) : (k : ℝ) ^ 2 ≤ 4 * L * A k := by
    induction k with
    | zero => simpa using mul_nonneg (by positivity : 0 ≤ 4 * L) (hAn 0)
    | succ k ih =>
      let t := 2 * L * a k
      have ht : 0 < t := mul_pos (mul_pos (by norm_num) hL) (han k)
      have heq : t ^ 2 = 4 * L * A k + 2 * t := by
        have hr := congrArg (fun v : ℝ => 4 * L * v) (hrec k)
        rw [hAsucc k] at hr
        dsimp [t]
        nlinarith only [hr]
      have ht1 : 1 ≤ t := by
        have hnonneg := mul_nonneg (by positivity : 0 ≤ 4 * L) (hAn k)
        nlinarith
      have hkt : (k : ℝ) + 1 ≤ t := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [sq_nonneg (t - 1 - (k : ℝ))]
      have hsquare : ((k : ℝ) + 1) ^ 2 ≤ t ^ 2 :=
        pow_le_pow_left₀ (by positivity) hkt 2
      have hr := congrArg (fun v : ℝ => 4 * L * v) (hrec k)
      dsimp [t] at hsquare
      push_cast
      nlinarith only [hsquare, hr]
  exact (div_le_iff₀ (by positivity : 0 < 4 * L)).2 (by
    simpa only [mul_comm] using hscaled n)

/-- The usual explicit `O(1/n²)` form, with quadratic weight growth
derived from the accelerated weight equations. -/
theorem proximalNesterov_quadratic_rate (f g : E → ℝ)
    (gradient : E → E) (L : ℝ) (hL : 0 < L)
    (hsmooth : SmoothUpper f gradient L)
    (hconvex : ConvexFirstOrder f gradient)
    (hsegment : SegmentConvex (composite f g))
    (A a θ : ℕ → ℝ) (x z y : ℕ → E) (u : E)
    (hA0 : A 0 = 0) (hz0 : z 0 = x 0)
    (hAn : ∀ k, 0 ≤ A k) (han : ∀ k, 0 < a k)
    (hθ0 : ∀ k, 0 ≤ θ k) (hθ1 : ∀ k, θ k ≤ 1)
    (hAsucc : ∀ k, A (k + 1) = A k + a k)
    (hweight : ∀ k, (A k + a k) * θ k = a k)
    (hexact : ∀ k, (A k + a k) * L * (θ k) ^ 2 = 1)
    (hy : ∀ k, y k = (1 - θ k) • x k + θ k • z k)
    (hx : ∀ k, x (k + 1) = (1 - θ k) • x k + θ k • z (k + 1))
    (hprox : ∀ k, ProximalOptimality g gradient L (y k) (x (k + 1)))
    (hmin : ∀ v, composite f g u ≤ composite f g v)
    (n : ℕ) (hn : 0 < n) :
    composite f g (x n) - composite f g u ≤
      2 * L * ‖x 0 - u‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hw := proximalNesterov_weighted_rate f g gradient L hL
    hsmooth hconvex hsegment A a θ x z y u hA0 hz0 hAn han
    hθ0 hθ1 hAsucc hweight hexact hy hx hprox n
  have hgap : 0 ≤ composite f g (x n) - composite f g u :=
    sub_nonneg.mpr (hmin (x n))
  have hgr := proximalNesterov_weight_growth L hL A a θ hAn han
    hAsucc hweight hexact n
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul := mul_le_mul_of_nonneg_right hgr hgap
  have hbound : ((n : ℝ) ^ 2 / (4 * L)) *
      (composite f g (x n) - composite f g u) ≤
      ‖x 0 - u‖ ^ 2 / 2 := le_trans hmul hw
  apply (le_div_iff₀ (sq_pos_of_pos hnR)).2
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp at hbound ⊢
  nlinarith

omit [InnerProductSpace ℝ E] in
/-- Restarting an accelerated proximal run of length `N` gives a geometric
rate whenever the composite objective has quadratic growth at its minimum.
`hblock` is the bound furnished by `proximalNesterov_quadratic_rate` for each
inner run. -/
theorem restartedProximalNesterov_strong_rate (F : E → ℝ)
    (L μ N : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hN : 0 < N)
    (u : E) (x : ℕ → E)
    (hgrowth : ∀ v, μ / 2 * ‖v - u‖ ^ 2 ≤ F v - F u)
    (hblock : ∀ k, F (x (k + 1)) - F u ≤
      2 * L * ‖x k - u‖ ^ 2 / N ^ 2)
    (hcontract : 4 * L < μ * N ^ 2)
    (k : ℕ) :
    (F (x k) - F u ≤
      (4 * L / (μ * N ^ 2)) ^ k * (F (x 0) - F u)) ∧
      4 * L / (μ * N ^ 2) < 1 := by
  let q := 4 * L / (μ * N ^ 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one (by positivity : 0 < μ * N ^ 2)).2 hcontract
  have hstep (j : ℕ) : F (x (j + 1)) - F u ≤ q * (F (x j) - F u) := by
    have hb := hblock j
    have hg := hgrowth (x j)
    have hscaled := mul_le_mul_of_nonneg_left hg
      (show 4 * L / (μ * N ^ 2) * (2 / μ) ≥ 0 by positivity)
    have hμne : μ ≠ 0 := ne_of_gt hμ
    have hNne : N ≠ 0 := ne_of_gt hN
    dsimp [q]
    field_simp at hb hg hscaled ⊢
    nlinarith
  have hrate (j : ℕ) : F (x j) - F u ≤ q ^ j * (F (x 0) - F u) := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        F (x (j + 1)) - F u ≤ q * (F (x j) - F u) := hstep j
        _ ≤ q * (q ^ j * (F (x 0) - F u)) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (j + 1) * (F (x 0) - F u) := by rw [pow_succ]; ring
  exact ⟨hrate k, hq1⟩

end QuasiNewtonConvergence

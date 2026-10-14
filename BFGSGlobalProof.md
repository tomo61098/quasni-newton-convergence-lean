# Global convergence of BFGS (Nocedal–Wright, Theorem 6.5)

This is a mathematical proof of the book's result. The existing Lean library
proves the secant equation, preservation of positive definiteness, the matrix
trace and determinant identities, the trace–logdet lower bound, and Zoutendijk
summability under a global Lipschitz-gradient hypothesis. The level-set
estimates and the final argument connecting the angle bound to convergence
of the iterates are **not yet formalized in Lean**.

## Statement

Let `f : ℝⁿ → ℝ` be twice continuously differentiable. Suppose the initial
level set `𝓛 = {x | f(x) ≤ f(x₀)}` is convex and, for every `x ∈ 𝓛`,

`m‖v‖² ≤ vᵀ∇²f(x)v ≤ M‖v‖²` for all `v`, with `0 < m ≤ M`.

Start with any symmetric positive definite `B₀`. At a nonstationary iterate,
set `pₖ = −Bₖ⁻¹∇f(xₖ)`, choose a positive step length `αₖ` satisfying weak
Wolfe conditions with `0 < c₁ < c₂ < 1`, and put

`sₖ = αₖpₖ`, `yₖ = ∇f(xₖ₊₁) − ∇f(xₖ)`,

`Bₖ₊₁ = Bₖ − BₖsₖsₖᵀBₖ/(sₖᵀBₖsₖ) + yₖyₖᵀ/(yₖᵀsₖ)`.

If a stationary iterate is reached, keep it fixed. Then `xₖ` converges to
the unique minimizer `x⋆` of `f`.

## Proof

**1. The iterates and update are well defined.** Armijo decrease keeps all
iterates in `𝓛`. The set `𝓛` is closed. For `x ∈ 𝓛`, Taylor's formula on the
segment from `x₀` to `x` gives

`f(x) ≥ f(x₀) + ∇f(x₀)ᵀ(x−x₀) + (m/2)‖x−x₀‖²`.

Because also `f(x) ≤ f(x₀)`, this makes `𝓛` bounded. In finite dimension it
is compact, so `f` has a minimizer `x⋆` in it. Any point with a lower value
would also belong to `𝓛`, so this is a global minimizer. The Hessian lower
bound makes it unique and gives `∇f(x⋆)=0`.

Convexity of `𝓛` keeps the segment `[xₖ,xₖ₊₁]` inside it. With
`Aₖ = ∫₀¹ ∇²f(xₖ+t sₖ)dt`, the fundamental theorem of calculus gives
`yₖ=Aₖsₖ` and `mI ⪯ Aₖ ⪯ MI`. Hence

`yₖᵀsₖ ≥ m‖sₖ‖² > 0`, and `‖yₖ‖² ≤ M yₖᵀsₖ`.

The first inequality ensures the BFGS denominator is nonzero. The BFGS
quadratic-form identity shows that a symmetric positive definite `Bₖ`
produces a symmetric positive definite `Bₖ₊₁`; this is already proved in
`BroydenUpdates.lean`.

**2. The BFGS potential prevents all search angles from collapsing.** Define

`aₖ = yₖᵀsₖ/‖sₖ‖² ≥ m`, `bₖ = ‖yₖ‖²/(yₖᵀsₖ) ≤ M`,

`qₖ = sₖᵀBₖsₖ/‖sₖ‖² > 0`,
`γₖ = sₖᵀBₖsₖ/(‖sₖ‖‖Bₖsₖ‖) ∈ (0,1]`.

The trace of a rank-one map `uvᵀ` is `vᵀu`; therefore the update gives

`tr(Bₖ₊₁) = tr(Bₖ) − ‖Bₖsₖ‖²/(sₖᵀBₖsₖ) + bₖ
          = tr(Bₖ) − qₖ/γₖ² + bₖ`.

The rank-two determinant lemma gives

`det(Bₖ₊₁) = det(Bₖ) (yₖᵀsₖ)/(sₖᵀBₖsₖ)
            = det(Bₖ) aₖ/qₖ`.

For completeness, take `u=Bₖsₖ`, `β=sₖᵀBₖsₖ`, `η=yₖᵀsₖ`,
`U=[−u,yₖ]`, and `Vᵀ=[uᵀ/β; yₖᵀ/η]`. Then
`Bₖ₊₁=Bₖ+UVᵀ` and

`I₂ + VᵀBₖ⁻¹U = [[0, η/β], [−1, 1+yₖᵀBₖ⁻¹yₖ/η]]`,

whose determinant is `η/β`. This proves the displayed determinant identity.

Let `Ψ(B)=tr(B)−log det(B)`. Its eigenvalue expression is
`Ψ(B)=Σᵢ(λᵢ−log λᵢ) ≥ n`, because `t−log t ≥ 1` for `t>0`.
Writing `tₖ=qₖ/γₖ²`, the two update identities yield exactly

`Ψ(Bₖ₊₁)−Ψ(Bₖ)
 = [bₖ−log aₖ−1] + [1−tₖ+log tₖ] + log γₖ²`.

The middle bracket is nonpositive. Choose a fixed `C>0` with
`C ≥ M−log m−1`. Then

`Ψ(Bₖ₊₁) ≤ Ψ(Bₖ)+C+log γₖ²`, so
`n ≤ Ψ(B_N) ≤ Ψ(B₀)+CN+Σₖ₌₀ᴺ⁻¹ log γₖ²`.

Suppose, toward contradiction, that `γₖ→0`. Eventually
`log γₖ² < −2C`, and the right-hand side tends to `−∞`, contrary to its
lower bound `n`. Thus `limsup γₖ>0`: there are `δ>0` and infinitely many
indices `k` with `γₖ≥δ`.

**3. Wolfe decrease and strong convexity finish the proof.** Because
`Bₖpₖ=−∇f(xₖ)` and `sₖ=αₖpₖ`, the angle above equals the cosine between
`−∇f(xₖ)` and `pₖ`:

`γₖ = −∇f(xₖ)ᵀpₖ/(‖∇f(xₖ)‖‖pₖ‖)`.

The Lipschitz gradient bound `‖∇f(v)−∇f(u)‖≤M‖v−u‖` on the convex level
set, weak Wolfe conditions, and the lower bound on `f` give Zoutendijk's
summability estimate

`Σₖ γₖ²‖∇f(xₖ)‖² < ∞`.

On the infinite subsequence with `γₖ≥δ`, gradient norms therefore tend to
zero. The Hessian lower bound implies
`‖x−x⋆‖ ≤ ‖∇f(x)‖/m` for `x∈𝓛`, so that subsequence tends to `x⋆`.
Armijo decrease makes `f(xₖ)` monotone, and the subsequence shows its limit
is `f(x⋆)`. Finally, strong convexity on `𝓛` gives
`f(xₖ)−f(x⋆) ≥ (m/2)‖xₖ−x⋆‖²`, hence the *whole* sequence satisfies
`xₖ→x⋆`. ∎

Source: [Nocedal and Wright, *Numerical Optimization*, second edition,
Chapter 6, Theorem 6.5](https://studylib.net/doc/27835099/numerical-optimization-jorge-nocedal-ste).

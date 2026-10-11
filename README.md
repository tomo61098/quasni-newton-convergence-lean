# BFGS convergence in Lean

This repository is a Lean formalization project for *Numerical Optimization*
by Jorge Nocedal and Stephen J. Wright (second edition), beginning with
Theorem 6.5 (global convergence of BFGS under Assumption 6.1) and Theorem 6.6
(superlinear convergence under the local Hessian condition and summability of
the iterate errors).

The project follows the package and submission conventions of the sibling
`c-separated-np-complete-lean` repository. It pins Lean and mathlib. The BFGS
update and line search results are developed in this repository using mathlib.

## Current formalized results

`QuasiNewtonConvergence/ProximalGradient.lean` treats a composite objective
`F = f + g`, where `f` has an `L`-smooth convex gradient and the exact
proximal subproblem satisfies its variational optimality condition. It proves
the three-point inequality, the last-iterate `O(1/k)` bound, and geometric
distance and objective bounds when `f` is strongly convex. The minimizer is
supplied to the rate theorems.

`QuasiNewtonConvergence/ProximalNesterov.lean` proves the accelerated
three-sequence potential and its `O(1/k²)` objective bound for standard
quadratically growing FISTA weights. The quadratic growth of the weights is
an explicit hypothesis of the rate theorem. It also proves the geometric
objective bound for fixed-length restarts under quadratic growth of `F`.

`QuasiNewtonConvergence/ProximalBFGS.lean` proves descent and summability of
squared steps for variable-metric proximal updates, including BFGS metrics,
under a uniform lower metric bound. An additional composite error bound yields
a geometric objective rate. These bounds require assumptions beyond the BFGS
secant update; positive definiteness of each update by itself does not give a
uniform spectral bound.

`QuasiNewtonConvergence/GradientDescent.lean` proves convergence of fixed-step
gradient descent with step size `1/L`. For an `L`-smooth convex objective, it
establishes the objective gap bound
`(k+1)(f(xₖ₊₁)-f(x★)) ≤ (L/2)‖x₀-x★‖²` and convergence of objective values.
Under `μ`-strong convexity with `0 < μ ≤ L`, it proves the geometric bound
`f(xₖ)-f(x★) ≤ (1-μ/L)^k(f(x₀)-f(x★))`. With a stationary minimizer, the
iterates themselves converge to it. Smoothness and convexity are expressed by
their standard first-order inequalities for the supplied gradient map.

`QuasiNewtonConvergence/DiminishingGradientDescent.lean` proves convergence for
the exact step schedule `αₖ = 1/√(k+1)`, corresponding to `1/√i` with indexing
from `i = 1`. For any `L > 0`, finitely many initial steps may exceed `1/L`;
the proof applies the variable-step potential bound to the remaining steps.
The sum of those step lengths diverges, giving convergence of objective values
for convex objectives. Under strong convexity and a stationary minimizer, the
iterates converge to that minimizer as well.

`QuasiNewtonConvergence/Subgradient.lean` proves the subgradient method for
the same step schedule `αₖ = 1/√(k+1)`. Given a minimizer and a uniform bound
on the chosen subgradients, the best objective value among the first `n`
iterates converges to the minimum. The proof establishes the standard weighted
gap estimate
`2∑_{k<n} αₖ(f(xₖ)-f(x★)) ≤ ‖x₀-x★‖² + G²∑_{k<n} αₖ²` and shows that the
sum of squared steps divided by the sum of steps tends to zero. The theorem
does not assert convergence of every iterate.

For a strongly convex objective, the same file proves more: if the selected
subgradients satisfy the strong subgradient inequality and remain uniformly
bounded, then every iterate converges to the minimizer under the same
`αₖ = 1/√(k+1)` schedule. The objective values converge as well. The proof
uses the recurrence
`‖xₖ₊₁-x★‖² ≤ (1-μ αₖ)‖xₖ-x★‖² + G²αₖ²` and needs no
differentiability or smoothness assumption.

`QuasiNewtonConvergence/Nesterov.lean` proves the standard smooth convex
accelerated gradient method in its three-sequence form. Its explicit bound is
`f(xₙ)-f(x★) ≤ 2L‖x₀-x★‖²/[n(n+1)]` for `n ≥ 1`; hence objective values
converge to the minimum. The assumptions are `L > 0`, the smooth upper
inequality, the convex first-order inequality, and a minimizer. Nocedal and
Wright's *Numerical Optimization* mentions Nesterov's optimal bound in its
discussion of conjugate gradients but does not present this accelerated
gradient algorithm or theorem. The result formalized here is the standard
smooth convex Nesterov acceleration result, not a numbered theorem from that
book.

Under smooth strong convexity, the same Nesterov sequence has convergent
iterates. Restarting the accelerated sequence every `m` steps gives a linear
rate at restart points: if `μ m(m+1) ≥ 8L`, each block at least halves the
objective gap, so after `r` blocks it is at most `2⁻ʳ` times the initial gap.
Such a finite `m` always exists. On a complete real inner product space, the
formalized convergence theorems obtain the minimizer from smooth strong
convexity; callers need not supply it. This is a restarted acceleration
guarantee. The direct constant-momentum result is in the next module.

`QuasiNewtonConvergence/NesterovStrong.lean` formalizes the direct
constant-momentum strongly convex method in a three-sequence form. With
`0 < μ ≤ L` and `t = √(μ/L)`, the potential
`f(xₖ)-f(x★) + (μ/2)‖zₖ-x★‖²` contracts by `1-t` at every iteration. Thus
`f(xₖ)-f(x★) ≤ (1-√(μ/L))^k [f(x₀)-f(x★)+(μ/2)‖x₀-x★‖²]`.
Both objective values and iterates converge to the minimizer. On a complete
real inner product space, the theorem obtains that minimizer from smooth
strong convexity.

`QuasiNewtonConvergence/StrongConvexMinimizer.lean` proves that, on a complete
real inner product space, a smooth strongly convex objective has a unique
stationary global minimizer. It constructs the minimizer as the limit of a
fixed-step descent sequence. The public strong-convexity convergence theorems
now choose the minimizer themselves, so callers need only give the objective,
gradient, smoothness and strong-convexity assumptions, and the iterate rule.

`QuasiNewtonConvergence/WolfeGradientDescent.lean` proves that steepest descent
with weak Wolfe steps converges to the unique minimizer of a smooth strongly
convex objective on a complete real inner product space. The theorem derives
the gradient Lipschitz estimate from the smoothness and convexity inequalities,
handles stationary iterates, and concludes both iterate and objective-value
convergence. Its line-search assumptions are the nonnegative step lengths and
the weak Wolfe inequalities at each step.

`QuasiNewtonConvergence.bfgsUpdate_secant` proves the secant equation for the
Hessian form of the BFGS update. The companion
`bfgsUpdate_secant_of_curvature` derives its denominator conditions from a
positive definite approximation and the curvature condition.
`lake build QuasiNewtonConvergence` passes, and
`lake env lean ProofAudit.lean` reports only Lean's three standard axioms.
This lemma is a foundation for the convergence proofs, not a proof of either
book theorem.

`QuasiNewtonConvergence/LineSearch.lean` proves the weak Wolfe directional
curvature and BFGS secant curvature conditions, a quantitative decrease bound,
and Zoutendijk's summability theorem for iterates whose gradient is Lipschitz.
The latter establishes summability of
`⟪∇f(xₖ),pₖ⟫² / ‖pₖ‖²` when the objective is bounded below. It assumes that the
line search produces weak Wolfe steps and uses a global Lipschitz gradient
bound; later work will derive the needed bound from the book's Hessian
assumptions on the relevant level set.

The Lean proof of Theorem 6.5 still requires the finite-dimensional
determinant identity, the Hessian bounds on the level set, and the final
Zoutendijk-to-iterate argument. Theorem 6.6 requires the Dennis--Moré
characterization and its BFGS summability argument.

A complete mathematical proof of Theorem 6.5 is in
[BFGSGlobalProof.md](BFGSGlobalProof.md). Its trace update identity is now
formalized in `QuasiNewtonConvergence/BFGSMatrix.lean`. The scalar
trace–determinant potential recurrence and its no-angle-collapse consequence
are formalized in `QuasiNewtonConvergence/BFGSGlobal.lean`. The finite-dimensional
determinant lemma has a proved two-dimensional reduction; connecting its
entries to the bundled BFGS map and completing the level-set iterate theorem
remain open in Lean.

No Palomar submission is ready until the full statements are proved without
placeholders, independently mirrored in a Challenge module, and checked by
Comparator. A `formalization.yaml` and Comparator configuration will be added
once a complete result exists, so the metadata cannot imply a completed proof.

## Newton's method

`QuasiNewtonConvergence/Newton.lean` proves local quadratic convergence of
full Newton steps. A globally Lipschitz Hessian yields a quadratic gradient remainder;
a uniformly bounded inverse Hessian near a stationary point then gives
`‖xₖ₊₁ - x⋆‖ ≤ (B L) ‖xₖ - x⋆‖²`. If the starting error is at most `r`
and `B L r < 1`, the iterates converge to `x⋆`. The proof uses the weaker
remainder constant `L` in place of the sharp `L/2`.

## Broyden-class updates and conditional convergence

`QuasiNewtonConvergence/BroydenUpdates.lean` implements Hessian-form BFGS,
the Broyden class with parameter `φ`, its DFP endpoint `φ = 1`, and SR1 with
the textbook relative-denominator safeguard. The formulas are bundled as
linear maps. Lean verifies their secant equations when updates are taken,
and proves symmetry and positive definiteness are preserved through any
sequence of BFGS, DFP, or nonnegative-parameter Broyden updates with
positive secant curvature. SR1 preserves symmetry but can lose positivity.

`QuasiNewtonConvergence/BroydenConvergence.lean` proves a conditional
line-search convergence theorem for quasi-Newton directions `pₖ = -Hₖ∇f(xₖ)`.
With weak Wolfe steps, a Lipschitz gradient, a lower bounded objective,
uniform inverse-approximation bounds `m‖gₖ‖² ≤ ⟪gₖ,Hₖgₖ⟫` and `‖Hₖ‖ ≤ M`,
the gradient norms tend to zero; stationary iterates are handled directly. Under strong
convexity, the iterates and objective values converge to a stationary
minimizer. A separate theorem proves a superlinear ratio for full steps when
the Hessian approximation error along the current displacement vanishes
relative to that displacement. These approximation and spectral bounds are
hypotheses, not consequences proved for the update sequences. Thus these
results do not yet establish Theorem 6.5
for unrestricted BFGS iterates or its restricted Broyden-class extension.
Nocedal–Wright excludes the DFP endpoint from that extension and analyzes
SR1 separately with a trust-region method.

## Sources

- Jorge Nocedal and Stephen J. Wright, *Numerical Optimization*, second
  edition, Springer, 2006, Chapter 3, Theorem 3.7 (local quadratic Newton
  convergence).

- Jorge Nocedal and Stephen J. Wright, *Numerical Optimization*, second
  edition, Springer, 2006, Chapter 6, Theorems 6.5 and 6.6.
- Yurii Nesterov, "A method of solving a convex programming problem with
  convergence rate O(1/k²)," *Doklady Akademii Nauk SSSR* 269 (1983),
  543–547.
- Alexandre d'Aspremont, Damien Scieur, and Adrien Taylor,
  [*Acceleration Methods*](https://accelerationmethods.github.io/AccelerationMethodsWebsite/acceleration_monograph_v3.pdf),
  Section 4.5, Algorithm 15 and Theorem 4.14.
- [Mathlib](https://github.com/leanprover-community/mathlib4).

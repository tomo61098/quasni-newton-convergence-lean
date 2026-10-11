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

Theorem 6.5 still requires the BFGS trace/determinant estimate, the positive
angle subsequence, and the strong convexity argument. Theorem 6.6 requires
the Dennis--Moré characterization and its BFGS summability argument.

No Palomar submission is ready until the full statements are proved without
placeholders, independently mirrored in a Challenge module, and checked by
Comparator. A `formalization.yaml` and Comparator configuration will be added
once a complete result exists, so the metadata cannot imply a completed proof.

## Sources

- Jorge Nocedal and Stephen J. Wright, *Numerical Optimization*, second
  edition, Springer, 2006, Chapter 6, Theorems 6.5 and 6.6.
- [Mathlib](https://github.com/leanprover-community/mathlib4).

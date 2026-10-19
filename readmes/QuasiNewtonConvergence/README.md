# QuasiNewtonConvergence: mathematical statements

This directory mirrors `QuasiNewtonConvergence/`: each Lean module has a
Markdown document with the same stem. Definitions, structures, and all
top-level theorem and lemma statements are included, including private helpers.
Proofs, tactic scripts, and programming implementation details are omitted.
Only this source folder is covered.

Open these files in a Markdown viewer with MathJax or KaTeX support. Inline
mathematics uses `$...$`; display mathematics uses `$$...$$`.

## Notation and conventions

- $\mathbb N=\{0,1,2,\ldots\}$, and $I_n=\{0,\ldots,n-1\}$. A function
  $I_n\to\mathbb R$ describes a real coordinate vector. Euclidean norm claims
  use $\mathbb R^n$; this distinction preserves Lean's explicit `EuclideanSpace`
  wrappers (ordinary function spaces need not carry the Euclidean norm).
- $\mathcal L_{\mathbb R}(E,F)$ denotes real linear maps, and
  $\mathcal L^{\rm cont}_{\mathbb R}(E,F)$ denotes continuous real linear maps.
  $\operatorname{Subspaces}_{\mathbb R}(E)$ is the collection of real linear subspaces.
- $G$ denotes the supplied map named `gradient`; $\mathcal H$ denotes
  `hessian`, and $J$ denotes `inverseHessian`. These names alone impose no
  differentiability or inverse condition. Such conditions are written as hypotheses.
- $x_\star$ denotes `minimizer` or `xstar`; $H_\star$ denotes `Hstar`.
  $\Psi$ is `potential`, $e$ is `error`, $T$ is `trace`, $D$ is `determinant`,
  and $\chi$ is `cosine`. The supplied kernel map `dh` is an actual gradient
  only where a gradient hypothesis says so.
- $P_U$ is orthogonal projection onto $U$, with its output viewed in the ambient
  space; $U^\perp$ is the orthogonal complement. $I$ denotes the identity map
  (and the numeral $1$ in matrix or endomorphism arithmetic denotes its identity).
- $\iota_2:(I_n\to\mathbb R)\longrightarrow\mathbb R^n$ identifies a coordinate
  function with the corresponding Euclidean vector (`WithLp.toLp 2` in Lean).
- For a run record $r$, subscripts such as $r_x$, $r_B$, $r_H$, and $r_\alpha$
  denote its named fields.
- An assertion $\sum_{k=0}^{\infty}|a(k)|<\infty$ translates `Summable a`
  for the real sequences here. Limits are along natural-number indices tending to infinity.
- Finite sums and products with an unqualified index range over the complete
  finite index set determined by the parameter types. Sums over `Finset.range n`
  are written with bounds $0\le k<n$.
- To retain unconditional Lean statements, scalar division is totalized:
  $a/0=0$ and $0^{-1}=0$. Lean's real logarithm has $\log0=0$ and
  $\log(-a)=\log a$; for $a>0$ it is the usual logarithm. Real square root is
  zero on negative inputs. Matrix inverse is the totalized inverse used by Lean.
  The positivity and nonzero assumptions in each statement are retained explicitly.
- Named predicates and functions refer to their definition sections, with a few
  shorter display names shown by the defining equations. Proof arguments and
  computational decidability instances are omitted; their mathematical assumptions
  are retained. Type coercions between integer, natural, and real arithmetic are implicit.

## Modules

| Lean module | Mathematical statements | Topic |
| --- | ---: | --- |
| [AxiomAudit](AxiomAudit.md) | 0 | Axiom audit support |
| [BFGSDennisMore](BFGSDennisMore.md) | 10 | Scalar Dennis–Moré analysis |
| [BFGSDirectional](BFGSDirectional.md) | 3 | Directional BFGS convergence |
| [BFGSGlobal](BFGSGlobal.md) | 2 | BFGS global potential bounds |
| [BFGSMatrix](BFGSMatrix.md) | 9 | BFGS matrix identities |
| [Bregman](Bregman.md) | 24 | Bregman divergences and rates |
| [BregmanExistence](BregmanExistence.md) | 11 | Bregman proximal existence and optimality |
| [BroydenConvergence](BroydenConvergence.md) | 8 | Conditional quasi-Newton convergence |
| [BroydenUpdates](BroydenUpdates.md) | 50 | Quasi-Newton update formulas |
| [DennisMoreProximal](DennisMoreProximal.md) | 14 | Smooth and proximal Dennis–Moré conditions |
| [DiminishingGradientDescent](DiminishingGradientDescent.md) | 16 | Diminishing-step gradient descent |
| [GradientDescent](GradientDescent.md) | 16 | Fixed-step gradient descent |
| [KarmarkarBitBounds](KarmarkarBitBounds.md) | 11 | Integer gaps and bit bounds |
| [KarmarkarProjection](KarmarkarProjection.md) | 13 | Projected directions and step bounds |
| [KarmarkarProjective](KarmarkarProjective.md) | 32 | Projective transformations and potential bounds |
| [LineSearch](LineSearch.md) | 8 | LineSearch |
| [LogBarrierNewtonInvariant](LogBarrierNewtonInvariant.md) | 17 | Log-barrier Newton invariants |
| [Nesterov](Nesterov.md) | 20 | Accelerated gradient methods |
| [NesterovStrong](NesterovStrong.md) | 10 | Strongly convex acceleration |
| [NesterovTraditional](NesterovTraditional.md) | 21 | Traditional FISTA parameters and convergence |
| [Newton](Newton.md) | 4 | Newton convergence |
| [Potential](Potential.md) | 2 | Scalar potential bounds |
| [PrimalPathFollowing](PrimalPathFollowing.md) | 18 | Primal barrier path-following bounds |
| [ProximalBFGS](ProximalBFGS.md) | 6 | Variable-metric proximal methods |
| [ProximalGradient](ProximalGradient.md) | 9 | Proximal gradient methods |
| [ProximalNesterov](ProximalNesterov.md) | 6 | Accelerated proximal methods |
| [SimplexPhaseOne](SimplexPhaseOne.md) | 23 | Phase I feasibility constructions |
| [StrongConvexMinimizer](StrongConvexMinimizer.md) | 9 | Strongly convex minimizers |
| [StrongWolfeCounterexample](StrongWolfeCounterexample.md) | 6 | Strong Wolfe counterexample |
| [Subgradient](Subgradient.md) | 11 | Subgradient methods |
| [WolfeGradientDescent](WolfeGradientDescent.md) | 3 | Gradient descent with Wolfe steps |

Total: **392 declarations** across **31 modules**.

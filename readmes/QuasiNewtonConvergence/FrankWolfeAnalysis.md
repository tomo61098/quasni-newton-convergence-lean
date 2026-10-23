# FrankWolfeAnalysis

[Lean source](../../QuasiNewtonConvergence/FrankWolfeAnalysis.lean)

Let $E$ be a complete real inner product space, $S\subseteq E$, $f:E\to\mathbb R$,
$G:E\to E$, and $L\ge0$. Assume `ConvexOn ℝ S f`,
`HasGradientAt f (G x) x` for each $x\in S$, and `LipschitzOnWith L G S`.
Thus $G$ is an actual ambient gradient at feasible points, with
$\|G(x)-G(y)\|\le L\|x-y\|$ on $S$. No interior-point assumption is imposed.

* `frankWolfe_first_order` proves, for all $x,y\in S$,
  $f(x)+\langle G(x),y-x\rangle\le f(y)$ and
  $f(y)\le f(x)+\langle G(x),y-x\rangle+(L/2)\|y-x\|^2$.
  It restricts $f$ to $z(t)=x+t(y-x)$. Convexity bounds its derivative at zero
  by its secant slope. The Lipschitz bound controls its derivative at $t$ by
  $\langle G(x),y-x\rangle+Lt\|y-x\|^2$; derivative comparison with the
  corresponding quadratic gives the upper inequality.
* `FrankWolfeProblem.ofGradient` constructs the core problem from these
  hypotheses and compactness of $S$, using $D=\operatorname{diam}S$.
* `frankWolfe_lineSearch_converges` additionally assumes compactness and
  $x_0\in S$. It constructs an exact line-search run starting at $x_0$, with
  step zero whenever the oracle gap is zero, and a constrained minimizer $u$.
  It proves $f(x_n)-f(u)\le2L(\operatorname{diam}S)^2/(n+2)$ for $n\ge1$
  and $f(x_n)\to f(u)$. Objective continuity is derived from the gradient
  hypothesis. Oracle and line-search attainment are proved using compactness.

The constructor also allows use of the original prescribed-step results with
the same conventional analytical hypotheses. All declarations are axiom-audited.

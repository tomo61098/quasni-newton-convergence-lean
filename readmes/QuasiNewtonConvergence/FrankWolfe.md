# FrankWolfe

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/FrankWolfe.lean)

Let $E$ be a real inner product space. The theorem concerns minimizing a
smooth convex objective over a bounded convex feasible set. All first-order
inequalities below are required only on that set.

## Problem and algorithm

`FrankWolfeProblem` records a convex set $S\subseteq E$, an objective
$f:E\to\mathbb R$, a supplied gradient map $G:E\to E$, and constants
$L,D\ge0$ satisfying, for every $x,y\in S$,

$$
f(x)+\langle G(x),y-x\rangle\le f(y)
\le f(x)+\langle G(x),y-x\rangle+\frac L2\|y-x\|^2,
\qquad \|y-x\|\le D.
$$

These inequalities hold for a differentiable convex function with an
$L$-Lipschitz gradient on the convex set. The core formalization takes the
inequalities as assumptions. `FrankWolfeProblem.ofCompact` constructs this
record from a compact convex set, the two inequalities, and $L\ge0$, using
$D=\operatorname{diam}S$.

[FrankWolfeAnalysis](FrankWolfeAnalysis.md) derives these inequalities from
convexity, actual derivatives, and a Lipschitz gradient on a Hilbert space.
[FrankWolfeLineSearch](FrankWolfeLineSearch.md) extends the algorithm to
variable steps and exact line search, with a zero-gap stopping rule.

`frankWolfeStepSize` defines $\gamma_k=2/(k+2)$, indexed from $k=0$.
`frankWolfeStepSize_mem` proves $0\le\gamma_k\le1$ for every $k$.

`FrankWolfeProblem.Run` records sequences $(x_k)$ and $(s_k)$ such that
$x_0\in S$ and, for every $k$,

$$
s_k\in S,\qquad
\langle G(x_k),s_k\rangle\le\langle G(x_k),y\rangle
\quad(y\in S),\qquad
x_{k+1}=x_k+\gamma_k(s_k-x_k).
$$

The linear oracle is exact. Any minimizing choice is permitted when there
are ties. `Run.gap` defines the oracle gap
$g_k=\langle G(x_k),x_k-s_k\rangle$.

## Theorems and proof

All `Run` theorems below are in the namespace `FrankWolfeProblem`.

1. `Run.feasible`: $x_k\in S$ for every $k$. This follows by induction
   because the update is a convex combination of feasible points.

2. `Run.error_le_gap`: for every $u\in S$ and $k\ge0$,
   $f(x_k)-f(u)\le g_k$. Indeed, the first-order lower inequality gives
   $f(x_k)-f(u)\le\langle G(x_k),x_k-u\rangle$, and the oracle property
   bounds this inner product by $g_k$.

3. `Run.descent`: writing $C=LD^2$, for every $k\ge0$,

   $$
   f(x_{k+1})\le f(x_k)-\gamma_k g_k+\frac C2\gamma_k^2.
   $$

   Apply the smooth upper inequality to the actual update, then use
   $\|s_k-x_k\|\le D$.

4. `Run.error_recurrence`: for any $u\in S$, put $h_k=f(x_k)-f(u)$.
   Combining the preceding two inequalities gives

   $$
   h_{k+1}\le(1-\gamma_k)h_k+\frac C2\gamma_k^2.
   $$

5. `frankWolfe_scalar_rate`: for any real sequence $(e_k)$ and $C\ge0$
   satisfying this recurrence, with no restriction on $e_0$,

   $$
   e_{k+1}\le\frac{2C}{k+3}\qquad(k\ge0).
   $$

   Since $\gamma_0=1$, the first step gives $e_1\le C/2\le2C/3$.
   If $e_n\le2C/(n+2)$ for $n\ge1$, the recurrence gives

   $$
   e_{n+1}\le\frac{2C(n+1)}{(n+2)^2}
   \le\frac{2C}{n+3},
   $$

   where the last inequality uses $(n+1)(n+3)\le(n+2)^2$.

6. `Run.rate`: for every feasible comparator $u$,

   $$
   f(x_n)-f(u)\le\frac{2LD^2}{n+2}\qquad(n\ge1).
   $$

   No claim of this initial-error-independent bound is made at $n=0$.

7. `Run.values_tendsto`: if $u\in S$ minimizes $f$ over $S$, then
   $f(x_k)\to f(u)$. The objective gap is between zero and the rate bound,
   whose limit is zero.

8. `Run.iterates_tendsto_of_quadratic_growth`: if the same constrained
   minimizer satisfies, for some $\mu>0$,

   $$
   \frac\mu2\|y-u\|^2\le f(y)-f(u)\qquad(y\in S),
   $$

   then $x_k\to u$. The objective convergence forces the squared distance
   to zero. This condition does not require $G(u)=0$.

9. `FrankWolfeProblem.exists_run`: if $S$ is compact and $x_0\in S$, a run
   with that starting point exists. Each continuous linear objective attains
   its minimum on the nonempty compact set; choosing such an oracle and
   recursively applying the update constructs the run.

10. `Run.compact_converges`: if $S$ is compact and $f$ is continuous on $S$,
    there exists $u\in S$ minimizing $f$ over $S$, with the bound in item 6
    for every positive iterate and the objective convergence in item 7.

The rate and value convergence do not assert convergence of the entire
iterate sequence without an additional condition such as quadratic growth.
Compactness is needed for the existence results; the rate itself only needs
the bounded convex problem and a supplied exact run.

All twelve theorem/construction declarations are included in `ProofAudit.lean`,
which rejects unfinished proofs and nonstandard axiom dependencies.

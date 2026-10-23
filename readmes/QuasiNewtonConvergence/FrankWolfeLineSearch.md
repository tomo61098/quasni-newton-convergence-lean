# FrankWolfeLineSearch

[Lean source](../../QuasiNewtonConvergence/FrankWolfeLineSearch.lean)

Fix a [FrankWolfeProblem](FrankWolfe.md) $P$ on a real inner product space.
`StepRun` records feasible oracle points $s_k$ that exactly minimize
$\langle G(x_k),s\rangle$, steps $\alpha_k\in[0,1]$, a feasible initial point,
and the update $x_{k+1}=x_k+\alpha_k(s_k-x_k)$.
`Run.toStepRun` embeds each original prescribed-step run into this definition.
`StepRun.gap` is $g_k=\langle G(x_k),x_k-s_k\rangle$.

Theorems in `FrankWolfeProblem.StepRun`:

* `feasible`: all $x_k$ remain feasible.
* `error_le_gap`: $f(x_k)-f(u)\le g_k$ for every feasible $u$.
* `optimal_of_gap_zero`: $g_k=0$ implies $x_k$ is a constrained global minimizer.
* `trial_bound`: for every $t\in[0,1]$,
  $f(x_k+t(s_k-x_k))\le f(x_k)-t g_k+(LD^2/2)t^2$.
* `descent`: the same bound holds for the actual step $t=\alpha_k$.
* `stays_of_gap_zero`: if every zero gap forces $\alpha_k=0$, then
  $g_k=0$ implies $x_{k+n}=x_k$ for all $n$. Changes in oracle tie choices
  do not affect this conclusion.
* `monotone_values`: exact line search implies $f(x_{k+1})\le f(x_k)$.
* `rate`: any run whose next value is no greater than the prescribed trial
  value at $t=2/(k+2)$ satisfies $f(x_n)-f(u)\le2LD^2/(n+2)$ for $n\ge1$
  and every feasible comparator $u$.
* `lineSearch_rate`: the same rate follows from exact line search.
* `lineSearch_values_tendsto`: for any supplied constrained minimizer $u$,
  exact line search gives $f(x_k)\to f(u)$.

`StepRun.IsLineSearch` means that, at each step, the actual next objective
value is minimal among all $t\in[0,1]$ on that step's oracle segment.
The rate proof compares this minimum with the prescribed trial value and
applies the existing scalar recurrence lemma. This compares trial points
from the current iterate; it does not compare two entire trajectories.

`FrankWolfeProblem.exists_lineSearch_run` proves that a compact feasible set,
a continuous objective on it, and a feasible starting point supply such a
run, with the zero-gap stopping rule. Both the oracle minimization and the
one-dimensional line minimization are attained. The construction chooses
zero explicitly when the gap is zero, including when a whole segment is optimal.

The modern prescribed-step method and exact segment minimization are described
in [Jaggi (2013), Algorithms 1 and 3; the rate comparison is in Appendix A](https://proceedings.mlr.press/v28/jaggi13-supp.pdf).
These results do not formalize the specialized quadratic-programming machinery
of the 1956 paper. All twelve theorem/construction declarations are axiom-audited.

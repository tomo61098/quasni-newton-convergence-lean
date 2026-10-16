# KarmarkarProjective

Projective transformations and potential bounds.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/KarmarkarProjective.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains. Let $n\in\mathbb{N}$.

## Definition: `karmarkarDenominator`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L19)

Let $a, y: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{den}\left(a,\,y\right) := \sum_{i} a\left(i\right) \, y\left(i\right)
$$

## Definition: `karmarkarInverse`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L22)

Let $a, y: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{Kinv}\left(a,\,y\right) := \left(i\mapsto \frac{a\left(i\right) \, y\left(i\right)}{\operatorname{den}\left(a,\,y\right)}\right)
$$

## Definition: `karmarkarForward`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L25)

Let $a, x: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{Kfwd}\left(a,\,x\right) := \left(i\mapsto \frac{\frac{x\left(i\right)}{a\left(i\right)}}{\sum_{j} \frac{x\left(j\right)}{a\left(j\right)}}\right)
$$

## Theorem: `karmarkarDenominator_pos`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L28)

Let $a, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad 0 < a\left(i\right)\\[4pt]\forall i,\quad 0 < y\left(i\right)
\end{gathered}
$$

Then

$$
0 < \operatorname{den}\left(a,\,y\right)
$$

## Theorem: `karmarkarInverse_sum`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L37)

Let $a, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{den}\left(a,\,y\right) \ne 0
\end{gathered}
$$

Then

$$
\sum_{i} \operatorname{Kinv}\left(a,\,y,\,i\right) = 1
$$

## Theorem: `karmarkarInverse_pos`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L47)

Let $a, y: I_{n}\to \mathbb{R}$; $i: I_{n}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 < a\left(i\right)\\[4pt]\forall i,\quad 0 < y\left(i\right)\\[4pt]0 < \operatorname{den}\left(a,\,y\right)
\end{gathered}
$$

Then

$$
0 < \operatorname{Kinv}\left(a,\,y,\,i\right)
$$

## Theorem: `karmarkarInverse_linear_constraint`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L53)

Let $m: \mathbb{N}$; $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $a, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
A\left(\left(i\mapsto a\left(i\right) \, y\left(i\right)\right)\right) = 0
\end{gathered}
$$

Then

$$
A\left(\operatorname{Kinv}\left(a,\,y\right)\right) = 0
$$

## Theorem: `karmarkarForward_inverse`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L64)

Let $a, x: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad a\left(i\right) \ne 0\\[4pt]\sum_{i} x\left(i\right) = 1\\[4pt]\sum_{i} \frac{x\left(i\right)}{a\left(i\right)} \ne 0
\end{gathered}
$$

Then

$$
\operatorname{Kinv}\left(a,\,\operatorname{Kfwd}\left(a,\,x\right)\right) = x
$$

## Theorem: `karmarkarInverse_forward`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L90)

Let $a, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad a\left(i\right) \ne 0\\[4pt]\sum_{i} y\left(i\right) = 1\\[4pt]\operatorname{den}\left(a,\,y\right) \ne 0
\end{gathered}
$$

Then

$$
\operatorname{Kfwd}\left(a,\,\operatorname{Kinv}\left(a,\,y\right)\right) = y
$$

## Definition: `karmarkarCost`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L116)

Let $c, x: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{cost}\left(c,\,x\right) := \sum_{i} c\left(i\right) \, x\left(i\right)
$$

## Definition: `karmarkarWeightedCost`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L118)

Let $a, c, y: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{weightedCost}\left(a,\,c,\,y\right) := \sum_{i} c\left(i\right) \, a\left(i\right) \, y\left(i\right)
$$

## Definition: `karmarkarPotential`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L121)

Let $c, x: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{Potential}\left(c,\,x\right) := n \, \log\left(\operatorname{cost}\left(c,\,x\right)\right) - \left(\sum_{i} \log\left(x\left(i\right)\right)\right)
$$

## Theorem: `karmarkarCost_inverse`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L125)

Let $a, c, y: I_{n}\to \mathbb{R}$.

Then

$$
\operatorname{cost}\left(c,\,\operatorname{Kinv}\left(a,\,y\right)\right) = \frac{\operatorname{weightedCost}\left(a,\,c,\,y\right)}{\operatorname{den}\left(a,\,y\right)}
$$

## Theorem: `karmarkarPotential_inverse`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L136)

Let $a, c, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 < a\left(i\right)\\[4pt]\forall i,\quad 0 < y\left(i\right)\\[4pt]0 < \operatorname{den}\left(a,\,y\right)\\[4pt]0 < \operatorname{weightedCost}\left(a,\,c,\,y\right)
\end{gathered}
$$

Then

$$
\operatorname{Potential}\left(c,\,\operatorname{Kinv}\left(a,\,y\right)\right) = n \, \log\left(\operatorname{weightedCost}\left(a,\,c,\,y\right)\right) - \left(\sum_{i} \log\left(a\left(i\right)\right)\right) - \left(\sum_{i} \log\left(y\left(i\right)\right)\right)
$$

## Definition: `karmarkarCenter`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L157)

Let $n: \mathbb{N}$.

Define

$$
\operatorname{center}\left(n\right) := \left(i\mapsto \frac{1}{n}\right)
$$

## Theorem: `karmarkarCenter_sum`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L159)

Assume all of the following.

$n\ne0$.

Then

$$
\sum_{i} \operatorname{center}\left(n,\,i\right) = 1
$$

## Theorem: `karmarkarDenominator_center`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L164)

Let $a: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\sum_{i} a\left(i\right) = 1
\end{gathered}
$$

Then

$$
\operatorname{den}\left(a,\,\operatorname{center}\left(n\right)\right) = \frac{1}{n}
$$

## Theorem: `karmarkarWeightedCost_center`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L169)

Let $a, c: I_{n}\to \mathbb{R}$.

Then

$$
\operatorname{weightedCost}\left(a,\,c,\,\operatorname{center}\left(n\right)\right) = \frac{\operatorname{cost}\left(c,\,a\right)}{n}
$$

## Theorem: `karmarkarInverse_center`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L178)

Let $a: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\sum_{i} a\left(i\right) = 1
\end{gathered}
$$

Then

$$
\operatorname{Kinv}\left(a,\,\operatorname{center}\left(n\right)\right) = a
$$

## Theorem: `karmarkarPotential_projective_change`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L187)

Let $a, c, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad 0 < a\left(i\right)\\[4pt]\forall i,\quad 0 < y\left(i\right)\\[4pt]\sum_{i} a\left(i\right) = 1\\[4pt]0 < \operatorname{den}\left(a,\,y\right)\\[4pt]0 < \operatorname{weightedCost}\left(a,\,c,\,y\right)\\[4pt]0 < \operatorname{cost}\left(c,\,a\right)
\end{gathered}
$$

Then

$$
\operatorname{Potential}\left(c,\,\operatorname{Kinv}\left(a,\,y\right)\right) - \operatorname{Potential}\left(c,\,a\right) = n \, \left(\log\left(\operatorname{weightedCost}\left(a,\,c,\,y\right)\right) - \log\left(\operatorname{weightedCost}\left(a,\,c,\,\operatorname{center}\left(n\right)\right)\right)\right) - \left(\sum_{i} \log\left(y\left(i\right)\right) - \log\left(\operatorname{center}\left(n,\,i\right)\right)\right)
$$

## Theorem: `karmarkarPotential_telescope`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L217)

Let $\varphi: \mathbb{N}\to \mathbb{R}$; $\delta: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad \varphi\left(k + 1\right) \le \varphi\left(k\right) - \delta
\end{gathered}
$$

Then

$$
\varphi\left(k\right) \le \varphi\left(0\right) - k \, \delta
$$

## Theorem: `karmarkar_simplex_log_bound`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L228)

Let $x: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]\sum_{i} x\left(i\right) = 1
\end{gathered}
$$

Then

$$
\sum_{i} \log\left(x\left(i\right)\right) \le -n \, \log\left(n\right)
$$

## Theorem: `karmarkarPotential_simplex_lower`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L243)

Let $c, x: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]\sum_{i} x\left(i\right) = 1\\[4pt]0 < \operatorname{cost}\left(c,\,x\right)
\end{gathered}
$$

Then

$$
n \, \log\left(n \, \operatorname{cost}\left(c,\,x\right)\right) \le \operatorname{Potential}\left(c,\,x\right)
$$

## Theorem: `karmarkarPotential_center`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L256)

Let $c: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
0 < \operatorname{cost}\left(c,\,\operatorname{center}\left(n\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{Potential}\left(c,\,\operatorname{center}\left(n\right)\right) = n \, \log\left(n \, \operatorname{cost}\left(c,\,\operatorname{center}\left(n\right)\right)\right)
$$

## Theorem: `karmarkar_log_remainder`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L273)

Let $t: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
-\left(\frac{1}{4}\right) \le t
\end{gathered}
$$

Then

$$
-\log\left(1 + t\right) \le -t + \frac{4}{3} \, t^{2}
$$

## Theorem: `karmarkar_barrier_bound`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L286)

Let $m: \mathbb{N}$; $t: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad -\left(\frac{1}{4}\right) \le t\left(i\right)\\[4pt]\sum_{i} t\left(i\right) = 0\\[4pt]\sum_{i} t\left(i\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

Then

$$
-\left(\sum_{i} \log\left(1 + t\left(i\right)\right)\right) \le \frac{1}{6}
$$

## Theorem: `karmarkar_projective_step_drop`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L303)

Let $a, c, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
2 \le n\\[4pt]\forall i,\quad 0 < a\left(i\right)\\[4pt]\forall i,\quad 0 < y\left(i\right)\\[4pt]\sum_{i} a\left(i\right) = 1\\[4pt]0 < \operatorname{den}\left(a,\,y\right)\\[4pt]0 < \operatorname{weightedCost}\left(a,\,c,\,y\right)\\[4pt]0 < \operatorname{cost}\left(c,\,a\right)\\[4pt]\frac{\operatorname{weightedCost}\left(a,\,c,\,y\right)}{\operatorname{weightedCost}\left(a,\,c,\,\operatorname{center}\left(n\right)\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}\\[4pt]-\left(\sum_{i} \log\left(y\left(i\right)\right) - \log\left(\operatorname{center}\left(n,\,i\right)\right)\right) \le \frac{1}{6}
\end{gathered}
$$

Then

$$
\operatorname{Potential}\left(c,\,\operatorname{Kinv}\left(a,\,y\right)\right) \le \operatorname{Potential}\left(c,\,a\right) - \frac{1}{12}
$$

## Theorem: `karmarkar_barrier_bound_from_coordinates`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L343)

Let $y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad 0 < y\left(i\right)\\[4pt]\sum_{i} y\left(i\right) = 1\\[4pt]\forall i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(i\right) - 1\\[4pt]\sum_{i} \left(n \, y\left(i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

Then

$$
-\left(\sum_{i} \log\left(y\left(i\right)\right) - \log\left(\operatorname{center}\left(n,\,i\right)\right)\right) \le \frac{1}{6}
$$

## Theorem: `karmarkar_projective_step_drop_of_coordinates`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L373)

Let $a, c, y: I_{n}\to \mathbb{R}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
2 \le n\\[4pt]\forall i,\quad 0 < a\left(i\right)\\[4pt]\forall i,\quad 0 < y\left(i\right)\\[4pt]\sum_{i} a\left(i\right) = 1\\[4pt]\sum_{i} y\left(i\right) = 1\\[4pt]0 < \operatorname{den}\left(a,\,y\right)\\[4pt]0 < \operatorname{weightedCost}\left(a,\,c,\,y\right)\\[4pt]0 < \operatorname{cost}\left(c,\,a\right)\\[4pt]\frac{\operatorname{weightedCost}\left(a,\,c,\,y\right)}{\operatorname{weightedCost}\left(a,\,c,\,\operatorname{center}\left(n\right)\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}\\[4pt]\forall i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(i\right) - 1\\[4pt]\sum_{i} \left(n \, y\left(i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

Then

$$
\operatorname{Potential}\left(c,\,\operatorname{Kinv}\left(a,\,y\right)\right) \le \operatorname{Potential}\left(c,\,a\right) - \frac{1}{12}
$$

## Theorem: `karmarkar_objective_exponential_rate`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L392)

Let $c: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\delta: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \sum_{i} x\left(k,\,i\right) = 1\\[4pt]\forall k,\quad 0 < \operatorname{cost}\left(c,\,x\left(k\right)\right)\\[4pt]\operatorname{Potential}\left(c,\,x\left(0\right)\right) = n \, \log\left(n \, \operatorname{cost}\left(c,\,x\left(0\right)\right)\right)\\[4pt]\forall k,\quad \operatorname{Potential}\left(c,\,x\left(k + 1\right)\right) \le \operatorname{Potential}\left(c,\,x\left(k\right)\right) - \delta
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) \le \operatorname{cost}\left(c,\,x\left(0\right)\right) \, \exp\left(\frac{-k \, \delta}{n}\right)
$$

## Theorem: `karmarkar_projective_run_rate`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L441)

Let $c: I_{n}\to \mathbb{R}$; $x, y: \mathbb{N}\to I_{n}\to \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
2 \le n\\[4pt]x\left(0\right) = \operatorname{center}\left(n\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{Kinv}\left(x\left(k\right),\,y\left(k\right)\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,i,\quad 0 < y\left(k,\,i\right)\\[4pt]\forall k,\quad \sum_{i} x\left(k,\,i\right) = 1\\[4pt]\forall k,\quad \sum_{i} y\left(k,\,i\right) = 1\\[4pt]\forall k,\quad 0 < \operatorname{cost}\left(c,\,x\left(k\right)\right)\\[4pt]\forall k,\quad 0 < \operatorname{den}\left(x\left(k\right),\,y\left(k\right)\right)\\[4pt]\forall k,\quad 0 < \operatorname{weightedCost}\left(x\left(k\right),\,c,\,y\left(k\right)\right)\\[4pt]\forall k,\quad \frac{\operatorname{weightedCost}\left(x\left(k\right),\,c,\,y\left(k\right)\right)}{\operatorname{weightedCost}\left(x\left(k\right),\,c,\,\operatorname{center}\left(n\right)\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}\\[4pt]\forall k,i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(k,\,i\right) - 1\\[4pt]\forall k,\quad \sum_{i} \left(n \, y\left(k,\,i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) \le \operatorname{cost}\left(c,\,x\left(0\right)\right) \, \exp\left(\frac{-k}{12 \, n}\right)
$$

## Theorem: `karmarkar_exponential_crosses_gap`

[Source](../../QuasiNewtonConvergence/KarmarkarProjective.lean#L480)

Let $c: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $D: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
0 < D\\[4pt]0 < \operatorname{cost}\left(c,\,x\left(0\right)\right)\\[4pt]\forall k,\quad \operatorname{cost}\left(c,\,x\left(k\right)\right) \le \operatorname{cost}\left(c,\,x\left(0\right)\right) \, \exp\left(\frac{-k}{12 \, n}\right)\\[4pt]12 \, n \, \log\left(D \, \operatorname{cost}\left(c,\,x\left(0\right)\right)\right) < k
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) < \frac{1}{D}
$$


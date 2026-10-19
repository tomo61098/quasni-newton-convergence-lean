# StrongWolfeCounterexample

Strong Wolfe counterexample.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains.

Definitions from other modules: [BroydenUpdates](BroydenUpdates.md), [LineSearch](LineSearch.md).

## Definition: `halfStepIterate`

[Source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean#L17)

Let $k: \mathbb{N}$.

Define

$$
\operatorname{halfStepIterate}\left(k\right) := \left(\frac{1}{2}\right)^{k}
$$

## Theorem: `halfStepIterate_pos` (private helper)

[Source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean#L19)

Let $k: \mathbb{N}$.

Then

$$
0 < \operatorname{halfStepIterate}\left(k\right)
$$

## Theorem: `halfStepIterate_succ` (private helper)

[Source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean#L22)

Let $k: \mathbb{N}$.

Then

$$
\operatorname{halfStepIterate}\left(k + 1\right) = \frac{\operatorname{halfStepIterate}\left(k\right)}{2}
$$

## Theorem: `quadratic_half_step_strongWolfe`

[Source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean#L28)

Let $x: \mathbb{R}$.

Then

$$
\begin{gathered}
\operatorname{WolfeStep}\left(\frac{1}{4},\,\frac{3}{4},\,\frac{1}{2},\,-x^{2},\,\frac{-x^{2}}{2},\,\frac{x^{2}}{2},\,\frac{\left(\frac{x}{2}\right)^{2}}{2}\right)\\
\land\quad \left|\frac{-x^{2}}{2}\right| \le \frac{3}{4} \, \left|-x^{2}\right|
\end{gathered}
$$

## Theorem: `bfgs_identity_update`

[Source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean#L39)

Let $s: \mathbb{R}$.

Then

$$
\operatorname{bfgsUpdateMap}\left(I,\,s,\,s\right) = I
$$

## Theorem: `quadratic_half_step_bfgs_counterexample`

[Source](../../QuasiNewtonConvergence/StrongWolfeCounterexample.lean#L45)

Then

$$
\begin{gathered}
\forall k,\quad \operatorname{bfgsUpdateMap}\left(I,\,\operatorname{halfStepIterate}\left(k + 1\right) - \operatorname{halfStepIterate}\left(k\right),\,\operatorname{halfStepIterate}\left(k + 1\right) - \operatorname{halfStepIterate}\left(k\right)\right) = I\\
\land\quad \forall k,\quad \operatorname{halfStepIterate}\left(k + 1\right) = \operatorname{halfStepIterate}\left(k\right) + \frac{1}{2} \, -\operatorname{halfStepIterate}\left(k\right)\\
\land\quad \forall k,\quad \operatorname{WolfeStep}\left(\frac{1}{4},\,\frac{3}{4},\,\frac{1}{2},\,-\operatorname{halfStepIterate}\left(k\right)^{2},\,\frac{-\operatorname{halfStepIterate}\left(k\right)^{2}}{2},\,\frac{\operatorname{halfStepIterate}\left(k\right)^{2}}{2},\,\frac{\left(\frac{\operatorname{halfStepIterate}\left(k\right)}{2}\right)^{2}}{2}\right) \land \left|\frac{-\operatorname{halfStepIterate}\left(k\right)^{2}}{2}\right| \le \frac{3}{4} \, \left|-\operatorname{halfStepIterate}\left(k\right)^{2}\right|\\
\land\quad \forall k,\quad \frac{\left\|\operatorname{halfStepIterate}\left(k + 1\right)\right\|}{\left\|\operatorname{halfStepIterate}\left(k\right)\right\|} = \frac{1}{2}\\
\land\quad \neg\left(\lim_{k\to\infty} \frac{\left\|\operatorname{halfStepIterate}\left(k + 1\right)\right\|}{\left\|\operatorname{halfStepIterate}\left(k\right)\right\|} = 0\right)
\end{gathered}
$$


# Subgradient

Subgradient methods.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/Subgradient.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [DiminishingGradientDescent](DiminishingGradientDescent.md).

## Definition: `IsSubgradient`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L18)

Let $f: E\to \mathbb{R}$; $x, g: E$.

Define

$$
\operatorname{IsSubgradient}\left(f,\,x,\,g\right) \Longleftrightarrow \forall y,\quad f\left(y\right) \ge f\left(x\right) + \left\langle g,y - x\right\rangle
$$

## Theorem: `subgradient_step_potential`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L22)

Let $f: E\to \mathbb{R}$; $x, x_\star, g: E$; $\alpha, G: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le \alpha\\[4pt]0 \le G\\[4pt]\operatorname{IsSubgradient}\left(f,\,x,\,g\right)\\[4pt]\left\|g\right\| \le G
\end{gathered}
$$

Then

$$
2 \, \alpha \, \left(f\left(x\right) - f\left(x_\star\right)\right) \le \left\|x - x_\star\right\|^{2} - \left\|\operatorname{gradientStepSize}\left(\left(i\mapsto g\right),\,\alpha,\,x\right) - x_\star\right\|^{2} + \alpha^{2} \, G^{2}
$$

## Theorem: `subgradient_weighted_gap_bound`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L52)

Let $f: E\to \mathbb{R}$; $x, g: \mathbb{N}\to E$; $x_\star: E$; $\alpha: \mathbb{N}\to \mathbb{R}$; $G: \mathbb{R}$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]0 \le G\\[4pt]\forall k,\quad \operatorname{IsSubgradient}\left(f,\,x\left(k\right),\,g\left(k\right)\right)\\[4pt]\forall k,\quad \left\|g\left(k\right)\right\| \le G\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(\left(i\mapsto g\left(k\right)\right),\,\alpha\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
2 \, \left(\sum_{k=0}^{n-1} \alpha\left(k\right) \, \left(f\left(x\left(k\right)\right) - f\left(x_\star\right)\right)\right) \le \left\|x\left(0\right) - x_\star\right\|^{2} + G^{2} \, \left(\sum_{k=0}^{n-1} \alpha\left(k\right)^{2}\right)
$$

## Theorem: `subgradient_best_eventually`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L80)

Let $f: E\to \mathbb{R}$; $x, g: \mathbb{N}\to E$; $x_\star: E$; $\alpha: \mathbb{N}\to \mathbb{R}$; $G: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]0 \le G\\[4pt]\forall k,\quad \operatorname{IsSubgradient}\left(f,\,x\left(k\right),\,g\left(k\right)\right)\\[4pt]\forall k,\quad \left\|g\left(k\right)\right\| \le G\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(\left(i\mapsto g\left(k\right)\right),\,\alpha\left(k\right),\,x\left(k\right)\right)\\[4pt]\lim_{n\to\infty} \sum_{k=0}^{n-1} \alpha\left(k\right) = +\infty\\[4pt]\lim_{n\to\infty} \frac{\sum_{k=0}^{n-1} \alpha\left(k\right)^{2}}{\sum_{k=0}^{n-1} \alpha\left(k\right)} = 0
\end{gathered}
$$

Then

$$
\forall \varepsilon\in \mathbb{R},\quad 0 < \varepsilon \Longrightarrow \left(\forall ᶠ n\in +\infty,\quad \exists k,<,n,\quad f\left(x\left(k\right)\right) - f\left(x_\star\right) < \varepsilon\right)
$$

## Theorem: `sqrtStepSize_square_sum_ratio_tendsto_zero`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L137)

Then

$$
\lim_{n\to\infty} \frac{\sum_{k=0}^{n-1} \operatorname{sqrtStepSize}\left(k\right)^{2}}{\sum_{k=0}^{n-1} \operatorname{sqrtStepSize}\left(k\right)} = 0
$$

## Theorem: `subgradient_sqrt_best_eventually`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L156)

Let $f: E\to \mathbb{R}$; $x, g: \mathbb{N}\to E$; $x_\star: E$; $G: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le G\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad \operatorname{IsSubgradient}\left(f,\,x\left(k\right),\,g\left(k\right)\right)\\[4pt]\forall k,\quad \left\|g\left(k\right)\right\| \le G\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(\left(i\mapsto g\left(k\right)\right),\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\forall \varepsilon\in \mathbb{R},\quad 0 < \varepsilon \Longrightarrow \left(\forall ᶠ n\in +\infty,\quad \exists k,<,n,\quad 0 \le f\left(x\left(k\right)\right) - f\left(x_\star\right) \land f\left(x\left(k\right)\right) - f\left(x_\star\right) < \varepsilon\right)
$$

## Theorem: `scalar_subgradient_decay` (private helper)

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L175)

Let $e, \alpha: \mathbb{N}\to \mathbb{R}$; $c, B: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c\\[4pt]0 \le B\\[4pt]\forall k,\quad 0 \le e\left(k\right)\\[4pt]\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]\lim_{k\to\infty} \alpha\left(k\right) = 0\\[4pt]\forall K,\quad \lim_{n\to\infty} \sum_{j=0}^{n-1} \alpha\left(K + j\right) = +\infty\\[4pt]\forall k,\quad e\left(k + 1\right) \le e\left(k\right) - c \, \alpha\left(k\right) \, e\left(k\right) + B \, \alpha\left(k\right)^{2}
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} e\left(k\right) = 0
$$

## Definition: `IsStrongSubgradient`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L253)

Let $f: E\to \mathbb{R}$; $\mu: \mathbb{R}$; $x, g: E$.

Define

$$
\operatorname{IsStrongSubgradient}\left(f,\,\mu,\,x,\,g\right) \Longleftrightarrow \forall y,\quad f\left(y\right) \ge f\left(x\right) + \left\langle g,y - x\right\rangle + \frac{\mu}{2} \, \left\|y - x\right\|^{2}
$$

## Theorem: `strong_subgradient_step_bound`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L258)

Let $f: E\to \mathbb{R}$; $x, x_\star, g: E$; $\alpha, G, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le \alpha\\[4pt]0 \le G\\[4pt]f\left(x_\star\right) \le f\left(x\right)\\[4pt]\operatorname{IsStrongSubgradient}\left(f,\,\mu,\,x,\,g\right)\\[4pt]\left\|g\right\| \le G
\end{gathered}
$$

Then

$$
\left\|\operatorname{gradientStepSize}\left(\left(i\mapsto g\right),\,\alpha,\,x\right) - x_\star\right\|^{2} \le \left(1 - \mu \, \alpha\right) \, \left\|x - x_\star\right\|^{2} + G^{2} \, \alpha^{2}
$$

## Theorem: `subgradient_sqrt_strong_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L288)

Let $f: E\to \mathbb{R}$; $x, g: \mathbb{N}\to E$; $x_\star: E$; $G, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le G\\[4pt]0 < \mu\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad \operatorname{IsStrongSubgradient}\left(f,\,\mu,\,x\left(k\right),\,g\left(k\right)\right)\\[4pt]\forall k,\quad \left\|g\left(k\right)\right\| \le G\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(\left(i\mapsto g\left(k\right)\right),\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = x_\star
$$

## Theorem: `subgradient_sqrt_strong_values_tendsto`

[Source](../../QuasiNewtonConvergence/Subgradient.lean#L321)

Let $f: E\to \mathbb{R}$; $x, g: \mathbb{N}\to E$; $x_\star: E$; $G, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le G\\[4pt]0 < \mu\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad \operatorname{IsStrongSubgradient}\left(f,\,\mu,\,x\left(k\right),\,g\left(k\right)\right)\\[4pt]\forall k,\quad \left\|g\left(k\right)\right\| \le G\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(\left(i\mapsto g\left(k\right)\right),\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$


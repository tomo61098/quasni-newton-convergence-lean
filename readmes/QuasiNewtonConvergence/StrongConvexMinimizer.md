# StrongConvexMinimizer

Strongly convex minimizers.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [GradientDescent](GradientDescent.md), [DiminishingGradientDescent](DiminishingGradientDescent.md), [LineSearch](LineSearch.md).

## Theorem: `strongConvex_gradient_monotone`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L21)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $\mu: \mathbb{R}$; $x, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\mu \, \left\|x - y\right\|^{2} \le \left\langle G\left(x\right) - G\left(y\right),x - y\right\rangle
$$

## Theorem: `strongConvex_distance_le_gradients`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L32)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $\mu: \mathbb{R}$; $x, y: E$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\left\|x - y\right\| \le \frac{\left\|G\left(x\right)\right\| + \left\|G\left(y\right)\right\|}{\mu}
$$

## Theorem: `gradientDescent_gradient_tendsto_zero`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L53)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \left\|G\left(x\left(k\right)\right)\right\| = 0
$$

## Theorem: `gradientDescent_cauchySeq_of_strongConvex`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L86)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{CauchySeq}\left(x\right)
$$

## Theorem: `objective_tendsto_of_points_tendsto`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L110)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $\operatorname{limit}: E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\lim_{k\to\infty} x\left(k\right) = \operatorname{limit}
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(\operatorname{limit}\right)
$$

## Theorem: `exists_strongConvex_minimizer`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L145)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad G\left(x_\star\right) = 0 \land \left(\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\right)
$$

## Theorem: `existsUnique_strongConvex_minimizer`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L186)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\exists! x_\star\in E,\quad \forall y,\quad f\left(x_\star\right) \le f\left(y\right)
$$

## Theorem: `gradientDescent_sqrt_strong_converges`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L209)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(G,\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad \left(\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\right) \land \lim_{k\to\infty} x\left(k\right) = x_\star
$$

## Theorem: `gradientDescent_strong_converges`

[Source](../../QuasiNewtonConvergence/StrongConvexMinimizer.lean#L226)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad \left(\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\right) \land \lim_{k\to\infty} x\left(k\right) = x_\star
$$


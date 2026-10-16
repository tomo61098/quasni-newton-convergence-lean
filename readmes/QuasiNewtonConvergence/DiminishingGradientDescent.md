# DiminishingGradientDescent

Diminishing-step gradient descent.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [GradientDescent](GradientDescent.md).

## Definition: `gradientStepSize`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L16)

Let $G: E\to E$; $\alpha: \mathbb{R}$; $x: E$.

Define

$$
\operatorname{gradientStepSize}\left(G,\,\alpha,\,x\right) := x - \alpha \, G\left(x\right)
$$

## Definition: `sqrtStepSize`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L19)

Let $k: \mathbb{N}$.

Define

$$
\operatorname{sqrtStepSize}\left(k\right) := \frac{1}{\sqrt{k + 1}}
$$

## Theorem: `smoothUpper_of_small_step` (private helper)

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L21)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \alpha: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \alpha\\[4pt]\alpha \le \frac{1}{L}\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)
\end{gathered}
$$

Then

$$
\operatorname{SmoothUpper}\left(f,\,G,\,\frac{1}{\alpha}\right)
$$

## Theorem: `gradientStepSize_convex_potential`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L37)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \alpha: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \alpha\\[4pt]\alpha \le \frac{1}{L}\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)
\end{gathered}
$$

Then

$$
2 \, \alpha \, \left(f\left(\operatorname{gradientStepSize}\left(G,\,\alpha,\,x\right)\right) - f\left(x_\star\right)\right) \le \left\|x - x_\star\right\|^{2} - \left\|\operatorname{gradientStepSize}\left(G,\,\alpha,\,x\right) - x_\star\right\|^{2}
$$

## Theorem: `gradientStepSize_descent` (private helper)

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L58)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \alpha: \mathbb{R}$; $x: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \alpha\\[4pt]\alpha \le \frac{1}{L}\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)
\end{gathered}
$$

Then

$$
f\left(\operatorname{gradientStepSize}\left(G,\,\alpha,\,x\right)\right) \le f\left(x\right)
$$

## Theorem: `gradientDescent_variable_rate`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L73)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L: \mathbb{R}$; $\alpha: \mathbb{N}\to \mathbb{R}$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall k,\quad 0 < \alpha\left(k\right)\\[4pt]\forall k,\quad \alpha\left(k\right) \le \frac{1}{L}\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(G,\,\alpha\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
2 \, \left(\sum_{k=0}^{n-1} \alpha\left(k\right)\right) \, \left(f\left(x\left(n\right)\right) - f\left(x_\star\right)\right) \le \left\|x\left(0\right) - x_\star\right\|^{2}
$$

## Theorem: `gradientDescent_variable_tendsto`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L107)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L: \mathbb{R}$; $\alpha: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad 0 < \alpha\left(k\right)\\[4pt]\forall k,\quad \alpha\left(k\right) \le \frac{1}{L}\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(G,\,\alpha\left(k\right),\,x\left(k\right)\right)\\[4pt]\lim_{n\to\infty} \sum_{k=0}^{n-1} \alpha\left(k\right) = +\infty
\end{gathered}
$$

Then

$$
\lim_{n\to\infty} f\left(x\left(n\right)\right) = f\left(x_\star\right)
$$

## Theorem: `sqrtStepSize_pos`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L140)

Let $k: \mathbb{N}$.

Then

$$
0 < \operatorname{sqrtStepSize}\left(k\right)
$$

## Theorem: `sqrtStepSize_ge_sqrt_difference` (private helper)

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L144)

Let $k: \mathbb{N}$.

Then

$$
\sqrt{k + 1} - \sqrt{k} \le \operatorname{sqrtStepSize}\left(k\right)
$$

## Theorem: `sqrtStepSize_tail_sum_diverges`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L159)

Let $K: \mathbb{N}$.

Then

$$
\lim_{n\to\infty} \sum_{k=0}^{n-1} \operatorname{sqrtStepSize}\left(K + k\right) = +\infty
$$

## Theorem: `sqrtStepSize_sum_diverges`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L192)

Then

$$
\lim_{n\to\infty} \sum_{k=0}^{n-1} \operatorname{sqrtStepSize}\left(k\right) = +\infty
$$

## Theorem: `sqrtStepSize_tendsto_zero`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L197)

Then

$$
\lim_{k\to\infty} \operatorname{sqrtStepSize}\left(k\right) = 0
$$

## Theorem: `gradientDescent_sqrt_tendsto`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L211)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(G,\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$

## Theorem: `StrongConvexFirstOrder.toConvexFirstOrder`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L237)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $\mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\operatorname{ConvexFirstOrder}\left(f,\,G\right)
$$

## Theorem: `gradientDescent_sqrt_strong_tendsto`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L249)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(G,\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$

## Theorem: `gradientDescent_sqrt_strong_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/DiminishingGradientDescent.lean#L265)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStepSize}\left(G,\,\operatorname{sqrtStepSize}\left(k\right),\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = x_\star
$$


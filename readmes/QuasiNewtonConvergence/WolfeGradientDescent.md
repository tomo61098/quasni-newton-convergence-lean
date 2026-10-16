# WolfeGradientDescent

Gradient descent with Wolfe steps.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/WolfeGradientDescent.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [StrongConvexMinimizer](StrongConvexMinimizer.md).

## Theorem: `smoothUpper_gradient_lipschitz`

[Source](../../QuasiNewtonConvergence/WolfeGradientDescent.lean#L18)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, y: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)
\end{gathered}
$$

Then

$$
\left\|G\left(y\right) - G\left(x\right)\right\| \le L \, \left\|y - x\right\|
$$

## Theorem: `wolfe_steepest_descent_bound`

[Source](../../QuasiNewtonConvergence/WolfeGradientDescent.lean#L56)

Let $g, g_+: E$; $L, c_{1}, c_{2}, \alpha, f, f_+: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]\operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha,\,\left\langle g,-g\right\rangle,\,\left\langle g_+,-g\right\rangle,\,f,\,f_+\right)\\[4pt]\left\langle g_+,-g\right\rangle - \left\langle g,-g\right\rangle \le L \, \alpha \, \left\|g\right\|^{2}
\end{gathered}
$$

Then

$$
\frac{c_{1} \, \left(1 - c_{2}\right)}{L} \, \left\|g\right\|^{2} \le f - f_+
$$

## Theorem: `gradientDescent_wolfe_strong_converges`

[Source](../../QuasiNewtonConvergence/WolfeGradientDescent.lean#L87)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $\alpha: \mathbb{N}\to \mathbb{R}$; $L, \mu, c_{1}, c_{2}: \mathbb{R}$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = x\left(k\right) + \alpha\left(k\right) \, -G\left(x\left(k\right)\right)\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha\left(k\right),\,\left\langle G\left(x\left(k\right)\right),-G\left(x\left(k\right)\right)\right\rangle,\,\left\langle G\left(x\left(k + 1\right)\right),-G\left(x\left(k\right)\right)\right\rangle,\,f\left(x\left(k\right)\right),\,f\left(x\left(k + 1\right)\right)\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad \left(\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\right) \land \lim_{k\to\infty} x\left(k\right) = x_\star \land \lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$


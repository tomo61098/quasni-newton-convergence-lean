# GradientDescent

Fixed-step gradient descent.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/GradientDescent.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [Potential](Potential.md).

## Definition: `gradientStep`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L22)

Let $G: E\to E$; $L: \mathbb{R}$; $x: E$.

Define

$$
\operatorname{gradientStep}\left(G,\,L,\,x\right) := x - \frac{1}{L} \, G\left(x\right)
$$

## Definition: `SmoothUpper`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L25)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$.

Define

$$
\operatorname{SmoothUpper}\left(f,\,G,\,L\right) \Longleftrightarrow \forall x,y,\quad f\left(y\right) \le f\left(x\right) + \left\langle G\left(x\right),y - x\right\rangle + \frac{L}{2} \, \left\|y - x\right\|^{2}
$$

## Definition: `ConvexFirstOrder`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L29)

Let $f: E\to \mathbb{R}$; $G: E\to E$.

Define

$$
\operatorname{ConvexFirstOrder}\left(f,\,G\right) \Longleftrightarrow \forall x,y,\quad f\left(y\right) \ge f\left(x\right) + \left\langle G\left(x\right),y - x\right\rangle
$$

## Definition: `StrongConvexFirstOrder`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L32)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $\mu: \mathbb{R}$.

Define

$$
\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right) \Longleftrightarrow \forall x,y,\quad f\left(y\right) \ge f\left(x\right) + \left\langle G\left(x\right),y - x\right\rangle + \frac{\mu}{2} \, \left\|y - x\right\|^{2}
$$

## Theorem: `step_sub` (private helper)

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L36)

Let $G: E\to E$; $L: \mathbb{R}$; $x: E$.

Then

$$
\operatorname{gradientStep}\left(G,\,L,\,x\right) - x = -\left(\frac{1}{L}\right) \, G\left(x\right)
$$

## Theorem: `step_norm_sq` (private helper)

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L40)

Let $G: E\to E$; $L: \mathbb{R}$; $x: E$.

Then

$$
\left\|\operatorname{gradientStep}\left(G,\,L,\,x\right) - x\right\|^{2} = \left(\frac{1}{L}\right)^{2} \, \left\|G\left(x\right)\right\|^{2}
$$

## Theorem: `gradientStep_descent`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L46)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)
\end{gathered}
$$

Then

$$
f\left(\operatorname{gradientStep}\left(G,\,L,\,x\right)\right) \le f\left(x\right) - \frac{\left\|G\left(x\right)\right\|^{2}}{2 \, L}
$$

## Theorem: `step_distance_sq` (private helper)

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L56)

Let $G: E\to E$; $L: \mathbb{R}$; $x, x_\star: E$.

Then

$$
\left\|\operatorname{gradientStep}\left(G,\,L,\,x\right) - x_\star\right\|^{2} = \left\|x - x_\star\right\|^{2} - \frac{2}{L} \, \left\langle G\left(x\right),x - x_\star\right\rangle + \left(\frac{1}{L}\right)^{2} \, \left\|G\left(x\right)\right\|^{2}
$$

## Theorem: `gradientStep_convex_potential`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L70)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)
\end{gathered}
$$

Then

$$
f\left(\operatorname{gradientStep}\left(G,\,L,\,x\right)\right) - f\left(x_\star\right) \le \frac{L}{2} \, \left(\left\|x - x_\star\right\|^{2} - \left\|\operatorname{gradientStep}\left(G,\,L,\,x\right) - x_\star\right\|^{2}\right)
$$

## Theorem: `gradientDescent_convex_rate`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L95)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\left(k + 1\right) \, \left(f\left(x\left(k + 1\right)\right) - f\left(x_\star\right)\right) \le \frac{L}{2} \, \left\|x\left(0\right) - x_\star\right\|^{2}
$$

## Theorem: `strongConvex_gradient_bound`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L121)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $\mu: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
2 \, \mu \, \left(f\left(x\right) - f\left(x_\star\right)\right) \le \left\|G\left(x\right)\right\|^{2}
$$

## Theorem: `gradientStep_strong_contraction`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L134)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
f\left(\operatorname{gradientStep}\left(G,\,L,\,x\right)\right) - f\left(x_\star\right) \le \left(1 - \frac{\mu}{L}\right) \, \left(f\left(x\right) - f\left(x_\star\right)\right)
$$

## Theorem: `gradientDescent_strong_rate`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L149)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L, \mu: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
f\left(x\left(k\right)\right) - f\left(x_\star\right) \le \left(1 - \frac{\mu}{L}\right)^{k} \, \left(f\left(x\left(0\right)\right) - f\left(x_\star\right)\right)
$$

## Theorem: `gradientDescent_convex_tendsto`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L176)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$

## Theorem: `gradientDescent_strong_tendsto`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L206)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$

## Theorem: `gradientDescent_strong_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/GradientDescent.lean#L235)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $x_\star: E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = x_\star
$$


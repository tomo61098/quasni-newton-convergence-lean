# Nesterov

Accelerated gradient methods.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/Nesterov.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [StrongConvexMinimizer](StrongConvexMinimizer.md).

## Theorem: `nesterov_step_potential` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L17)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, A, a: \mathbb{R}$; $x, y, z, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 \le A\\[4pt]0 \le a\\[4pt]L \, a^{2} \le A + a\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\left(A + a\right) \, \left(y - x\right) = a \, \left(z - x\right)
\end{gathered}
$$

Then

$$
\left(A + a\right) \, \left(f\left(\operatorname{gradientStep}\left(G,\,L,\,y\right)\right) - f\left(x_\star\right)\right) + \frac{\left\|z - a \, G\left(y\right) - x_\star\right\|^{2}}{2} \le A \, \left(f\left(x\right) - f\left(x_\star\right)\right) + \frac{\left\|z - x_\star\right\|^{2}}{2}
$$

## Definition: `nesterovWeight`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L86)

Let $L: \mathbb{R}$; $k: \mathbb{N}$.

Define

$$
\operatorname{nesterovWeight}\left(L,\,k\right) := \frac{k \, \left(k + 1\right)}{4 \, L}
$$

## Definition: `nesterovIncrement`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L90)

Let $L: \mathbb{R}$; $k: \mathbb{N}$.

Define

$$
\operatorname{nesterovIncrement}\left(L,\,k\right) := \frac{k + 1}{2 \, L}
$$

## Definition: `nesterovExtrapolate`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L94)

Let $k: \mathbb{N}$; $x, z: E$.

Define

$$
\operatorname{nesterovExtrapolate}\left(k,\,x,\,z\right) := x + \frac{2}{k + 2} \, \left(z - x\right)
$$

## Theorem: `nesterov_weight_succ` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L97)

Let $L: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L
\end{gathered}
$$

Then

$$
\operatorname{nesterovWeight}\left(L,\,k + 1\right) = \operatorname{nesterovWeight}\left(L,\,k\right) + \operatorname{nesterovIncrement}\left(L,\,k\right)
$$

## Theorem: `nesterov_weight_nonneg` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L105)

Let $L: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L
\end{gathered}
$$

Then

$$
0 \le \operatorname{nesterovWeight}\left(L,\,k\right)
$$

## Theorem: `nesterov_increment_nonneg` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L110)

Let $L: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L
\end{gathered}
$$

Then

$$
0 \le \operatorname{nesterovIncrement}\left(L,\,k\right)
$$

## Theorem: `nesterov_weight_condition` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L115)

Let $L: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L
\end{gathered}
$$

Then

$$
L \, \operatorname{nesterovIncrement}\left(L,\,k\right)^{2} \le \operatorname{nesterovWeight}\left(L,\,k\right) + \operatorname{nesterovIncrement}\left(L,\,k\right)
$$

## Theorem: `nesterov_extrapolate_couple` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L132)

Let $L: \mathbb{R}$; $k: \mathbb{N}$; $x, z: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L
\end{gathered}
$$

Then

$$
\left(\operatorname{nesterovWeight}\left(L,\,k\right) + \operatorname{nesterovIncrement}\left(L,\,k\right)\right) \, \left(\operatorname{nesterovExtrapolate}\left(k,\,x,\,z\right) - x\right) = \operatorname{nesterovIncrement}\left(L,\,k\right) \, \left(z - x\right)
$$

## Theorem: `nesterov_convex_weighted_rate`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L149)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, z: \mathbb{N}\to E$; $x_\star: E$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = z\left(k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{nesterovWeight}\left(L,\,n\right) \, \left(f\left(x\left(n\right)\right) - f\left(x_\star\right)\right) \le \frac{\left\|x\left(0\right) - x_\star\right\|^{2}}{2}
$$

## Theorem: `nesterov_convex_rate`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L184)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, z: \mathbb{N}\to E$; $x_\star: E$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = z\left(k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]0 < n
\end{gathered}
$$

Then

$$
f\left(x\left(n\right)\right) - f\left(x_\star\right) \le \frac{2 \, L \, \left\|x\left(0\right) - x_\star\right\|^{2}}{n \, \left(n + 1\right)}
$$

## Theorem: `nesterov_convex_tendsto`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L219)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, z: \mathbb{N}\to E$; $x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall y,\quad f\left(x_\star\right) \le f\left(y\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = z\left(k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$

## Theorem: `strongConvex_distance_gap` (private helper)

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L258)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $\mu: \mathbb{R}$; $x_\star: E$; $y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0
\end{gathered}
$$

Then

$$
\frac{\mu}{2} \, \left\|y - x_\star\right\|^{2} \le f\left(y\right) - f\left(x_\star\right)
$$

## Theorem: `exists_nesterov_restart_length`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L268)

Let $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu
\end{gathered}
$$

Then

$$
\exists m\in \mathbb{N},\quad 2 \le \mu \, \operatorname{nesterovWeight}\left(L,\,m\right)
$$

## Theorem: `nesterov_strong_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L289)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x_\star: E$; $x, z: \mathbb{N}\to E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = z\left(k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = x_\star
$$

## Theorem: `nesterov_strong_restart_half`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L337)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x_\star: E$; $x, z: \mathbb{N}\to E$; $m: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]2 \le \mu \, \operatorname{nesterovWeight}\left(L,\,m\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = z\left(k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)
\end{gathered}
$$

Then

$$
2 \, \left(f\left(x\left(m\right)\right) - f\left(x_\star\right)\right) \le f\left(x\left(0\right)\right) - f\left(x_\star\right)
$$

## Theorem: `nesterov_strong_restarted_rate`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L367)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x_\star: E$; $x, z: \mathbb{N}\to \mathbb{N}\to E$; $m: \mathbb{N}$; $r: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]2 \le \mu \, \operatorname{nesterovWeight}\left(L,\,m\right)\\[4pt]\forall r,\quad z\left(r,\,0\right) = x\left(r,\,0\right)\\[4pt]\forall r,k,\quad x\left(r,\,k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(r,\,k\right),\,z\left(r,\,k\right)\right)\right)\\[4pt]\forall r,k,\quad z\left(r,\,k + 1\right) = z\left(r,\,k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(r,\,k\right),\,z\left(r,\,k\right)\right)\right)\\[4pt]\forall r,\quad x\left(r + 1,\,0\right) = x\left(r,\,m\right)
\end{gathered}
$$

Then

$$
f\left(x\left(r,\,0\right)\right) - f\left(x_\star\right) \le \left(\frac{1}{2}\right)^{r} \, \left(f\left(x\left(0,\,0\right)\right) - f\left(x_\star\right)\right)
$$

## Theorem: `nesterov_strong_restarted_converges`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L402)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x_\star: E$; $x, z: \mathbb{N}\to \mathbb{N}\to E$; $m: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]2 \le \mu \, \operatorname{nesterovWeight}\left(L,\,m\right)\\[4pt]\forall r,\quad z\left(r,\,0\right) = x\left(r,\,0\right)\\[4pt]\forall r,k,\quad x\left(r,\,k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(r,\,k\right),\,z\left(r,\,k\right)\right)\right)\\[4pt]\forall r,k,\quad z\left(r,\,k + 1\right) = z\left(r,\,k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(r,\,k\right),\,z\left(r,\,k\right)\right)\right)\\[4pt]\forall r,\quad x\left(r + 1,\,0\right) = x\left(r,\,m\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\lim_{r\to\infty} x\left(r,\,0\right) = x_\star\\
\land\quad \lim_{r\to\infty} f\left(x\left(r,\,0\right)\right) = f\left(x_\star\right)
\end{gathered}
$$

## Theorem: `nesterov_strong_converges`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L464)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, z: \mathbb{N}\to E$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = z\left(k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(k\right),\,z\left(k\right)\right)\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad \lim_{k\to\infty} x\left(k\right) = x_\star \land \lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$

## Theorem: `nesterov_strong_restarted_exists_minimizer`

[Source](../../QuasiNewtonConvergence/Nesterov.lean#L490)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, z: \mathbb{N}\to \mathbb{N}\to E$; $m: \mathbb{N}$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]2 \le \mu \, \operatorname{nesterovWeight}\left(L,\,m\right)\\[4pt]\forall r,\quad z\left(r,\,0\right) = x\left(r,\,0\right)\\[4pt]\forall r,k,\quad x\left(r,\,k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{nesterovExtrapolate}\left(k,\,x\left(r,\,k\right),\,z\left(r,\,k\right)\right)\right)\\[4pt]\forall r,k,\quad z\left(r,\,k + 1\right) = z\left(r,\,k\right) - \operatorname{nesterovIncrement}\left(L,\,k\right) \, G\left(\operatorname{nesterovExtrapolate}\left(k,\,x\left(r,\,k\right),\,z\left(r,\,k\right)\right)\right)\\[4pt]\forall r,\quad x\left(r + 1,\,0\right) = x\left(r,\,m\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad \lim_{r\to\infty} x\left(r,\,0\right) = x_\star \land \lim_{r\to\infty} f\left(x\left(r,\,0\right)\right) = f\left(x_\star\right)
$$


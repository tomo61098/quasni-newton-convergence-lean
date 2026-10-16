# NesterovStrong

Strongly convex acceleration.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/NesterovStrong.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [Nesterov](Nesterov.md).

## Theorem: `norm_sq_convex_combo` (private helper)

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L17)

Let $u, v: E$; $t: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le t\\[4pt]t \le 1
\end{gathered}
$$

Then

$$
\left\|\left(1 - t\right) \, u + t \, v\right\|^{2} \le \left(1 - t\right) \, \left\|u\right\|^{2} + t \, \left\|v\right\|^{2}
$$

## Definition: `strongNesterovExtrapolate`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L36)

Let $t: \mathbb{R}$; $x, z: E$.

Define

$$
\operatorname{StrongExtrapolate}\left(t,\,x,\,z\right) := x + \frac{t}{1 + t} \, \left(z - x\right)
$$

## Definition: `strongNesterovAuxiliary`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L39)

Let $t, \mu: \mathbb{R}$; $z, y, g: E$.

Define

$$
\operatorname{StrongAuxiliary}\left(t,\,\mu,\,z,\,y,\,g\right) := \left(1 - t\right) \, z + t \, y - \frac{t}{\mu} \, g
$$

## Theorem: `strongNesterov_extrapolate_relation` (private helper)

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L42)

Let $t: \mathbb{R}$; $x, z: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le t
\end{gathered}
$$

Then

$$
\operatorname{StrongExtrapolate}\left(t,\,x,\,z\right) - x = t \, \left(z - \operatorname{StrongExtrapolate}\left(t,\,x,\,z\right)\right)
$$

## Theorem: `strongNesterov_step_potential`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L67)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu, t: \mathbb{R}$; $x, z, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]0 \le t\\[4pt]t \le 1\\[4pt]t^{2} = \frac{\mu}{L}\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Set

$$
y:=\operatorname{StrongExtrapolate}\left(t,\,x,\,z\right)
$$

Set

$$
\operatorname{xnext}:=\operatorname{gradientStep}\left(G,\,L,\,y\right)
$$

Set

$$
\operatorname{znext}:=\operatorname{StrongAuxiliary}\left(t,\,\mu,\,z,\,y,\,G\left(y\right)\right)
$$

Then

$$
f\left(\operatorname{xnext}\right) - f\left(x_\star\right) + \frac{\mu}{2} \, \left\|\operatorname{znext} - x_\star\right\|^{2} \le \left(1 - t\right) \, \left(f\left(x\right) - f\left(x_\star\right) + \frac{\mu}{2} \, \left\|z - x_\star\right\|^{2}\right)
$$

## Definition: `strongNesterovMomentum`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L207)

Let $L, \mu: \mathbb{R}$.

Define

$$
\operatorname{StrongMomentum}\left(L,\,\mu\right) := \sqrt{\frac{\mu}{L}}
$$

## Theorem: `strongNesterov_geometric_rate`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L210)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu, t: \mathbb{R}$; $x, z: \mathbb{N}\to E$; $x_\star: E$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]0 \le t\\[4pt]t \le 1\\[4pt]t^{2} = \frac{\mu}{L}\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{StrongExtrapolate}\left(t,\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = \operatorname{StrongAuxiliary}\left(t,\,\mu,\,z\left(k\right),\,\operatorname{StrongExtrapolate}\left(t,\,x\left(k\right),\,z\left(k\right)\right),\,G\left(\operatorname{StrongExtrapolate}\left(t,\,x\left(k\right),\,z\left(k\right)\right)\right)\right)
\end{gathered}
$$

Then

$$
f\left(x\left(n\right)\right) - f\left(x_\star\right) \le \left(1 - t\right)^{n} \, \left(f\left(x\left(0\right)\right) - f\left(x_\star\right) + \frac{\mu}{2} \, \left\|x\left(0\right) - x_\star\right\|^{2}\right)
$$

## Theorem: `strongNesterov_sqrt_geometric_rate`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L253)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, z: \mathbb{N}\to E$; $x_\star: E$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = \operatorname{StrongAuxiliary}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,\mu,\,z\left(k\right),\,\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right),\,G\left(\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right)\right)\right)
\end{gathered}
$$

Then

$$
f\left(x\left(n\right)\right) - f\left(x_\star\right) \le \left(1 - \sqrt{\frac{\mu}{L}}\right)^{n} \, \left(f\left(x\left(0\right)\right) - f\left(x_\star\right) + \frac{\mu}{2} \, \left\|x\left(0\right) - x_\star\right\|^{2}\right)
$$

## Theorem: `strongNesterov_sqrt_tendsto`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L287)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, z: \mathbb{N}\to E$; $x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = \operatorname{StrongAuxiliary}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,\mu,\,z\left(k\right),\,\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right),\,G\left(\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right)\right)\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\lim_{k\to\infty} x\left(k\right) = x_\star\\
\land\quad \lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
\end{gathered}
$$

## Theorem: `strongNesterov_sqrt_converges`

[Source](../../QuasiNewtonConvergence/NesterovStrong.lean#L356)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, z: \mathbb{N}\to E$.

Assume all of the following.

$E$ is complete.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{gradientStep}\left(G,\,L,\,\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right)\right)\\[4pt]\forall k,\quad z\left(k + 1\right) = \operatorname{StrongAuxiliary}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,\mu,\,z\left(k\right),\,\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right),\,G\left(\operatorname{StrongExtrapolate}\left(\operatorname{StrongMomentum}\left(L,\,\mu\right),\,x\left(k\right),\,z\left(k\right)\right)\right)\right)
\end{gathered}
$$

Then

$$
\exists x_\star\in E,\quad \left(\forall n,\quad f\left(x\left(n\right)\right) - f\left(x_\star\right) \le \left(1 - \sqrt{\frac{\mu}{L}}\right)^{n} \, \left(f\left(x\left(0\right)\right) - f\left(x_\star\right) + \frac{\mu}{2} \, \left\|x\left(0\right) - x_\star\right\|^{2}\right)\right) \land \lim_{k\to\infty} x\left(k\right) = x_\star \land \lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
$$


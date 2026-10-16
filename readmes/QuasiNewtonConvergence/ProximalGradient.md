# ProximalGradient

Proximal gradient methods.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/ProximalGradient.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [GradientDescent](GradientDescent.md).

## Definition: `composite`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L12)

Let $f, g: E\to \mathbb{R}$; $x: E$.

Define

$$
\operatorname{composite}\left(f,\,g,\,x\right) := f\left(x\right) + g\left(x\right)
$$

## Definition: `ProximalOptimality`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L17)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, z: E$.

Define

$$
\operatorname{ProxOpt}\left(g,\,G,\,L,\,x,\,z\right) \Longleftrightarrow \forall u,\quad g\left(u\right) - g\left(z\right) \ge \left\langle -G\left(x\right) - L \, \left(z - x\right),u - z\right\rangle
$$

## Theorem: `distance_identity` (private helper)

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L22)

Let $x, z, u: E$.

Then

$$
2 \, \left\langle z - x,u - z\right\rangle = \left\|u - x\right\|^{2} - \left\|z - x\right\|^{2} - \left\|u - z\right\|^{2}
$$

## Theorem: `proximal_three_point`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L30)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, z, u: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{ProxOpt}\left(g,\,G,\,L,\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le \frac{L}{2} \, \left(\left\|x - u\right\|^{2} - \left\|z - u\right\|^{2}\right)
$$

## Theorem: `proximal_descent`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L55)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x, z: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{ProxOpt}\left(g,\,G,\,L,\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) \le \operatorname{composite}\left(f,\,g,\,x\right)
$$

## Theorem: `proximalGradient_convex_rate`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L66)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\forall k,\quad \operatorname{ProxOpt}\left(g,\,G,\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\left(k + 1\right) \, \left(\operatorname{composite}\left(f,\,g,\,x\left(k + 1\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right)\right) \le \frac{L}{2} \, \left\|x\left(0\right) - u\right\|^{2}
$$

## Theorem: `proximal_strong_three_point`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L89)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x, z, u: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\operatorname{ProxOpt}\left(g,\,G,\,L,\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le \frac{L}{2} \, \left(\left\|x - u\right\|^{2} - \left\|z - u\right\|^{2}\right) - \frac{\mu}{2} \, \left\|x - u\right\|^{2}
$$

## Theorem: `proximalGradient_strong_distance_rate`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L115)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]\forall k,\quad \operatorname{ProxOpt}\left(g,\,G,\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\left\|x\left(k\right) - u\right\|^{2} \le \left(1 - \frac{\mu}{L}\right)^{k} \, \left\|x\left(0\right) - u\right\|^{2}
$$

## Theorem: `proximalGradient_strong_objective_rate`

[Source](../../QuasiNewtonConvergence/ProximalGradient.lean#L151)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, \mu: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]\forall k,\quad \operatorname{ProxOpt}\left(g,\,G,\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,x\left(k + 1\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le \frac{L}{2} \, \left(1 - \frac{\mu}{L}\right)^{k} \, \left\|x\left(0\right) - u\right\|^{2}
$$


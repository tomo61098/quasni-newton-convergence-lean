# Bregman

Bregman divergences and rates.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/Bregman.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [ProximalGradient](ProximalGradient.md).

## Definition: `bregmanD`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L18)

Let $h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x, y: E$.

Define

$$
\operatorname{D}\left(h,\,\operatorname{dh},\,x,\,y\right) := h\left(y\right) - h\left(x\right) - \left\langle \operatorname{dh}\left(x\right),y - x\right\rangle
$$

## Theorem: `bregmanD_nonneg`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L21)

Let $h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)
\end{gathered}
$$

Then

$$
0 \le \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,y\right)
$$

## Theorem: `bregmanD_self`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L28)

Let $h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x: E$.

Then

$$
\operatorname{D}\left(h,\,\operatorname{dh},\,x,\,x\right) = 0
$$

## Theorem: `bregman_three_point_identity`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L33)

Let $h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x, z, u: E$.

Then

$$
\left\langle \operatorname{dh}\left(z\right) - \operatorname{dh}\left(x\right),u - z\right\rangle = \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right) - \operatorname{D}\left(h,\,\operatorname{dh},\,z,\,u\right) - \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,z\right)
$$

## Definition: `RelativeSmoothUpper`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L45)

Let $f, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L: \mathbb{R}$.

Define

$$
\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right) \Longleftrightarrow \forall x,y,\quad f\left(y\right) \le f\left(x\right) + \left\langle G\left(x\right),y - x\right\rangle + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,y\right)
$$

## Definition: `RelativeStrongFirstOrder`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L51)

Let $f, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $\mu: \mathbb{R}$.

Define

$$
\operatorname{RelStrong}\left(f,\,h,\,G,\,\operatorname{dh},\,\mu\right) \Longleftrightarrow \forall x,y,\quad f\left(y\right) \ge f\left(x\right) + \left\langle G\left(x\right),y - x\right\rangle + \mu \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,y\right)
$$

## Definition: `BregmanGradientOptimality`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L58)

Let $g: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x, z: E$.

Define

$$
\operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x,\,z\right) \Longleftrightarrow \forall u,\quad g\left(u\right) - g\left(z\right) \ge \left\langle -G\left(x\right) - L \, \left(\operatorname{dh}\left(z\right) - \operatorname{dh}\left(x\right)\right),u - z\right\rangle
$$

## Theorem: `bregmanGradient_three_point`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L64)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x, z, u: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le L \, \left(\operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right) - \operatorname{D}\left(h,\,\operatorname{dh},\,z,\,u\right)\right)
$$

## Theorem: `bregmanGradient_strong_three_point`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L89)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L, \mu: \mathbb{R}$; $x, z, u: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{RelStrong}\left(f,\,h,\,G,\,\operatorname{dh},\,\mu\right)\\[4pt]\operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le \left(L - \mu\right) \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right) - L \, \operatorname{D}\left(h,\,\operatorname{dh},\,z,\,u\right)
$$

## Definition: `BregmanProximalOptimality`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L115)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x, z: E$.

Define

$$
\operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x,\,z\right) \Longleftrightarrow \forall u,\quad F\left(u\right) - F\left(z\right) \ge \left\langle -\left(L \, \left(\operatorname{dh}\left(z\right) - \operatorname{dh}\left(x\right)\right)\right),u - z\right\rangle
$$

## Theorem: `bregmanProximal_three_point`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L122)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x, z, u: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x,\,z\right)
\end{gathered}
$$

Then

$$
F\left(z\right) - F\left(u\right) \le L \, \left(\operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right) - \operatorname{D}\left(h,\,\operatorname{dh},\,z,\,u\right) - \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,z\right)\right)
$$

## Theorem: `bregman_potential_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L134)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall k,\quad F\left(x\left(k + 1\right)\right) - F\left(u\right) \le L \, \left(\operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,u\right) - \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k + 1\right),\,u\right)\right)\\[4pt]\forall k,\quad F\left(x\left(k + 1\right)\right) \le F\left(x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\left(k + 1\right) \, \left(F\left(x\left(k + 1\right)\right) - F\left(u\right)\right) \le L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregmanGradient_convex_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L153)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall k,\quad \operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\left(k + 1\right) \, \left(\operatorname{composite}\left(f,\,g,\,x\left(k + 1\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right)\right) \le L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregmanProximal_convex_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L184)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall k,\quad \operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\left(k + 1\right) \, \left(F\left(x\left(k + 1\right)\right) - F\left(u\right)\right) \le L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregmanGradient_strong_distance_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L211)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L, \mu: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{RelStrong}\left(f,\,h,\,G,\,\operatorname{dh},\,\mu\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]\forall k,\quad \operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,u\right) \le \left(1 - \frac{\mu}{L}\right)^{k} \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregmanProximal_strong_distance_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L254)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L, \mu: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]0 < \mu\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \mu \, \operatorname{D}\left(h,\,\operatorname{dh},\,v,\,u\right) \le F\left(v\right) - F\left(u\right)\\[4pt]\forall k,\quad \operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,u\right) \le \left(\frac{L}{L + \mu}\right)^{k} \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregmanGradient_strong_objective_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L297)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L, \mu: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{RelStrong}\left(f,\,h,\,G,\,\operatorname{dh},\,\mu\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]\forall k,\quad \operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,x\left(k + 1\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le L \, \left(1 - \frac{\mu}{L}\right)^{k} \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregmanProximal_strong_objective_rate`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L322)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L, \mu: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]0 < \mu\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \mu \, \operatorname{D}\left(h,\,\operatorname{dh},\,v,\,u\right) \le F\left(v\right) - F\left(u\right)\\[4pt]\forall k,\quad \operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
F\left(x\left(k + 1\right)\right) - F\left(u\right) \le L \, \left(\frac{L}{L + \mu}\right)^{k} \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
$$

## Theorem: `bregman_geometric_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L346)

Let $h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x: \mathbb{N}\to E$; $u: E$; $q, \kappa: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le q\\[4pt]q < 1\\[4pt]0 < \kappa\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \kappa \, \left\|v - u\right\|^{2} \le \operatorname{D}\left(h,\,\operatorname{dh},\,v,\,u\right)\\[4pt]\forall k,\quad \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,u\right) \le q^{k} \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = u
$$

## Theorem: `bregmanGradient_strong_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L382)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L, \mu, \kappa: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\mu \le L\\[4pt]0 < \kappa\\[4pt]\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{RelStrong}\left(f,\,h,\,G,\,\operatorname{dh},\,\mu\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]\forall v,\quad \kappa \, \left\|v - u\right\|^{2} \le \operatorname{D}\left(h,\,\operatorname{dh},\,v,\,u\right)\\[4pt]\forall k,\quad \operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = u
$$

## Theorem: `bregmanProximal_strong_iterates_tendsto`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L405)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L, \mu, \kappa: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]0 < \mu\\[4pt]0 < \kappa\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \mu \, \operatorname{D}\left(h,\,\operatorname{dh},\,v,\,u\right) \le F\left(v\right) - F\left(u\right)\\[4pt]\forall v,\quad \kappa \, \left\|v - u\right\|^{2} \le \operatorname{D}\left(h,\,\operatorname{dh},\,v,\,u\right)\\[4pt]\forall k,\quad \operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} x\left(k\right) = u
$$

## Theorem: `bregman_rate_tendsto`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L426)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$.

Assume all of the following.

$$
\begin{gathered}
\forall v,\quad F\left(u\right) \le F\left(v\right)\\[4pt]\forall k,\quad \left(k + 1\right) \, \left(F\left(x\left(k + 1\right)\right) - F\left(u\right)\right) \le L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(0\right),\,u\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} F\left(x\left(k\right)\right) = F\left(u\right)
$$

## Theorem: `bregmanGradient_tendsto`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L452)

Let $f, g, h: E\to \mathbb{R}$; $G, \operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{RelSmooth}\left(f,\,h,\,G,\,\operatorname{dh},\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]\forall k,\quad \operatorname{BregmanGradOpt}\left(g,\,G,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \operatorname{composite}\left(f,\,g,\,x\left(k\right)\right) = \operatorname{composite}\left(f,\,g,\,u\right)
$$

## Theorem: `bregmanProximal_tendsto`

[Source](../../QuasiNewtonConvergence/Bregman.lean#L468)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x: \mathbb{N}\to E$; $u: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\operatorname{ConvexFirstOrder}\left(h,\,\operatorname{dh}\right)\\[4pt]\forall v,\quad F\left(u\right) \le F\left(v\right)\\[4pt]\forall k,\quad \operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} F\left(x\left(k\right)\right) = F\left(u\right)
$$


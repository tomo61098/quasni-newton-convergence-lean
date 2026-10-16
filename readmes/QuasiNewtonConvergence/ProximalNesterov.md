# ProximalNesterov

Accelerated proximal methods.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/ProximalNesterov.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [ProximalGradient](ProximalGradient.md).

## Definition: `SegmentConvex`

[Source](../../QuasiNewtonConvergence/ProximalNesterov.lean#L11)

Let $F: E\to \mathbb{R}$.

Define

$$
\operatorname{SegmentConvex}\left(F\right) \Longleftrightarrow \forall x,u\in E,\theta\in \mathbb{R},\quad 0 \le \theta \Longrightarrow \left(\theta \le 1 \Longrightarrow F\left(\left(1 - \theta\right) \, x + \theta \, u\right) \le \left(1 - \theta\right) \, F\left(x\right) + \theta \, F\left(u\right)\right)
$$

## Theorem: `proximalNesterov_step`

[Source](../../QuasiNewtonConvergence/ProximalNesterov.lean#L17)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, A, a, \theta: \mathbb{R}$; $x, z, y, x', z', u: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 \le A\\[4pt]0 < a\\[4pt]0 \le \theta\\[4pt]\theta \le 1\\[4pt]\left(A + a\right) \, \theta = a\\[4pt]\left(A + a\right) \, L \, \theta^{2} = 1\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{SegmentConvex}\left(\operatorname{composite}\left(f,\,g\right)\right)\\[4pt]y = \left(1 - \theta\right) \, x + \theta \, z\\[4pt]x' = \left(1 - \theta\right) \, x + \theta \, z'\\[4pt]\operatorname{ProxOpt}\left(g,\,G,\,L,\,y,\,x'\right)
\end{gathered}
$$

Then

$$
\left(A + a\right) \, \left(\operatorname{composite}\left(f,\,g,\,x'\right) - \operatorname{composite}\left(f,\,g,\,u\right)\right) + \frac{\left\|z' - u\right\|^{2}}{2} \le A \, \left(\operatorname{composite}\left(f,\,g,\,x\right) - \operatorname{composite}\left(f,\,g,\,u\right)\right) + \frac{\left\|z - u\right\|^{2}}{2}
$$

## Theorem: `proximalNesterov_weighted_rate`

[Source](../../QuasiNewtonConvergence/ProximalNesterov.lean#L70)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $A, a, \theta: \mathbb{N}\to \mathbb{R}$; $x, z, y: \mathbb{N}\to E$; $u: E$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{SegmentConvex}\left(\operatorname{composite}\left(f,\,g\right)\right)\\[4pt]A\left(0\right) = 0\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad 0 \le A\left(k\right)\\[4pt]\forall k,\quad 0 < a\left(k\right)\\[4pt]\forall k,\quad 0 \le \theta\left(k\right)\\[4pt]\forall k,\quad \theta\left(k\right) \le 1\\[4pt]\forall k,\quad A\left(k + 1\right) = A\left(k\right) + a\left(k\right)\\[4pt]\forall k,\quad \left(A\left(k\right) + a\left(k\right)\right) \, \theta\left(k\right) = a\left(k\right)\\[4pt]\forall k,\quad \left(A\left(k\right) + a\left(k\right)\right) \, L \, \theta\left(k\right)^{2} = 1\\[4pt]\forall k,\quad y\left(k\right) = \left(1 - \theta\left(k\right)\right) \, x\left(k\right) + \theta\left(k\right) \, z\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \left(1 - \theta\left(k\right)\right) \, x\left(k\right) + \theta\left(k\right) \, z\left(k + 1\right)\\[4pt]\forall k,\quad \operatorname{ProxOpt}\left(g,\,G,\,L,\,y\left(k\right),\,x\left(k + 1\right)\right)
\end{gathered}
$$

Then

$$
A\left(n\right) \, \left(\operatorname{composite}\left(f,\,g,\,x\left(n\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right)\right) \le \frac{\left\|x\left(0\right) - u\right\|^{2}}{2}
$$

## Theorem: `proximalNesterov_weight_growth`

[Source](../../QuasiNewtonConvergence/ProximalNesterov.lean#L103)

Let $L: \mathbb{R}$; $A, a, \theta: \mathbb{N}\to \mathbb{R}$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\forall k,\quad 0 \le A\left(k\right)\\[4pt]\forall k,\quad 0 < a\left(k\right)\\[4pt]\forall k,\quad A\left(k + 1\right) = A\left(k\right) + a\left(k\right)\\[4pt]\forall k,\quad \left(A\left(k\right) + a\left(k\right)\right) \, \theta\left(k\right) = a\left(k\right)\\[4pt]\forall k,\quad \left(A\left(k\right) + a\left(k\right)\right) \, L \, \theta\left(k\right)^{2} = 1
\end{gathered}
$$

Then

$$
\frac{n^{2}}{4 \, L} \le A\left(n\right)
$$

## Theorem: `proximalNesterov_quadratic_rate`

[Source](../../QuasiNewtonConvergence/ProximalNesterov.lean#L144)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L: \mathbb{R}$; $A, a, \theta: \mathbb{N}\to \mathbb{R}$; $x, z, y: \mathbb{N}\to E$; $u: E$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{ConvexFirstOrder}\left(f,\,G\right)\\[4pt]\operatorname{SegmentConvex}\left(\operatorname{composite}\left(f,\,g\right)\right)\\[4pt]A\left(0\right) = 0\\[4pt]z\left(0\right) = x\left(0\right)\\[4pt]\forall k,\quad 0 \le A\left(k\right)\\[4pt]\forall k,\quad 0 < a\left(k\right)\\[4pt]\forall k,\quad 0 \le \theta\left(k\right)\\[4pt]\forall k,\quad \theta\left(k\right) \le 1\\[4pt]\forall k,\quad A\left(k + 1\right) = A\left(k\right) + a\left(k\right)\\[4pt]\forall k,\quad \left(A\left(k\right) + a\left(k\right)\right) \, \theta\left(k\right) = a\left(k\right)\\[4pt]\forall k,\quad \left(A\left(k\right) + a\left(k\right)\right) \, L \, \theta\left(k\right)^{2} = 1\\[4pt]\forall k,\quad y\left(k\right) = \left(1 - \theta\left(k\right)\right) \, x\left(k\right) + \theta\left(k\right) \, z\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = \left(1 - \theta\left(k\right)\right) \, x\left(k\right) + \theta\left(k\right) \, z\left(k + 1\right)\\[4pt]\forall k,\quad \operatorname{ProxOpt}\left(g,\,G,\,L,\,y\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall v,\quad \operatorname{composite}\left(f,\,g,\,u\right) \le \operatorname{composite}\left(f,\,g,\,v\right)\\[4pt]0 < n
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,x\left(n\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le \frac{2 \, L \, \left\|x\left(0\right) - u\right\|^{2}}{n^{2}}
$$

## Theorem: `restartedProximalNesterov_strong_rate`

[Source](../../QuasiNewtonConvergence/ProximalNesterov.lean#L184)

Let $F: E\to \mathbb{R}$; $L, \mu, N: \mathbb{R}$; $u: E$; $x: \mathbb{N}\to E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]0 < N\\[4pt]\forall v,\quad \frac{\mu}{2} \, \left\|v - u\right\|^{2} \le F\left(v\right) - F\left(u\right)\\[4pt]\forall k,\quad F\left(x\left(k + 1\right)\right) - F\left(u\right) \le \frac{2 \, L \, \left\|x\left(k\right) - u\right\|^{2}}{N^{2}}\\[4pt]4 \, L < \mu \, N^{2}
\end{gathered}
$$

Then

$$
\begin{gathered}
F\left(x\left(k\right)\right) - F\left(u\right) \le \left(\frac{4 \, L}{\mu \, N^{2}}\right)^{k} \, \left(F\left(x\left(0\right)\right) - F\left(u\right)\right)\\
\land\quad \frac{4 \, L}{\mu \, N^{2}} < 1
\end{gathered}
$$


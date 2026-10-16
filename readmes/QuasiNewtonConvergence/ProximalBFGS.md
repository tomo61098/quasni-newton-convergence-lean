# ProximalBFGS

Variable-metric proximal methods.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/ProximalBFGS.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [ProximalGradient](ProximalGradient.md), [BroydenUpdates](BroydenUpdates.md).

## Definition: `MetricProximalOptimality`

[Source](../../QuasiNewtonConvergence/ProximalBFGS.lean#L14)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $x, z: E$.

Define

$$
\operatorname{MetricProxOpt}\left(g,\,G,\,B,\,x,\,z\right) \Longleftrightarrow \forall u,\quad g\left(u\right) - g\left(z\right) \ge \left\langle -G\left(x\right) - B\left(z - x\right),u - z\right\rangle
$$

## Theorem: `metricProximal_descent`

[Source](../../QuasiNewtonConvergence/ProximalBFGS.lean#L19)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, m: \mathbb{R}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $x, z: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\forall v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(v\right),v\right\rangle\\[4pt]\operatorname{MetricProxOpt}\left(g,\,G,\,B,\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) \le \operatorname{composite}\left(f,\,g,\,x\right) - \left(m - \frac{L}{2}\right) \, \left\|z - x\right\|^{2}
$$

## Theorem: `proximalBFGS_descent`

[Source](../../QuasiNewtonConvergence/ProximalBFGS.lean#L36)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, m: \mathbb{R}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, x, z: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\forall v,\quad m \, \left\|v\right\|^{2} \le \left\langle \operatorname{bfgsUpdateMap}\left(B,\,s,\,y,\,v\right),v\right\rangle\\[4pt]\operatorname{MetricProxOpt}\left(g,\,G,\,\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right),\,x,\,z\right)
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,z\right) \le \operatorname{composite}\left(f,\,g,\,x\right) - \left(m - \frac{L}{2}\right) \, \left\|z - x\right\|^{2}
$$

## Theorem: `metricProximal_steps_summable`

[Source](../../QuasiNewtonConvergence/ProximalBFGS.lean#L52)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, m: \mathbb{R}$; $x: \mathbb{N}\to E$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $\ell_{\rm low}: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]0 < m - \frac{L}{2}\\[4pt]\forall k,v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(k,\,v\right),v\right\rangle\\[4pt]\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall k,\quad \ell_{\rm low} \le \operatorname{composite}\left(f,\,g,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\sum_{k=0}^{\infty}\left|\left\|x\left(k + 1\right) - x\left(k\right)\right\|^{2}\right|<\infty
$$

## Theorem: `metricProximal_steps_tendsto_zero`

[Source](../../QuasiNewtonConvergence/ProximalBFGS.lean#L85)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, m: \mathbb{R}$; $x: \mathbb{N}\to E$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $\ell_{\rm low}: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]0 < m - \frac{L}{2}\\[4pt]\forall k,v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(k,\,v\right),v\right\rangle\\[4pt]\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall k,\quad \ell_{\rm low} \le \operatorname{composite}\left(f,\,g,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \left\|x\left(k + 1\right) - x\left(k\right)\right\|^{2} = 0
$$

## Theorem: `metricProximal_linear_rate`

[Source](../../QuasiNewtonConvergence/ProximalBFGS.lean#L103)

Let $f, g: E\to \mathbb{R}$; $G: E\to E$; $L, m, C: \mathbb{R}$; $x: \mathbb{N}\to E$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]0 < m - \frac{L}{2}\\[4pt]0 < C\\[4pt]\forall k,v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(k,\,v\right),v\right\rangle\\[4pt]\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall k,\quad \operatorname{composite}\left(f,\,g,\,x\left(k + 1\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le C \, \left\|x\left(k + 1\right) - x\left(k\right)\right\|^{2}
\end{gathered}
$$

Then

$$
\operatorname{composite}\left(f,\,g,\,x\left(k\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right) \le \left(\frac{C}{C + \left(m - \frac{L}{2}\right)}\right)^{k} \, \left(\operatorname{composite}\left(f,\,g,\,x\left(0\right)\right) - \operatorname{composite}\left(f,\,g,\,u\right)\right)
$$


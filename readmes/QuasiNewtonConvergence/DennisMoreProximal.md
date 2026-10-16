# DennisMoreProximal

Smooth and proximal Dennis–Moré conditions.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/DennisMoreProximal.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [ProximalBFGS](ProximalBFGS.md), [Newton](Newton.md).

## Definition: `DennisMoreOnSteps`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L18)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $\delta: \mathbb{N}\to \mathbb{R}$.

Define

$$
\operatorname{DennisMoreOnSteps}\left(B,\,H_\star,\,x,\,\delta\right) \Longleftrightarrow \forall k,\quad \left\|\left(B\left(k\right) - H_\star\right)\left(x\left(k + 1\right) - x\left(k\right)\right)\right\| \le \delta\left(k\right) \, \left\|x\left(k + 1\right) - x\left(k\right)\right\|
$$

## Definition: `dennisMoreRatio`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L25)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $k: \mathbb{N}$.

Define

$$
\operatorname{dennisMoreRatio}\left(B,\,H_\star,\,x,\,k\right) := \frac{\left\|\left(B\left(k\right) - H_\star\right)\left(x\left(k + 1\right) - x\left(k\right)\right)\right\|}{\left\|x\left(k + 1\right) - x\left(k\right)\right\|}
$$

## Definition: `DennisMoreCriterion`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L30)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$.

Define

$$
\operatorname{DennisMoreCriterion}\left(B,\,H_\star,\,x\right) \Longleftrightarrow \lim_{k\to\infty} \operatorname{dennisMoreRatio}\left(B,\,H_\star,\,x\right)\left(k\right) = 0
$$

## Theorem: `dennisMoreRatio_nonneg`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L35)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $k: \mathbb{N}$.

Then

$$
0 \le \operatorname{dennisMoreRatio}\left(B,\,H_\star,\,x,\,k\right)
$$

## Theorem: `dennisMoreRatio_bounds`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L41)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$.

Then

$$
\operatorname{DennisMoreOnSteps}\left(B,\,H_\star,\,x,\,\operatorname{dennisMoreRatio}\left(B,\,H_\star,\,x\right)\right)
$$

## Theorem: `metricProximal_step_bound`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L56)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $x, z, x_\star: E$; $m, M, G: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < m\\[4pt]0 \le M\\[4pt]0 \le G\\[4pt]\forall v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(v\right),v\right\rangle\\[4pt]\forall v,\quad \left\|B\left(v\right)\right\| \le M \, \left\|v\right\|\\[4pt]\left\|G\left(x\right) - G\left(x_\star\right)\right\| \le G \, \left\|x - x_\star\right\|\\[4pt]\operatorname{MetricProxOpt}\left(g,\,G,\,B,\,x,\,z\right)\\[4pt]\forall u,\quad g\left(u\right) - g\left(x_\star\right) \ge \left\langle -G\left(x_\star\right),u - x_\star\right\rangle
\end{gathered}
$$

Then

$$
\left\|z - x\right\| \le \left(1 + \frac{M + G}{m}\right) \, \left\|x - x_\star\right\|
$$

## Theorem: `proximalDennisMore_one_step`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L122)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $H_\star, B: \mathcal{L}_{\mathbb{R}}(E,E)$; $x, z, x_\star: E$; $\mu, L, C, \delta: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]0 \le L\\[4pt]0 \le \delta\\[4pt]\forall v,\quad \mu \, \left\|v\right\|^{2} \le \left\langle H_\star\left(v\right),v\right\rangle\\[4pt]\operatorname{MetricProxOpt}\left(g,\,G,\,B,\,x,\,z\right)\\[4pt]\forall u,\quad g\left(u\right) - g\left(x_\star\right) \ge \left\langle -G\left(x_\star\right),u - x_\star\right\rangle\\[4pt]\left\|G\left(x\right) - G\left(x_\star\right) - H_\star\left(x - x_\star\right)\right\| \le L \, \left\|x - x_\star\right\|^{2}\\[4pt]\left\|\left(B - H_\star\right)\left(z - x\right)\right\| \le \delta \, \left\|z - x\right\|\\[4pt]\left\|z - x\right\| \le C \, \left\|x - x_\star\right\|
\end{gathered}
$$

Then

$$
\left\|z - x_\star\right\| \le \frac{\delta \, C + L \, \left\|x - x_\star\right\|}{\mu} \, \left\|x - x_\star\right\|
$$

## Theorem: `proximalDennisMore_superlinear`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L191)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $x_\star: E$; $\delta: \mathbb{N}\to \mathbb{R}$; $\mu, L, C: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]0 \le L\\[4pt]0 \le C\\[4pt]\forall v,\quad \mu \, \left\|v\right\|^{2} \le \left\langle H_\star\left(v\right),v\right\rangle\\[4pt]\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall u,\quad g\left(u\right) - g\left(x_\star\right) \ge \left\langle -G\left(x_\star\right),u - x_\star\right\rangle\\[4pt]\forall k,\quad \left\|G\left(x\left(k\right)\right) - G\left(x_\star\right) - H_\star\left(x\left(k\right) - x_\star\right)\right\| \le L \, \left\|x\left(k\right) - x_\star\right\|^{2}\\[4pt]\operatorname{DennisMoreOnSteps}\left(B,\,H_\star,\,x,\,\delta\right)\\[4pt]\forall k,\quad 0 \le \delta\left(k\right)\\[4pt]\forall k,\quad \left\|x\left(k + 1\right) - x\left(k\right)\right\| \le C \, \left\|x\left(k\right) - x_\star\right\|\\[4pt]\lim_{k\to\infty} x\left(k\right) = x_\star\\[4pt]\lim_{k\to\infty} \delta\left(k\right) = 0
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|x\left(k + 1\right) - x_\star\right\|}{\left\|x\left(k\right) - x_\star\right\|} = 0
$$

## Theorem: `proximalDennisMore_standard`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L242)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $H_\star: \mathcal{L}_{\mathbb{R}}(E,E)$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $x_\star: E$; $\mu, L, C: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]0 \le L\\[4pt]0 \le C\\[4pt]\forall v,\quad \mu \, \left\|v\right\|^{2} \le \left\langle H_\star\left(v\right),v\right\rangle\\[4pt]\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall u,\quad g\left(u\right) - g\left(x_\star\right) \ge \left\langle -G\left(x_\star\right),u - x_\star\right\rangle\\[4pt]\forall k,\quad \left\|G\left(x\left(k\right)\right) - G\left(x_\star\right) - H_\star\left(x\left(k\right) - x_\star\right)\right\| \le L \, \left\|x\left(k\right) - x_\star\right\|^{2}\\[4pt]\forall k,\quad \left\|x\left(k + 1\right) - x\left(k\right)\right\| \le C \, \left\|x\left(k\right) - x_\star\right\|\\[4pt]\lim_{k\to\infty} x\left(k\right) = x_\star\\[4pt]\operatorname{DennisMoreCriterion}\left(B,\,H_\star,\,x\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|x\left(k + 1\right) - x_\star\right\|}{\left\|x\left(k\right) - x_\star\right\|} = 0
$$

## Theorem: `dennisMore_gradient_remainder`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L266)

Let $G: E\to E$; $\mathcal{H}: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $L: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|
\end{gathered}
$$

Then

$$
\left\|G\left(x\right) - G\left(x_\star\right) - \mathcal{H}\left(x_\star,\,x - x_\star\right)\right\| \le L \, \left\|x - x_\star\right\|^{2}
$$

## Theorem: `proximalDennisMore_of_uniform_metrics`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L287)

Let $g: E\to \mathbb{R}$; $G: E\to E$; $\mathcal{H}: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $x_\star: E$; $\delta: \mathbb{N}\to \mathbb{R}$; $\mu, m, M, G, L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]0 < m\\[4pt]0 \le M\\[4pt]0 \le G\\[4pt]0 \le L\\[4pt]\forall v,\quad \mu \, \left\|v\right\|^{2} \le \left\langle \mathcal{H}\left(x_\star,\,v\right),v\right\rangle\\[4pt]\forall k,v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(k,\,v\right),v\right\rangle\\[4pt]\forall k,v,\quad \left\|B\left(k,\,v\right)\right\| \le M \, \left\|v\right\|\\[4pt]\forall k,\quad \left\|G\left(x\left(k\right)\right) - G\left(x_\star\right)\right\| \le G \, \left\|x\left(k\right) - x_\star\right\|\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|\\[4pt]\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)\\[4pt]\forall u,\quad g\left(u\right) - g\left(x_\star\right) \ge \left\langle -G\left(x_\star\right),u - x_\star\right\rangle\\[4pt]\operatorname{DennisMoreOnSteps}\left(B,\,\mathcal{H}\left(x_\star\right),\,x,\,\delta\right)\\[4pt]\forall k,\quad 0 \le \delta\left(k\right)\\[4pt]\lim_{k\to\infty} x\left(k\right) = x_\star\\[4pt]\lim_{k\to\infty} \delta\left(k\right) = 0
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|x\left(k + 1\right) - x_\star\right\|}{\left\|x\left(k\right) - x_\star\right\|} = 0
$$

## Theorem: `dennisMore_smooth_superlinear`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L331)

Let $G: E\to E$; $\mathcal{H}: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $x_\star: E$; $\delta: \mathbb{N}\to \mathbb{R}$; $\mu, m, M, G, L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]0 < m\\[4pt]0 \le M\\[4pt]0 \le G\\[4pt]0 \le L\\[4pt]\forall v,\quad \mu \, \left\|v\right\|^{2} \le \left\langle \mathcal{H}\left(x_\star,\,v\right),v\right\rangle\\[4pt]\forall k,v,\quad m \, \left\|v\right\|^{2} \le \left\langle B\left(k,\,v\right),v\right\rangle\\[4pt]\forall k,v,\quad \left\|B\left(k,\,v\right)\right\| \le M \, \left\|v\right\|\\[4pt]\forall k,\quad \left\|G\left(x\left(k\right)\right) - G\left(x_\star\right)\right\| \le G \, \left\|x\left(k\right) - x_\star\right\|\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|\\[4pt]G\left(x_\star\right) = 0\\[4pt]\forall k,\quad G\left(x\left(k\right)\right) + B\left(k,\,x\left(k + 1\right) - x\left(k\right)\right) = 0\\[4pt]\operatorname{DennisMoreOnSteps}\left(B,\,\mathcal{H}\left(x_\star\right),\,x,\,\delta\right)\\[4pt]\forall k,\quad 0 \le \delta\left(k\right)\\[4pt]\lim_{k\to\infty} x\left(k\right) = x_\star\\[4pt]\lim_{k\to\infty} \delta\left(k\right) = 0
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|x\left(k + 1\right) - x_\star\right\|}{\left\|x\left(k\right) - x_\star\right\|} = 0
$$

## Structure: `ProximalBFGSRun`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L380)

Let $g: E\to \mathbb{R}$; $G: E\to E$.

The record consists of the following fields and conditions.

**x**

$$
x: \mathbb{N}\to E
$$

**B**

$$
B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)
$$

**step**

$$
\forall k,\quad \operatorname{MetricProxOpt}\left(g,\,G,\,B\left(k\right),\,x\left(k\right),\,x\left(k + 1\right)\right)
$$

**update**

$$
\forall k,\quad B\left(k + 1\right) = \operatorname{bfgsUpdateMap}\left(B\left(k\right),\,x\left(k + 1\right) - x\left(k\right),\,G\left(x\left(k + 1\right)\right) - G\left(x\left(k\right)\right)\right)
$$


## Theorem: `ProximalBFGSRun.dennisMore_superlinear`

[Source](../../QuasiNewtonConvergence/DennisMoreProximal.lean#L390)

Let $\operatorname{run}: \operatorname{ProximalBFGSRun}\left(g,\,G\right)$; $\mathcal{H}: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $x_\star: E$; $\delta: \mathbb{N}\to \mathbb{R}$; $\mu, m, M, G, L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \mu\\[4pt]0 < m\\[4pt]0 \le M\\[4pt]0 \le G\\[4pt]0 \le L\\[4pt]\forall v,\quad \mu \, \left\|v\right\|^{2} \le \left\langle \mathcal{H}\left(x_\star,\,v\right),v\right\rangle\\[4pt]\forall k,v,\quad m \, \left\|v\right\|^{2} \le \left\langle \operatorname{run}_{B}\left(k,\,v\right),v\right\rangle\\[4pt]\forall k,v,\quad \left\|\operatorname{run}_{B}\left(k,\,v\right)\right\| \le M \, \left\|v\right\|\\[4pt]\forall k,\quad \left\|G\left(\operatorname{run}_{x}\left(k\right)\right) - G\left(x_\star\right)\right\| \le G \, \left\|\operatorname{run}_{x}\left(k\right) - x_\star\right\|\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|\\[4pt]\forall u,\quad g\left(u\right) - g\left(x_\star\right) \ge \left\langle -G\left(x_\star\right),u - x_\star\right\rangle\\[4pt]\operatorname{DennisMoreOnSteps}\left(\operatorname{run}_{B},\,\mathcal{H}\left(x_\star\right),\,\operatorname{run}_{x},\,\delta\right)\\[4pt]\forall k,\quad 0 \le \delta\left(k\right)\\[4pt]\lim_{k\to\infty} \operatorname{run}_{x}\left(k\right) = x_\star\\[4pt]\lim_{k\to\infty} \delta\left(k\right) = 0
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|\operatorname{run}_{x}\left(k + 1\right) - x_\star\right\|}{\left\|\operatorname{run}_{x}\left(k\right) - x_\star\right\|} = 0
$$


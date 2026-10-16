# PrimalPathFollowing

Primal barrier path-following bounds.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains.

Definitions from other modules: [KarmarkarProjective](KarmarkarProjective.md).

## Definition: `primalLogBarrierObjective`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L22)

Let $n: \mathbb{N}$; $c, x: I_{n}\to \mathbb{R}$; $t: \mathbb{R}$.

Define

$$
\operatorname{Barrier}\left(c,\,x,\,t\right) := t \, \operatorname{cost}\left(c,\,x\right) - \left(\sum_{i} \log\left(x\left(i\right)\right)\right)
$$

## Definition: `PrimalCentralStationarity`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L26)

Let $n: \mathbb{N}$; $c, x: I_{n}\to \mathbb{R}$; $t: \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$.

Define

$$
\operatorname{Central}\left(c,\,x,\,t,\,\mathcal{F}\right) \Longleftrightarrow \forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} \left(t \, c\left(i\right) - x\left(i\right)^{-1}\right) \, \left(x\left(i\right) - z\left(i\right)\right) = 0
$$

## Theorem: `primal_log_barrier_gap`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L34)

Let $n: \mathbb{N}$; $c, x, z: I_{n}\to \mathbb{R}$; $t: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < t\\[4pt]\forall i,\quad 0 < x\left(i\right)\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\sum_{i} \left(t \, c\left(i\right) - x\left(i\right)^{-1}\right) \, \left(x\left(i\right) - z\left(i\right)\right) = 0
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\right) - \operatorname{cost}\left(c,\,z\right) \le \frac{n}{t}
$$

## Definition: `PrimalApproxCentralStationarity`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L59)

Let $n: \mathbb{N}$; $c, x: I_{n}\to \mathbb{R}$; $t, \beta: \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$.

Define

$$
\operatorname{ApproxCentral}\left(c,\,x,\,t,\,\beta,\,\mathcal{F}\right) \Longleftrightarrow \exists e\in I_{n}\to \mathbb{R},\quad \left(\forall i,\quad \left|e\left(i\right)\right| \le \beta\right) \land \left(\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} \left(t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x\left(i\right)}\right) \, \left(x\left(i\right) - z\left(i\right)\right) = 0\right)
$$

## Theorem: `primal_approx_log_barrier_gap`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L68)

Let $n: \mathbb{N}$; $c, x, z, e: I_{n}\to \mathbb{R}$; $t, \beta: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < t\\[4pt]\beta < 1\\[4pt]\forall i,\quad 0 < x\left(i\right)\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall i,\quad \left|e\left(i\right)\right| \le \beta\\[4pt]\sum_{i} \left(t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x\left(i\right)}\right) \, \left(x\left(i\right) - z\left(i\right)\right) = 0
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\right) - \operatorname{cost}\left(c,\,z\right) \le \frac{n \, \left(1 + \beta\right)}{t}
$$

## Theorem: `primal_central_path_gap`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L107)

Let $n: \mathbb{N}$; $c, x, z: I_{n}\to \mathbb{R}$; $t: \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $\operatorname{hzfeas}: z\in\mathcal{F}$.

Assume all of the following.

$$
\begin{gathered}
0 < t\\[4pt]\forall i,\quad 0 < x\left(i\right)\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\operatorname{Central}\left(c,\,x,\,t,\,\mathcal{F}\right)
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\right) - \operatorname{cost}\left(c,\,z\right) \le \frac{n}{t}
$$

## Definition: `primalBarrierParameter`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L117)

Let $t_{0}, \gamma: \mathbb{R}$; $k: \mathbb{N}$.

Define

$$
\operatorname{BarrierParameter}\left(t_{0},\,\gamma,\,k\right) := t_{0} \, \left(1 + \gamma\right)^{k}
$$

## Theorem: `primal_central_path_geometric_rate`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L122)

Let $n: \mathbb{N}$; $c, z: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $t_{0}, \gamma: \mathbb{R}$; $\operatorname{hzfeas}: z\in\mathcal{F}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < t_{0}\\[4pt]0 < \gamma\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \operatorname{Central}\left(c,\,x\left(k\right),\,\operatorname{BarrierParameter}\left(t_{0},\,\gamma,\,k\right),\,\mathcal{F}\right)
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) - \operatorname{cost}\left(c,\,z\right) \le \frac{n}{t_{0}} \, \left(\frac{1}{1 + \gamma}\right)^{k}
$$

## Theorem: `primal_barrier_parameter_accuracy`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L148)

Let $n: \mathbb{N}$; $t_{0}, \gamma, \varepsilon: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]0 < t_{0}\\[4pt]0 < \gamma\\[4pt]0 < \varepsilon\\[4pt]\log\left(\frac{n}{\varepsilon \, t_{0}}\right) \le k \, \log\left(1 + \gamma\right)
\end{gathered}
$$

Then

$$
\frac{n}{\operatorname{BarrierParameter}\left(t_{0},\,\gamma,\,k\right)} \le \varepsilon
$$

## Theorem: `primal_barrier_parameter_accuracy_real`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L169)

Let $M, t_{0}, \gamma, \varepsilon: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < M\\[4pt]0 < t_{0}\\[4pt]0 < \gamma\\[4pt]0 < \varepsilon\\[4pt]\log\left(\frac{M}{\varepsilon \, t_{0}}\right) \le k \, \log\left(1 + \gamma\right)
\end{gathered}
$$

Then

$$
\frac{M}{\operatorname{BarrierParameter}\left(t_{0},\,\gamma,\,k\right)} \le \varepsilon
$$

## Theorem: `primal_approx_central_path_accuracy`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L190)

Let $n: \mathbb{N}$; $c, z: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $t_{0}, \gamma, \beta, \varepsilon: \mathbb{R}$; $\operatorname{hzfeas}: z\in\mathcal{F}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]0 < t_{0}\\[4pt]0 < \gamma\\[4pt]0 \le \beta\\[4pt]\beta < 1\\[4pt]0 < \varepsilon\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \operatorname{ApproxCentral}\left(c,\,x\left(k\right),\,\operatorname{BarrierParameter}\left(t_{0},\,\gamma,\,k\right),\,\beta,\,\mathcal{F}\right)\\[4pt]\log\left(\frac{n \, \left(1 + \beta\right)}{\varepsilon \, t_{0}}\right) \le k \, \log\left(1 + \gamma\right)
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) - \operatorname{cost}\left(c,\,z\right) \le \varepsilon
$$

## Theorem: `primal_central_path_accuracy`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L218)

Let $n: \mathbb{N}$; $c, z: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $t_{0}, \gamma, \varepsilon: \mathbb{R}$; $\operatorname{hzfeas}: z\in\mathcal{F}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]0 < t_{0}\\[4pt]0 < \gamma\\[4pt]0 < \varepsilon\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \operatorname{Central}\left(c,\,x\left(k\right),\,\operatorname{BarrierParameter}\left(t_{0},\,\gamma,\,k\right),\,\mathcal{F}\right)\\[4pt]\log\left(\frac{n}{\varepsilon \, t_{0}}\right) \le k \, \log\left(1 + \gamma\right)
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) - \operatorname{cost}\left(c,\,z\right) \le \varepsilon
$$

## Theorem: `primal_short_step_log_growth`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L241)

Let $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n
\end{gathered}
$$

Then

$$
\frac{1}{8 \, \sqrt{n}} \le \log\left(1 + \frac{1}{4 \, \sqrt{n}}\right)
$$

## Theorem: `primal_short_step_central_path_accuracy`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L267)

Let $n: \mathbb{N}$; $c, z: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $t_{0}, \varepsilon: \mathbb{R}$; $\operatorname{hzfeas}: z\in\mathcal{F}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]0 < t_{0}\\[4pt]0 < \varepsilon\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \operatorname{Central}\left(c,\,x\left(k\right),\,\operatorname{BarrierParameter}\left(t_{0},\,\frac{1}{4 \, \sqrt{n}},\,k\right),\,\mathcal{F}\right)\\[4pt]8 \, \sqrt{n} \, \log\left(\frac{n}{\varepsilon \, t_{0}}\right) \le k
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) - \operatorname{cost}\left(c,\,z\right) \le \varepsilon
$$

## Theorem: `primal_short_step_log_threshold`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L307)

Let $n: \mathbb{N}$; $M, t_{0}, \varepsilon: \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]8 \, \sqrt{n} \, \log\left(\frac{M}{\varepsilon \, t_{0}}\right) \le k
\end{gathered}
$$

Then

$$
\log\left(\frac{M}{\varepsilon \, t_{0}}\right) \le k \, \log\left(1 + \frac{1}{4 \, \sqrt{n}}\right)
$$

## Theorem: `primal_short_step_approx_accuracy`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L334)

Let $n: \mathbb{N}$; $c, z: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $t_{0}, \beta, \varepsilon: \mathbb{R}$; $\operatorname{hzfeas}: z\in\mathcal{F}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]0 < t_{0}\\[4pt]0 \le \beta\\[4pt]\beta < 1\\[4pt]0 < \varepsilon\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \operatorname{ApproxCentral}\left(c,\,x\left(k\right),\,\operatorname{BarrierParameter}\left(t_{0},\,\frac{1}{4 \, \sqrt{n}},\,k\right),\,\beta,\,\mathcal{F}\right)\\[4pt]8 \, \sqrt{n} \, \log\left(\frac{n \, \left(1 + \beta\right)}{\varepsilon \, t_{0}}\right) \le k
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) - \operatorname{cost}\left(c,\,z\right) \le \varepsilon
$$

## Theorem: `primal_newton_short_step_log_growth`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L362)

Let $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n
\end{gathered}
$$

Then

$$
\frac{1}{32 \, \sqrt{n}} \le \log\left(1 + \frac{1}{16 \, \sqrt{n}}\right)
$$

## Theorem: `primal_newton_short_step_approx_accuracy`

[Source](../../QuasiNewtonConvergence/PrimalPathFollowing.lean#L388)

Let $n: \mathbb{N}$; $c, z: I_{n}\to \mathbb{R}$; $x: \mathbb{N}\to I_{n}\to \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$; $t_{0}, \beta, \varepsilon: \mathbb{R}$; $\operatorname{hzfeas}: z\in\mathcal{F}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
1 \le n\\[4pt]0 < t_{0}\\[4pt]0 \le \beta\\[4pt]\beta < 1\\[4pt]0 < \varepsilon\\[4pt]\forall i,\quad 0 \le z\left(i\right)\\[4pt]\forall k,i,\quad 0 < x\left(k,\,i\right)\\[4pt]\forall k,\quad \operatorname{ApproxCentral}\left(c,\,x\left(k\right),\,\operatorname{BarrierParameter}\left(t_{0},\,\frac{1}{16 \, \sqrt{n}},\,k\right),\,\beta,\,\mathcal{F}\right)\\[4pt]32 \, \sqrt{n} \, \log\left(\frac{n \, \left(1 + \beta\right)}{\varepsilon \, t_{0}}\right) \le k
\end{gathered}
$$

Then

$$
\operatorname{cost}\left(c,\,x\left(k\right)\right) - \operatorname{cost}\left(c,\,z\right) \le \varepsilon
$$


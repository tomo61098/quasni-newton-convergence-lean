# LogBarrierNewtonInvariant

Log-barrier Newton invariants.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [KarmarkarProjective](KarmarkarProjective.md).

## Theorem: `orthogonalProjection_parameter_perturb_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L28)

Let $E$ a set; $U: \operatorname{Subspaces}_{\mathbb{R}}(E)$; $v, e: E$; $s: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
0 \le s
\end{gathered}
$$

Then

$$
\left\|P_{U}\left(v + s \, \left(v + e\right)\right)\right\| \le \left\|P_{U}\left(v\right)\right\| + s \, \left(\left\|P_{U}\left(v\right)\right\| + \left\|e\right\|\right)
$$

## Theorem: `logBarrier_ones_norm`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L57)

Let $n: \mathbb{N}$.

Then

$$
\left\|\iota_2\left(\left(i\in I_{n}\mapsto 1\right)\right)\right\| = \sqrt{n}
$$

## Theorem: `logBarrier_projected_cost_perturb_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L71)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $v: \mathbb{R}^{n}$; $s: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
0 \le s
\end{gathered}
$$

Set

$$
e:=\iota_2\left(\left(i\in I_{n}\mapsto 1\right)\right)
$$

Then

$$
\left\|P_{U}\left(v + s \, \left(v + e\right)\right)\right\| \le \left\|P_{U}\left(v\right)\right\| + s \, \left(\left\|P_{U}\left(v\right)\right\| + \sqrt{n}\right)
$$

## Theorem: `logBarrier_newton_residual_identity`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L86)

Let $x, d: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
x \ne 0\\[4pt]x + d \ne 0
\end{gathered}
$$

Then

$$
\frac{1 - \left(\frac{d}{x}\right)^{2}}{x + d} = \frac{1}{x} - \frac{d}{x^{2}}
$$

## Theorem: `logBarrier_newton_coordinate_pos`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L93)

Let $x, d, \rho: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < x\\[4pt]\rho < 1\\[4pt]\left|\frac{d}{x}\right| \le \rho
\end{gathered}
$$

Then

$$
0 < x + d
$$

## Theorem: `logBarrier_local_norm_coordinate_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L106)

Let $n: \mathbb{N}$; $u: I_{n}\to \mathbb{R}$; $\rho: \mathbb{R}$; $i: I_{n}$.

Assume all of the following.

$$
\begin{gathered}
0 \le \rho\\[4pt]\sum_{i} u\left(i\right)^{2} \le \rho^{2}
\end{gathered}
$$

Then

$$
\left|u\left(i\right)\right| \le \rho
$$

## Theorem: `logBarrier_squared_residual_norm_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L118)

Let $n: \mathbb{N}$; $u: I_{n}\to \mathbb{R}$.

Then

$$
\sum_{i} \left(u\left(i\right)^{2}\right)^{2} \le \left(\sum_{i} u\left(i\right)^{2}\right)^{2}
$$

## Theorem: `logBarrier_full_newton_euclidean_residual_invariant`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L128)

Let $n: \mathbb{N}$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho < 1\\[4pt]\sum_{i} \left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2} \le \rho^{2}\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)
\end{gathered}
$$

Set

$$
x_+:=\left(i\mapsto x\left(i\right) + d\left(i\right)\right)
$$

Set

$$
e:=\left(i\mapsto -\left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2}\right)
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x_+\left(i\right)\\
\land\quad \forall i,\quad x_+\left(i\right) \, \left(t \, c\left(i\right) - \frac{1}{x_+\left(i\right)} - q\left(i\right)\right) = e\left(i\right)\\
\land\quad \left\|\iota_2\left(e\right)\right\| \le \rho^{2}\\
\land\quad \forall i,\quad t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x_+\left(i\right)} = q\left(i\right)
\end{gathered}
$$

## Theorem: `logBarrier_projected_gradient_of_residual`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L172)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $c, x, q, e: I_{n}\to \mathbb{R}$; $t, \beta: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
\forall i,\quad x\left(i\right) \ne 0\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x\left(i\right)} = q\left(i\right)\\[4pt]\iota_2\left(\left(i\mapsto x\left(i\right) \, q\left(i\right)\right)\right) \in U^{\perp}\\[4pt]\left\|\iota_2\left(e\right)\right\| \le \beta
\end{gathered}
$$

Then

$$
\left\|P_{U}\left(\iota_2\left(\left(i\mapsto t \, x\left(i\right) \, c\left(i\right) - 1\right)\right)\right)\right\| \le \beta
$$

## Theorem: `logBarrier_full_newton_projected_invariant`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L200)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho < 1\\[4pt]\sum_{i} \left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2} \le \rho^{2}\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)\\[4pt]\iota_2\left(\left(i\mapsto \left(x\left(i\right) + d\left(i\right)\right) \, q\left(i\right)\right)\right) \in U^{\perp}
\end{gathered}
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right) + d\left(i\right)\\
\land\quad \left\|P_{U}\left(\iota_2\left(\left(i\mapsto t \, \left(x\left(i\right) + d\left(i\right)\right) \, c\left(i\right) - 1\right)\right)\right)\right\| \le \rho^{2}
\end{gathered}
$$

## Theorem: `logBarrier_full_newton_residual_invariant`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L222)

Let $n: \mathbb{N}$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho < 1\\[4pt]\forall i,\quad \left|\frac{d\left(i\right)}{x\left(i\right)}\right| \le \rho\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)\\[4pt]\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} q\left(i\right) \, \left(x\left(i\right) + d\left(i\right) - z\left(i\right)\right) = 0
\end{gathered}
$$

Set

$$
x_+:=\left(i\mapsto x\left(i\right) + d\left(i\right)\right)
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x_+\left(i\right)\\
\land\quad \exists e\in I_{n}\to \mathbb{R},\quad \left(\forall i,\quad \left|e\left(i\right)\right| \le \rho^{2}\right) \land \left(\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} \left(t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x_+\left(i\right)}\right) \, \left(x_+\left(i\right) - z\left(i\right)\right) = 0\right)
\end{gathered}
$$

## Theorem: `logBarrier_full_newton_local_norm_invariant`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L264)

Let $n: \mathbb{N}$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho < 1\\[4pt]\sum_{i} \left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2} \le \rho^{2}\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)\\[4pt]\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} q\left(i\right) \, \left(x\left(i\right) + d\left(i\right) - z\left(i\right)\right) = 0
\end{gathered}
$$

Set

$$
x_+:=\left(i\mapsto x\left(i\right) + d\left(i\right)\right)
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x_+\left(i\right)\\
\land\quad \exists e\in I_{n}\to \mathbb{R},\quad \left(\forall i,\quad \left|e\left(i\right)\right| \le \rho^{2}\right) \land \left(\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} \left(t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x_+\left(i\right)}\right) \, \left(x_+\left(i\right) - z\left(i\right)\right) = 0\right)
\end{gathered}
$$

## Theorem: `logBarrier_short_step_pre_newton_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L288)

Let $s, \operatorname{lam}, \rho: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
1 \le s\\[4pt]0 \le \operatorname{lam}\\[4pt]\operatorname{lam} \le \frac{1}{4}\\[4pt]\rho \le \operatorname{lam} + \frac{1}{16 \, s} \, \left(s + \operatorname{lam}\right)
\end{gathered}
$$

Then

$$
\rho \le \frac{21}{64}
$$

## Theorem: `logBarrier_short_step_projection_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L306)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $v: \mathbb{R}^{n}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
1 \le n\\[4pt]\left\|P_{U}\left(v\right)\right\| \le \frac{1}{4}
\end{gathered}
$$

Set

$$
e:=\iota_2\left(\left(i\in I_{n}\mapsto 1\right)\right)
$$

Set

$$
s:=\frac{1}{16 \, \sqrt{n}}
$$

Then

$$
\left\|P_{U}\left(v + s \, \left(v + e\right)\right)\right\| \le \frac{21}{64}
$$

## Theorem: `logBarrier_full_newton_projected_quarter_invariant`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L341)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho \le \frac{21}{64}\\[4pt]\sum_{i} \left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2} \le \rho^{2}\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)\\[4pt]\iota_2\left(\left(i\mapsto \left(x\left(i\right) + d\left(i\right)\right) \, q\left(i\right)\right)\right) \in U^{\perp}
\end{gathered}
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right) + d\left(i\right)\\
\land\quad \left\|P_{U}\left(\iota_2\left(\left(i\mapsto t \, \left(x\left(i\right) + d\left(i\right)\right) \, c\left(i\right) - 1\right)\right)\right)\right\| \le \frac{1}{4}
\end{gathered}
$$

## Theorem: `logBarrier_full_newton_next_short_step_bound`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L364)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
1 \le n\\[4pt]\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho \le \frac{21}{64}\\[4pt]\sum_{i} \left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2} \le \rho^{2}\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)\\[4pt]\iota_2\left(\left(i\mapsto \left(x\left(i\right) + d\left(i\right)\right) \, q\left(i\right)\right)\right) \in U^{\perp}
\end{gathered}
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right) + d\left(i\right)\\
\land\quad \left\|P_{U}\left(\iota_2\left(\left(i\mapsto \left(1 + \frac{1}{16 \, \sqrt{n}}\right) \, t \, \left(x\left(i\right) + d\left(i\right)\right) \, c\left(i\right) - 1\right)\right)\right)\right\| \le \frac{21}{64}
\end{gathered}
$$

## Theorem: `logBarrier_full_newton_quarter_invariant`

[Source](../../QuasiNewtonConvergence/LogBarrierNewtonInvariant.lean#L397)

Let $n: \mathbb{N}$; $c, x, d, q: I_{n}\to \mathbb{R}$; $t, \rho: \mathbb{R}$; $\mathcal{F}: \left(I_{n}\to \mathbb{R}\right)\to \mathrm{Prop}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 < x\left(i\right)\\[4pt]0 \le \rho\\[4pt]\rho \le \frac{21}{64}\\[4pt]\sum_{i} \left(\frac{d\left(i\right)}{x\left(i\right)}\right)^{2} \le \rho^{2}\\[4pt]\forall i,\quad t \, c\left(i\right) - \frac{1}{x\left(i\right)} + \frac{d\left(i\right)}{x\left(i\right)^{2}} = q\left(i\right)\\[4pt]\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} q\left(i\right) \, \left(x\left(i\right) + d\left(i\right) - z\left(i\right)\right) = 0
\end{gathered}
$$

Set

$$
x_+:=\left(i\mapsto x\left(i\right) + d\left(i\right)\right)
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < x_+\left(i\right)\\
\land\quad \exists e\in I_{n}\to \mathbb{R},\quad \left(\forall i,\quad \left|e\left(i\right)\right| \le \frac{1}{4}\right) \land \left(\forall z,\quad z\in\mathcal{F} \Longrightarrow \sum_{i} \left(t \, c\left(i\right) - \frac{1 + e\left(i\right)}{x_+\left(i\right)}\right) \, \left(x_+\left(i\right) - z\left(i\right)\right) = 0\right)
\end{gathered}
$$


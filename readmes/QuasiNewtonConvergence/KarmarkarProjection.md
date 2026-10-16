# KarmarkarProjection

Projected directions and step bounds.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/KarmarkarProjection.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [KarmarkarProjective](KarmarkarProjective.md).

## Theorem: `karmarkar_orthogonal_projection_identities`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L22)

Let $U: \operatorname{Subspaces}_{\mathbb{R}}(E)$; $\ell: \mathcal{L}_{\mathbb{R}}(E,\mathbb{R})$; $v, w: E$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
\forall x,\quad \ell\left(x\right) = \left\langle v,x\right\rangle\\[4pt]w \in U
\end{gathered}
$$

Set

$$
p:=P_{U}\left(v\right)
$$

Then

$$
\begin{gathered}
\ell\left(w\right) = \left\langle p,w\right\rangle\\
\land\quad \ell\left(p\right) = \left\langle p,p\right\rangle
\end{gathered}
$$

## Theorem: `karmarkar_orthogonal_projection_ne_zero`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L41)

Let $U: \operatorname{Subspaces}_{\mathbb{R}}(E)$; $\ell: \mathcal{L}_{\mathbb{R}}(E,\mathbb{R})$; $v, u, z: E$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
\forall x,\quad \ell\left(x\right) = \left\langle v,x\right\rangle\\[4pt]u - z \in U\\[4pt]\ell\left(z\right) = 0\\[4pt]0 < \ell\left(u\right)
\end{gathered}
$$

Then

$$
P_{U}\left(v\right) \ne 0
$$

## Theorem: `karmarkar_projected_cost_ratio`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L60)

Let $\ell: \mathcal{L}_{\mathbb{R}}(E,\mathbb{R})$; $u, z, p: E$; $\alpha, r, R: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \alpha\\[4pt]0 < r\\[4pt]0 < R\\[4pt]\ell\left(z\right) = 0\\[4pt]0 < \ell\left(u\right)\\[4pt]\ell\left(u - z\right) = \left\langle p,u - z\right\rangle\\[4pt]\ell\left(p\right) = \left\langle p,p\right\rangle\\[4pt]\left\|u - z\right\| \le R
\end{gathered}
$$

Then

$$
\frac{\ell\left(u - \frac{\alpha \, r}{\left\|p\right\|} \, p\right)}{\ell\left(u\right)} \le 1 - \frac{\alpha \, r}{R}
$$

## Theorem: `karmarkar_projected_cost_ratio_quarter`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L105)

Let $\ell: \mathcal{L}_{\mathbb{R}}(E,\mathbb{R})$; $u, z, p: E$; $r, R: \mathbb{R}$; $n: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < r\\[4pt]0 < R\\[4pt]\ell\left(z\right) = 0\\[4pt]0 < \ell\left(u\right)\\[4pt]\ell\left(u - z\right) = \left\langle p,u - z\right\rangle\\[4pt]\ell\left(p\right) = \left\langle p,p\right\rangle\\[4pt]\left\|u - z\right\| \le R\\[4pt]2 \le n\\[4pt]\frac{r}{R} = \frac{1}{n - 1}
\end{gathered}
$$

Then

$$
\frac{\ell\left(u - \frac{\frac{1}{4} \, r}{\left\|p\right\|} \, p\right)}{\ell\left(u\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}
$$

## Theorem: `karmarkar_orthogonal_projection_quarter_ratio`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L130)

Let $U: \operatorname{Subspaces}_{\mathbb{R}}(E)$; $\ell: \mathcal{L}_{\mathbb{R}}(E,\mathbb{R})$; $v, u, z: E$; $r, R: \mathbb{R}$; $n: \mathbb{N}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
\forall x,\quad \ell\left(x\right) = \left\langle v,x\right\rangle\\[4pt]u - z \in U\\[4pt]0 < r\\[4pt]0 < R\\[4pt]\ell\left(z\right) = 0\\[4pt]0 < \ell\left(u\right)\\[4pt]\left\|u - z\right\| \le R\\[4pt]2 \le n\\[4pt]\frac{r}{R} = \frac{1}{n - 1}
\end{gathered}
$$

Set

$$
p:=P_{U}\left(v\right)
$$

Then

$$
\frac{\ell\left(u - \frac{\frac{1}{4} \, r}{\left\|p\right\|} \, p\right)}{\ell\left(u\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}
$$

## Theorem: `karmarkar_coordinate_lower_of_radius`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L153)

Let $n: \mathbb{N}$; $t: I_{n}\to \mathbb{R}$; $i: I_{n}$.

Assume all of the following.

$$
\begin{gathered}
2 \le n\\[4pt]\sum_{i} t\left(i\right) = 0\\[4pt]\sum_{i} t\left(i\right)^{2} \le \frac{n}{16 \, \left(n - 1\right)}
\end{gathered}
$$

Then

$$
-\left(\frac{1}{4}\right) \le t\left(i\right)
$$

## Theorem: `karmarkar_quarter_step_coordinates`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L196)

Let $n: \mathbb{N}$; $p: I_{n}\to \mathbb{R}$; $r: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
2 \le n\\[4pt]\sum_{i} p\left(i\right) = 0\\[4pt]\sum_{i} p\left(i\right)^{2} = 1\\[4pt]r^{2} = \frac{1}{n \, \left(n - 1\right)}
\end{gathered}
$$

Set

$$
y:=\left(i\mapsto \operatorname{center}\left(n,\,i\right) - \frac{1}{4} \, r \, p\left(i\right)\right)
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < y\left(i\right)\\
\land\quad \sum_{i} y\left(i\right) = 1\\
\land\quad \forall i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(i\right) - 1\\
\land\quad \sum_{i} \left(n \, y\left(i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

## Theorem: `karmarkar_euclidean_quarter_step_coordinates`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L258)

Let $n: \mathbb{N}$; $p: \mathbb{R}^{n}$; $r: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
2 \le n\\[4pt]p \ne 0\\[4pt]\sum_{i} p\left(i\right) = 0\\[4pt]r^{2} = \frac{1}{n \, \left(n - 1\right)}
\end{gathered}
$$

Set

$$
y:=\left(i\mapsto \operatorname{center}\left(n,\,i\right) - \frac{1}{4} \, r \, \left(\frac{p\left(i\right)}{\left\|p\right\|}\right)\right)
$$

Then

$$
\begin{gathered}
\forall i,\quad 0 < y\left(i\right)\\
\land\quad \sum_{i} y\left(i\right) = 1\\
\land\quad \forall i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(i\right) - 1\\
\land\quad \sum_{i} \left(n \, y\left(i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

## Definition: `karmarkarCoordinateSum`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L280)

Let $n: \mathbb{N}$.

Define

$$
\operatorname{coordSum}(n)(x)=\sum_{i=0}^{n-1}x(i).
$$

## Definition: `karmarkarFeasibleTangent`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L288)

Let $n: \mathbb{N}$; $F$ a set; $A: \mathcal{L}_{\mathbb{R}}(\mathbb{R}^{n},F)$.

Assume all of the following.

$F$ is a vector space over $\mathbb{R}$.

Define

$$
\operatorname{tangent}\left(A\right) := \ker\left(A\right) \cap \ker\left(\operatorname{coordSum}\left(n\right)\right)
$$

## Theorem: `karmarkar_projected_direction_feasible`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L294)

Let $n: \mathbb{N}$; $F$ a set; $A: \mathcal{L}_{\mathbb{R}}(\mathbb{R}^{n},F)$; $v: \mathbb{R}^{n}$.

Assume all of the following.

$F$ is a vector space over $\mathbb{R}$.

Set

$$
p:=P_{\operatorname{tangent}\left(A\right)}\left(v\right)
$$

Then

$$
\begin{gathered}
A\left(p\right) = 0\\
\land\quad \sum_{i} p\left(i\right) = 0
\end{gathered}
$$

## Theorem: `karmarkar_orthogonal_projective_step_bounds`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L307)

Let $n: \mathbb{N}$; $U: \operatorname{Subspaces}_{\mathbb{R}}(\mathbb{R}^{n})$; $\ell: \mathcal{L}_{\mathbb{R}}(\mathbb{R}^{n},\mathbb{R})$; $v, u, z: \mathbb{R}^{n}$; $r, R: \mathbb{R}$.

Assume all of the following.

$U$ admits an orthogonal projection.

$$
\begin{gathered}
2 \le n\\[4pt]\forall x,\quad \ell\left(x\right) = \left\langle v,x\right\rangle\\[4pt]u - z \in U\\[4pt]\ell\left(z\right) = 0\\[4pt]0 < \ell\left(u\right)\\[4pt]0 < r\\[4pt]0 < R\\[4pt]\left\|u - z\right\| \le R\\[4pt]\frac{r}{R} = \frac{1}{n - 1}\\[4pt]r^{2} = \frac{1}{n \, \left(n - 1\right)}\\[4pt]\sum_{i} P_{U}\left(v,\,i\right) = 0
\end{gathered}
$$

Set

$$
p:=P_{U}\left(v\right)
$$

Set

$$
y:=\left(i\mapsto \operatorname{center}\left(n,\,i\right) - \frac{1}{4} \, r \, \left(\frac{p\left(i\right)}{\left\|p\right\|}\right)\right)
$$

Then

$$
\begin{gathered}
\frac{\ell\left(u - \frac{\frac{1}{4} \, r}{\left\|p\right\|} \, p\right)}{\ell\left(u\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}\\
\land\quad \forall i,\quad 0 < y\left(i\right)\\
\land\quad \sum_{i} y\left(i\right) = 1\\
\land\quad \forall i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(i\right) - 1\\
\land\quad \sum_{i} \left(n \, y\left(i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$

## Theorem: `karmarkar_kernel_projective_step_bounds`

[Source](../../QuasiNewtonConvergence/KarmarkarProjection.lean#L343)

Let $n: \mathbb{N}$; $F$ a set; $A: \mathcal{L}_{\mathbb{R}}(\mathbb{R}^{n},F)$; $\ell: \mathcal{L}_{\mathbb{R}}(\mathbb{R}^{n},\mathbb{R})$; $v, u, z: \mathbb{R}^{n}$; $r, R: \mathbb{R}$.

Assume all of the following.

$F$ is a vector space over $\mathbb{R}$.

$$
\begin{gathered}
2 \le n\\[4pt]\forall x,\quad \ell\left(x\right) = \left\langle v,x\right\rangle\\[4pt]A\left(u\right) = A\left(z\right)\\[4pt]\sum_{i} u\left(i\right) = \left(\sum_{i} z\left(i\right)\right)\\[4pt]\ell\left(z\right) = 0\\[4pt]0 < \ell\left(u\right)\\[4pt]0 < r\\[4pt]0 < R\\[4pt]\left\|u - z\right\| \le R\\[4pt]\frac{r}{R} = \frac{1}{n - 1}\\[4pt]r^{2} = \frac{1}{n \, \left(n - 1\right)}
\end{gathered}
$$

Set

$$
p:=P_{\operatorname{tangent}\left(A\right)}\left(v\right)
$$

Set

$$
y:=\left(i\mapsto \operatorname{center}\left(n,\,i\right) - \frac{1}{4} \, r \, \left(\frac{p\left(i\right)}{\left\|p\right\|}\right)\right)
$$

Then

$$
\begin{gathered}
\frac{\ell\left(u - \frac{\frac{1}{4} \, r}{\left\|p\right\|} \, p\right)}{\ell\left(u\right)} \le 1 - \frac{1}{4 \, \left(n - 1\right)}\\
\land\quad \forall i,\quad 0 < y\left(i\right)\\
\land\quad \sum_{i} y\left(i\right) = 1\\
\land\quad \forall i,\quad -\left(\frac{1}{4}\right) \le n \, y\left(i\right) - 1\\
\land\quad \sum_{i} \left(n \, y\left(i\right) - 1\right)^{2} \le \frac{1}{8}
\end{gathered}
$$


# BFGSMatrix

BFGS matrix identities.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BFGSMatrix.lean)

Let $E$ be a real inner product space with its induced norm. Here $E$ is finite dimensional.

Definitions from other modules: [BroydenUpdates](BroydenUpdates.md).

## Definition: `innerLinear` (private helper)

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L23)

Let $a: E$.

Define

$$
\operatorname{innerLinear}(a)(z)=\langle a,z\rangle\quad(z\in E).
$$

## Theorem: `trace_rankOne` (private helper)

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L28)

Let $a, b: E$.

Then

$$
\operatorname{tr}\left(\operatorname{rankOne}\left(a,\,b\right)\right) = \left\langle a,b\right\rangle
$$

## Theorem: `bfgs_trace_update`

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L37)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Then

$$
\operatorname{tr}\left(\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right)\right) = \operatorname{tr}\left(B\right) - \frac{\left\|B\left(s\right)\right\|^{2}}{\left\langle B\left(s\right),s\right\rangle} + \frac{\left\|y\right\|^{2}}{\left\langle y,s\right\rangle}
$$

## Theorem: `bfgs_det_rank_two_aux`

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L48)

Let $\iota$ a set; $A: \mathbb{R}^{\iota\times \iota}$; $U: \mathbb{R}^{\iota\times I_{2}}$; $V: \mathbb{R}^{I_{2}\times \iota}$; $\beta, \eta: \mathbb{R}$.

Assume all of the following.

$\iota$ is a finite index set.

$$
\begin{gathered}
\det\left(A\right)\ne0\\[4pt]\left(1 + V \, A^{-1} \, U\right)\left(0,\,0\right) = 0\\[4pt]\left(1 + V \, A^{-1} \, U\right)\left(0,\,1\right) = \frac{\eta}{\beta}\\[4pt]\left(1 + V \, A^{-1} \, U\right)\left(1,\,0\right) = -1
\end{gathered}
$$

Then

$$
\det\left(A + U \, V\right) = \det\left(A\right) \, \left(\frac{\eta}{\beta}\right)
$$

## Theorem: `positive_eigenvalues` (private helper)

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L59)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $i: I_{\dim_{\mathbb{R}} E}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
0 < \lambda_{i}(B)
$$

## Theorem: `positiveDefinite_det_pos`

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L70)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
0 < \det\left(B\right)
$$

## Theorem: `positiveDefinite_trace_sub_log_det`

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L78)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\dim_{\mathbb{R}} E \le \operatorname{tr}\left(B\right) - \log\left(\det\left(B\right)\right)
$$

## Theorem: `det_one_add_comp` (private helper)

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L92)

Let $U: \mathcal{L}_{\mathbb{R}}(I_{2}\to \mathbb{R},E)$; $V: \mathcal{L}_{\mathbb{R}}(E,I_{2}\to \mathbb{R})$.

Then

$$
\det\left(1 + U\circ V\right) = \det\left(1 + V\circ U\right)
$$

## Theorem: `bfgs_det_update`

[Source](../../QuasiNewtonConvergence/BFGSMatrix.lean#L104)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle
\end{gathered}
$$

Then

$$
\det\left(\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right)\right) = \det\left(B\right) \, \left(\frac{\left\langle y,s\right\rangle}{\left\langle B\left(s\right),s\right\rangle}\right)
$$


# BFGSDirectional

Directional BFGS convergence.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BFGSDirectional.lean)

Let $E$ be a real inner product space with its induced norm. Here $E$ is finite dimensional.

Definitions from other modules: [BFGSMatrix](BFGSMatrix.md), [BFGSDennisMore](BFGSDennisMore.md).

## Theorem: `bfgs_trace_normalized` (private helper)

[Source](../../QuasiNewtonConvergence/BFGSDirectional.lean#L20)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
0 < \left\langle B\left(s\right),s\right\rangle\\[4pt]0 < \left\langle y,s\right\rangle
\end{gathered}
$$

Then

$$
\operatorname{tr}\left(\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right)\right) = \operatorname{tr}\left(B\right) - \frac{\frac{\left\langle B\left(s\right),s\right\rangle}{\left\|s\right\|^{2}}}{\left(\frac{\left\langle B\left(s\right),s\right\rangle}{\left\|B\left(s\right)\right\| \, \left\|s\right\|}\right)^{2}} + \frac{\left\|y\right\|^{2}}{\left\langle y,s\right\rangle}
$$

## Theorem: `bfgs_update_directional_dennis_more`

[Source](../../QuasiNewtonConvergence/BFGSDirectional.lean#L42)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: \mathbb{N}\to E$; $D, e_{\rm sec}: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad B\left(k + 1\right) = \operatorname{bfgsUpdateMap}\left(B\left(k\right),\,s\left(k\right),\,y\left(k\right)\right)\\[4pt]\forall k,\quad 0 < \left\langle B\left(k,\,s\left(k\right)\right),s\left(k\right)\right\rangle\\[4pt]\forall k,\quad 0 < \left\langle y\left(k\right),s\left(k\right)\right\rangle\\[4pt]\forall k,\quad 0 < D\left(k\right)\\[4pt]\forall k,\quad 0 \le \operatorname{tr}\left(B\left(k\right)\right) - \log\left(D\left(k\right)\right)\\[4pt]\forall k,\quad 0 \le e_{\rm sec}\left(k\right)\\[4pt]\sum_{k=0}^{\infty}\left|e_{\rm sec}\left(k\right)\right|<\infty\\[4pt]\forall k,\quad D\left(k + 1\right) = \frac{D\left(k\right) \, \left(\frac{\left\langle y\left(k\right),s\left(k\right)\right\rangle}{\left\|s\left(k\right)\right\|^{2}}\right)}{\frac{\left\langle B\left(k,\,s\left(k\right)\right),s\left(k\right)\right\rangle}{\left\|s\left(k\right)\right\|^{2}}}\\[4pt]\forall k,\quad \frac{\left\|y\left(k\right)\right\|^{2}}{\left\langle y\left(k\right),s\left(k\right)\right\rangle} - \log\left(\frac{\left\langle y\left(k\right),s\left(k\right)\right\rangle}{\left\|s\left(k\right)\right\|^{2}}\right) - 1 \le e_{\rm sec}\left(k\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|B\left(k,\,s\left(k\right)\right) - s\left(k\right)\right\|}{\left\|s\left(k\right)\right\|} = 0
$$

## Theorem: `bfgs_sequence_directional_dennis_more`

[Source](../../QuasiNewtonConvergence/BFGSDirectional.lean#L101)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: \mathbb{N}\to E$; $e_{\rm sec}: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\left(0\right)\right) \land \operatorname{SymmetricHessian}\left(B\left(0\right)\right)\\[4pt]\forall k,\quad B\left(k + 1\right) = \operatorname{bfgsUpdateMap}\left(B\left(k\right),\,s\left(k\right),\,y\left(k\right)\right)\\[4pt]\forall k,\quad 0 < \left\langle y\left(k\right),s\left(k\right)\right\rangle\\[4pt]\forall k,\quad 0 \le e_{\rm sec}\left(k\right)\\[4pt]\sum_{k=0}^{\infty}\left|e_{\rm sec}\left(k\right)\right|<\infty\\[4pt]\forall k,\quad \frac{\left\|y\left(k\right)\right\|^{2}}{\left\langle y\left(k\right),s\left(k\right)\right\rangle} - \log\left(\frac{\left\langle y\left(k\right),s\left(k\right)\right\rangle}{\left\|s\left(k\right)\right\|^{2}}\right) - 1 \le e_{\rm sec}\left(k\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|B\left(k,\,s\left(k\right)\right) - s\left(k\right)\right\|}{\left\|s\left(k\right)\right\|} = 0
$$


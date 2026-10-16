# BFGSDennisMore

Scalar Dennis–Moré analysis.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BFGSDennisMore.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [DennisMoreProximal](DennisMoreProximal.md), [BFGSGlobal](BFGSGlobal.md).

## Theorem: `bfgs_scalar_potential_identity`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L24)

Let $T, T_+, D, D_+, a, q, \chi, M: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < D\\[4pt]0 < a\\[4pt]0 < q\\[4pt]0 < \chi\\[4pt]T_+ = T - \frac{q}{\chi^{2}} + M\\[4pt]D_+ = \frac{D \, a}{q}
\end{gathered}
$$

Then

$$
T_+ - \log\left(D_+\right) + -\log\left(\chi^{2}\right) + \left(\frac{q}{\chi^{2}} - 1 - \log\left(\frac{q}{\chi^{2}}\right)\right) = T - \log\left(D\right) + \left(M - \log\left(a\right) - 1\right)
$$

## Theorem: `bfgs_scalar_potential_dissipation`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L47)

Let $T, T_+, D, D_+, a, q, \chi, M, e: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < D\\[4pt]0 < a\\[4pt]0 < q\\[4pt]0 < \chi\\[4pt]\chi \le 1\\[4pt]T_+ = T - \frac{q}{\chi^{2}} + M\\[4pt]D_+ = \frac{D \, a}{q}\\[4pt]M - \log\left(a\right) - 1 \le e
\end{gathered}
$$

Then

$$
\begin{gathered}
0 \le -\log\left(\chi^{2}\right)\\
\land\quad 0 \le \frac{q}{\chi^{2}} - 1 - \log\left(\frac{q}{\chi^{2}}\right)\\
\land\quad T_+ - \log\left(D_+\right) + -\log\left(\chi^{2}\right) + \left(\frac{q}{\chi^{2}} - 1 - \log\left(\frac{q}{\chi^{2}}\right)\right) \le T - \log\left(D\right) + e
\end{gathered}
$$

## Theorem: `bfgs_potential_dissipation_summable`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L73)

Let $\Psi, e, d: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 \le \Psi\left(k\right)\\[4pt]\forall k,\quad 0 \le e\left(k\right)\\[4pt]\forall k,\quad 0 \le d\left(k\right)\\[4pt]\sum_{k=0}^{\infty}\left|e\left(k\right)\right|<\infty\\[4pt]\forall k,\quad \Psi\left(k + 1\right) + d\left(k\right) \le \Psi\left(k\right) + e\left(k\right)
\end{gathered}
$$

Then

$$
\sum_{k=0}^{\infty}\left|d\left(k\right)\right|<\infty
$$

## Theorem: `bfgs_potential_defects_tendsto_zero`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L97)

Let $\Psi, e, a, r: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 \le \Psi\left(k\right)\\[4pt]\forall k,\quad 0 \le e\left(k\right)\\[4pt]\forall k,\quad 0 \le a\left(k\right)\\[4pt]\forall k,\quad 0 \le r\left(k\right)\\[4pt]\sum_{k=0}^{\infty}\left|e\left(k\right)\right|<\infty\\[4pt]\forall k,\quad \Psi\left(k + 1\right) + a\left(k\right) + r\left(k\right) \le \Psi\left(k\right) + e\left(k\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\lim_{k\to\infty} a\left(k\right) = 0\\
\land\quad \lim_{k\to\infty} r\left(k\right) = 0
\end{gathered}
$$

## Theorem: `bfgs_scalar_trace_det_defects_tendsto_zero`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L124)

Let $T, D, m, M, q, \chi, e: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 < D\left(k\right)\\[4pt]\forall k,\quad 0 < m\left(k\right)\\[4pt]\forall k,\quad 0 < q\left(k\right)\\[4pt]\forall k,\quad 0 < \chi\left(k\right)\\[4pt]\forall k,\quad \chi\left(k\right) \le 1\\[4pt]\forall k,\quad 0 \le T\left(k\right) - \log\left(D\left(k\right)\right)\\[4pt]\forall k,\quad 0 \le e\left(k\right)\\[4pt]\sum_{k=0}^{\infty}\left|e\left(k\right)\right|<\infty\\[4pt]\forall k,\quad T\left(k + 1\right) = T\left(k\right) - \frac{q\left(k\right)}{\chi\left(k\right)^{2}} + M\left(k\right)\\[4pt]\forall k,\quad D\left(k + 1\right) = \frac{D\left(k\right) \, m\left(k\right)}{q\left(k\right)}\\[4pt]\forall k,\quad M\left(k\right) - \log\left(m\left(k\right)\right) - 1 \le e\left(k\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\lim_{k\to\infty} -\log\left(\chi\left(k\right)^{2}\right) = 0\\
\land\quad \lim_{k\to\infty} \frac{q\left(k\right)}{\chi\left(k\right)^{2}} - 1 - \log\left(\frac{q\left(k\right)}{\chi\left(k\right)^{2}}\right) = 0
\end{gathered}
$$

## Theorem: `bfgs_geometric_error_tendsto_zero`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L163)

Let $q, a, e: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\lim_{k\to\infty} q\left(k\right) = 1\\[4pt]\lim_{k\to\infty} a\left(k\right) = 1\\[4pt]\forall k,\quad 0 \le e\left(k\right)\\[4pt]\forall k,\quad e\left(k\right)^{2} = \frac{q\left(k\right)^{2}}{a\left(k\right)} - 2 \, q\left(k\right) + 1
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} e\left(k\right) = 0
$$

## Theorem: `bfgs_radial_defect_tendsto_one`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L195)

Let $t: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 < t\left(k\right)\\[4pt]\lim_{k\to\infty} t\left(k\right) - 1 - \log\left(t\left(k\right)\right) = 0
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} t\left(k\right) = 1
$$

## Theorem: `bfgs_defects_imply_directional_error`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L227)

Let $q, a, e: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 < q\left(k\right)\\[4pt]\forall k,\quad 0 < a\left(k\right)\\[4pt]\lim_{k\to\infty} -\log\left(a\left(k\right)\right) = 0\\[4pt]\lim_{k\to\infty} \frac{q\left(k\right)}{a\left(k\right)} - 1 - \log\left(\frac{q\left(k\right)}{a\left(k\right)}\right) = 0\\[4pt]\forall k,\quad 0 \le e\left(k\right)\\[4pt]\forall k,\quad e\left(k\right)^{2} = \frac{q\left(k\right)^{2}}{a\left(k\right)} - 2 \, q\left(k\right) + 1
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} e\left(k\right) = 0
$$

## Theorem: `bfgs_scalar_trace_det_dennis_more`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L261)

Let $T, D, m, M, q, \chi, e_{\rm sec}, e_{\rm dir}: \mathbb{N}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad 0 < D\left(k\right)\\[4pt]\forall k,\quad 0 < m\left(k\right)\\[4pt]\forall k,\quad 0 < q\left(k\right)\\[4pt]\forall k,\quad 0 < \chi\left(k\right)\\[4pt]\forall k,\quad \chi\left(k\right) \le 1\\[4pt]\forall k,\quad 0 \le T\left(k\right) - \log\left(D\left(k\right)\right)\\[4pt]\forall k,\quad 0 \le e_{\rm sec}\left(k\right)\\[4pt]\sum_{k=0}^{\infty}\left|e_{\rm sec}\left(k\right)\right|<\infty\\[4pt]\forall k,\quad T\left(k + 1\right) = T\left(k\right) - \frac{q\left(k\right)}{\chi\left(k\right)^{2}} + M\left(k\right)\\[4pt]\forall k,\quad D\left(k + 1\right) = \frac{D\left(k\right) \, m\left(k\right)}{q\left(k\right)}\\[4pt]\forall k,\quad M\left(k\right) - \log\left(m\left(k\right)\right) - 1 \le e_{\rm sec}\left(k\right)\\[4pt]\forall k,\quad 0 \le e_{\rm dir}\left(k\right)\\[4pt]\forall k,\quad e_{\rm dir}\left(k\right)^{2} = \frac{q\left(k\right)^{2}}{\chi\left(k\right)^{2}} - 2 \, q\left(k\right) + 1
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} e_{\rm dir}\left(k\right) = 0
$$

## Theorem: `bfgs_geometric_identity`

[Source](../../QuasiNewtonConvergence/BFGSDennisMore.lean#L292)

Let $E$ a set; $u, s: E$.

Assume all of the following.

$$
\begin{gathered}
0 < \left\langle u,s\right\rangle
\end{gathered}
$$

Then

$$
\left(\frac{\left\|u - s\right\|}{\left\|s\right\|}\right)^{2} = \frac{\left(\frac{\left\langle u,s\right\rangle}{\left\|s\right\|^{2}}\right)^{2}}{\frac{\left\langle u,s\right\rangle^{2}}{\left\|u\right\|^{2} \, \left\|s\right\|^{2}}} - 2 \, \left(\frac{\left\langle u,s\right\rangle}{\left\|s\right\|^{2}}\right) + 1
$$


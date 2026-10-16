# BFGSGlobal

BFGS global potential bounds.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BFGSGlobal.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains.

## Theorem: `bfgs_scalar_potential_step`

[Source](../../QuasiNewtonConvergence/BFGSGlobal.lean#L18)

Let $T, T_+, D, D_+, a, b, q, \chi, m, M, C: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < D\\[4pt]0 < a\\[4pt]0 < q\\[4pt]0 < \chi\\[4pt]0 < m\\[4pt]m \le a\\[4pt]b \le M\\[4pt]M - \log\left(m\right) - 1 \le C\\[4pt]T_+ = T - \frac{q}{\chi^{2}} + b\\[4pt]D_+ = \frac{D \, a}{q}
\end{gathered}
$$

Then

$$
T_+ - \log\left(D_+\right) \le T - \log\left(D\right) + C + \log\left(\chi^{2}\right)
$$

## Theorem: `bfgs_angle_not_tendsto_zero`

[Source](../../QuasiNewtonConvergence/BFGSGlobal.lean#L45)

Let $\Psi, \chi: \mathbb{N}\to \mathbb{R}$; $C: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < C\\[4pt]\forall k,\quad 0 \le \Psi\left(k\right)\\[4pt]\forall k,\quad 0 < \chi\left(k\right)\\[4pt]\forall k,\quad \Psi\left(k + 1\right) \le \Psi\left(k\right) + C + \log\left(\chi\left(k\right)^{2}\right)
\end{gathered}
$$

Then

$$
\neg\left(\lim_{k\to\infty} \chi\left(k\right) = 0\right)
$$


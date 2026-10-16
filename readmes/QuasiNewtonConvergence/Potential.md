# Potential

Scalar potential bounds.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/Potential.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains.

## Theorem: `potential_weighted_bound`

[Source](../../QuasiNewtonConvergence/Potential.lean#L10)

Let $e, \Psi: \mathbb{N}\to \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad e\left(k + 1\right) \le e\left(k\right)\\[4pt]\forall k,\quad e\left(k + 1\right) \le \Psi\left(k\right) - \Psi\left(k + 1\right)
\end{gathered}
$$

Then

$$
k \, e\left(k\right) + \Psi\left(k\right) \le \Psi\left(0\right)
$$

## Theorem: `potential_last_iterate_bound`

[Source](../../QuasiNewtonConvergence/Potential.lean#L25)

Let $e, \Psi: \mathbb{N}\to \mathbb{R}$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
\forall k,\quad e\left(k + 1\right) \le e\left(k\right)\\[4pt]\forall k,\quad e\left(k + 1\right) \le \Psi\left(k\right) - \Psi\left(k + 1\right)\\[4pt]\forall k,\quad 0 \le \Psi\left(k\right)
\end{gathered}
$$

Then

$$
\left(k + 1\right) \, e\left(k + 1\right) \le \Psi\left(0\right)
$$


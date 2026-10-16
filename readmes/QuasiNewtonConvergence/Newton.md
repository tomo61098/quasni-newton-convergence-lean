# Newton

Newton convergence.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/Newton.lean)

Let $E$ be a real normed vector space.

## Definition: `newtonStep`

[Source](../../QuasiNewtonConvergence/Newton.lean#L21)

Let $G: E\to E$; $J: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $x: E$.

Define

$$
\operatorname{newtonStep}\left(G,\,J,\,x\right) := x - J\left(x,\,G\left(x\right)\right)
$$

## Theorem: `newton_gradient_remainder`

[Source](../../QuasiNewtonConvergence/Newton.lean#L26)

Let $G: E\to E$; $\mathcal{H}: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $L: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|
\end{gathered}
$$

Then

$$
\left\|\mathcal{H}\left(x,\,x - x_\star\right) - \left(G\left(x\right) - G\left(x_\star\right)\right)\right\| \le L \, \left\|x - x_\star\right\|^{2}
$$

## Theorem: `newtonStep_quadratic_bound`

[Source](../../QuasiNewtonConvergence/Newton.lean#L58)

Let $G: E\to E$; $\mathcal{H}, J: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $L, B: \mathbb{R}$; $x, x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]0 \le B\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|\\[4pt]G\left(x_\star\right) = 0\\[4pt]\forall y,v,\quad J\left(y,\,\mathcal{H}\left(y,\,v\right)\right) = v\\[4pt]\left\|J\left(x\right)\right\| \le B
\end{gathered}
$$

Then

$$
\left\|\operatorname{newtonStep}\left(G,\,J,\,x\right) - x_\star\right\| \le B \, L \, \left\|x - x_\star\right\|^{2}
$$

## Theorem: `newton_local_quadratic_convergence`

[Source](../../QuasiNewtonConvergence/Newton.lean#L85)

Let $G: E\to E$; $\mathcal{H}, J: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $L, B, r: \mathbb{R}$; $x: \mathbb{N}\to E$; $x_\star: E$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]0 \le B\\[4pt]0 \le r\\[4pt]B \, L \, r < 1\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|\\[4pt]G\left(x_\star\right) = 0\\[4pt]\forall y,v,\quad J\left(y,\,\mathcal{H}\left(y,\,v\right)\right) = v\\[4pt]\forall y,\quad \left\|y - x_\star\right\| \le r \Longrightarrow \left\|J\left(y\right)\right\| \le B\\[4pt]\left\|x\left(0\right) - x_\star\right\| \le r\\[4pt]\forall k,\quad x\left(k + 1\right) = \operatorname{newtonStep}\left(G,\,J,\,x\left(k\right)\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\forall k,\quad \left\|x\left(k + 1\right) - x_\star\right\| \le B \, L \, \left\|x\left(k\right) - x_\star\right\|^{2}\\
\land\quad \forall k,\quad \left\|x\left(k\right) - x_\star\right\| \le \left(B \, L \, r\right)^{k} \, \left\|x\left(0\right) - x_\star\right\|\\
\land\quad \lim_{k\to\infty} x\left(k\right) = x_\star
\end{gathered}
$$


# BroydenConvergence

Conditional quasi-Newton convergence.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BroydenConvergence.lean)

Let $E$ be a real inner product space with its induced norm.

Definitions from other modules: [BroydenUpdates](BroydenUpdates.md), [LineSearch](LineSearch.md), [StrongConvexMinimizer](StrongConvexMinimizer.md), [Newton](Newton.md).

## Definition: `quasiNewtonDirection`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L21)

Let $H: \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $g: E$.

Define

$$
\operatorname{quasiNewtonDirection}\left(H,\,g\right) := -H\left(g\right)
$$

## Structure: `QuasiNewtonRun`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L25)

Let $G: E\to E$.

The record consists of the following fields and conditions.

**x**

$$
x: \mathbb{N}\to E
$$

**B**

$$
B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)
$$

**H**

$$
H: \mathbb{N}\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)
$$

**α**

$$
\alpha: \mathbb{N}\to \mathbb{R}
$$

**method**

$$
\operatorname{method}: \mathbb{N}\to \operatorname{HessianUpdateMethod}
$$

**step**

$$
\forall k,\quad x\left(k + 1\right) = x\left(k\right) + \alpha\left(k\right) \, \operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)
$$

**update**

$$
\forall k,\quad B\left(k + 1\right) = \operatorname{hessianUpdate}\left(\operatorname{method}\left(k\right),\,B\left(k\right),\,x\left(k + 1\right) - x\left(k\right),\,G\left(x\left(k + 1\right)\right) - G\left(x\left(k\right)\right)\right)
$$

**leftInverse**

$$
\forall k,v,\quad H\left(k,\,B\left(k,\,v\right)\right) = v
$$

**rightInverse**

$$
\forall k,v,\quad B\left(k,\,H\left(k,\,v\right)\right) = v
$$


## Theorem: `quasiNewton_direction_weight_bound`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L39)

Let $H: \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $g: E$; $m, M: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < m\\[4pt]0 < M\\[4pt]g \ne 0\\[4pt]m \, \left\|g\right\|^{2} \le \left\langle g,H\left(g\right)\right\rangle\\[4pt]\left\|H\right\| \le M
\end{gathered}
$$

Then

$$
\left(\frac{m}{M}\right)^{2} \, \left\|g\right\|^{2} \le \frac{\left\langle g,\operatorname{quasiNewtonDirection}\left(H,\,g\right)\right\rangle^{2}}{\left\|\operatorname{quasiNewtonDirection}\left(H,\,g\right)\right\|^{2}}
$$

## Theorem: `quasiNewton_wolfe_gradient_tendsto`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L79)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $H: \mathbb{N}\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $\alpha: \mathbb{N}\to \mathbb{R}$; $\ell_{\rm low}, c_{1}, c_{2}, L, m, M: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]0 < m\\[4pt]0 < M\\[4pt]\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = x\left(k\right) + \alpha\left(k\right) \, \operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\\[4pt]\forall k,\quad G\left(x\left(k\right)\right) \ne 0\\[4pt]\forall k,\quad m \, \left\|G\left(x\left(k\right)\right)\right\|^{2} \le \left\langle G\left(x\left(k\right)\right),H\left(k,\,G\left(x\left(k\right)\right)\right)\right\rangle\\[4pt]\forall k,\quad \left\|H\left(k\right)\right\| \le M\\[4pt]\forall k,\quad \ell_{\rm low} \le f\left(x\left(k\right)\right)\\[4pt]\forall u,v,\quad \left\|G\left(v\right) - G\left(u\right)\right\| \le L \, \left\|v - u\right\|\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha\left(k\right),\,\left\langle G\left(x\left(k\right)\right),\operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\right\rangle,\,\left\langle G\left(x\left(k + 1\right)\right),\operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\right\rangle,\,f\left(x\left(k\right)\right),\,f\left(x\left(k + 1\right)\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \left\|G\left(x\left(k\right)\right)\right\| = 0
$$

## Theorem: `quasiNewton_wolfe_gradient_tendsto_all`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L128)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $H: \mathbb{N}\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $\alpha: \mathbb{N}\to \mathbb{R}$; $\ell_{\rm low}, c_{1}, c_{2}, L, m, M: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]0 < m\\[4pt]0 < M\\[4pt]\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = x\left(k\right) + \alpha\left(k\right) \, \operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\\[4pt]\forall k,\quad m \, \left\|G\left(x\left(k\right)\right)\right\|^{2} \le \left\langle G\left(x\left(k\right)\right),H\left(k,\,G\left(x\left(k\right)\right)\right)\right\rangle\\[4pt]\forall k,\quad \left\|H\left(k\right)\right\| \le M\\[4pt]\forall k,\quad \ell_{\rm low} \le f\left(x\left(k\right)\right)\\[4pt]\forall u,v,\quad \left\|G\left(v\right) - G\left(u\right)\right\| \le L \, \left\|v - u\right\|\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha\left(k\right),\,\left\langle G\left(x\left(k\right)\right),\operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\right\rangle,\,\left\langle G\left(x\left(k + 1\right)\right),\operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\right\rangle,\,f\left(x\left(k\right)\right),\,f\left(x\left(k + 1\right)\right)\right)
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \left\|G\left(x\left(k\right)\right)\right\| = 0
$$

## Theorem: `quasiNewton_wolfe_strong_converges`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L174)

Let $f: E\to \mathbb{R}$; $G: E\to E$; $x: \mathbb{N}\to E$; $H: \mathbb{N}\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $\alpha: \mathbb{N}\to \mathbb{R}$; $x_\star: E$; $\ell_{\rm low}, c_{1}, c_{2}, L, m, M, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]0 < m\\[4pt]0 < M\\[4pt]0 < \mu\\[4pt]\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = x\left(k\right) + \alpha\left(k\right) \, \operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\\[4pt]\forall k,\quad m \, \left\|G\left(x\left(k\right)\right)\right\|^{2} \le \left\langle G\left(x\left(k\right)\right),H\left(k,\,G\left(x\left(k\right)\right)\right)\right\rangle\\[4pt]\forall k,\quad \left\|H\left(k\right)\right\| \le M\\[4pt]\forall k,\quad \ell_{\rm low} \le f\left(x\left(k\right)\right)\\[4pt]\forall u,v,\quad \left\|G\left(v\right) - G\left(u\right)\right\| \le L \, \left\|v - u\right\|\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha\left(k\right),\,\left\langle G\left(x\left(k\right)\right),\operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\right\rangle,\,\left\langle G\left(x\left(k + 1\right)\right),\operatorname{quasiNewtonDirection}\left(H\left(k\right),\,G\left(x\left(k\right)\right)\right)\right\rangle,\,f\left(x\left(k\right)\right),\,f\left(x\left(k + 1\right)\right)\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\lim_{k\to\infty} x\left(k\right) = x_\star\\
\land\quad \lim_{k\to\infty} f\left(x\left(k\right)\right) = f\left(x_\star\right)
\end{gathered}
$$

## Theorem: `QuasiNewtonRun.strong_converges`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L219)

Let $\operatorname{run}: \operatorname{QuasiNewtonRun}\left(G\right)$; $f: E\to \mathbb{R}$; $x_\star: E$; $\ell_{\rm low}, c_{1}, c_{2}, L, m, M, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]0 < m\\[4pt]0 < M\\[4pt]0 < \mu\\[4pt]\forall k,\quad 0 \le \operatorname{run}_{\alpha}\left(k\right)\\[4pt]\forall k,\quad m \, \left\|G\left(\operatorname{run}_{x}\left(k\right)\right)\right\|^{2} \le \left\langle G\left(\operatorname{run}_{x}\left(k\right)\right),\operatorname{run}_{H}\left(k,\,G\left(\operatorname{run}_{x}\left(k\right)\right)\right)\right\rangle\\[4pt]\forall k,\quad \left\|\operatorname{run}_{H}\left(k\right)\right\| \le M\\[4pt]\forall k,\quad \ell_{\rm low} \le f\left(\operatorname{run}_{x}\left(k\right)\right)\\[4pt]\forall u,v,\quad \left\|G\left(v\right) - G\left(u\right)\right\| \le L \, \left\|v - u\right\|\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\operatorname{run}_{\alpha}\left(k\right),\,\left\langle G\left(\operatorname{run}_{x}\left(k\right)\right),\operatorname{quasiNewtonDirection}\left(\operatorname{run}_{H}\left(k\right),\,G\left(\operatorname{run}_{x}\left(k\right)\right)\right)\right\rangle,\,\left\langle G\left(\operatorname{run}_{x}\left(k + 1\right)\right),\operatorname{quasiNewtonDirection}\left(\operatorname{run}_{H}\left(k\right),\,G\left(\operatorname{run}_{x}\left(k\right)\right)\right)\right\rangle,\,f\left(\operatorname{run}_{x}\left(k\right)\right),\,f\left(\operatorname{run}_{x}\left(k + 1\right)\right)\right)\\[4pt]G\left(x_\star\right) = 0\\[4pt]\operatorname{SmoothUpper}\left(f,\,G,\,L\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(f,\,G,\,\mu\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\lim_{k\to\infty} \operatorname{run}_{x}\left(k\right) = x_\star\\
\land\quad \lim_{k\to\infty} f\left(\operatorname{run}_{x}\left(k\right)\right) = f\left(x_\star\right)
\end{gathered}
$$

## Theorem: `quasiNewton_full_step_superlinear`

[Source](../../QuasiNewtonConvergence/BroydenConvergence.lean#L250)

Let $G: E\to E$; $\mathcal{H}: E\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $H: \mathbb{N}\to \mathcal{L}^{\rm cont}_{\mathbb{R}}(E,E)$; $x: \mathbb{N}\to E$; $x_\star: E$; $\delta: \mathbb{N}\to \mathbb{R}$; $L, M: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 \le L\\[4pt]0 \le M\\[4pt]\forall k,\quad 0 \le \delta\left(k\right)\\[4pt]\forall y,\quad D G\left(y\right) = \mathcal{H}\left(y\right)\\[4pt]\forall y,z,\quad \left\|\mathcal{H}\left(y\right) - \mathcal{H}\left(z\right)\right\| \le L \, \left\|y - z\right\|\\[4pt]G\left(x_\star\right) = 0\\[4pt]\forall k,v,\quad H\left(k,\,B\left(k,\,v\right)\right) = v\\[4pt]\forall k,\quad \left\|H\left(k\right)\right\| \le M\\[4pt]\forall k,\quad \left\|B\left(k,\,x\left(k\right) - x_\star\right) - \mathcal{H}\left(x\left(k\right),\,x\left(k\right) - x_\star\right)\right\| \le \delta\left(k\right) \, \left\|x\left(k\right) - x_\star\right\|\\[4pt]\forall k,\quad x\left(k + 1\right) = x\left(k\right) - H\left(k,\,G\left(x\left(k\right)\right)\right)\\[4pt]\lim_{k\to\infty} x\left(k\right) = x_\star\\[4pt]\lim_{k\to\infty} \delta\left(k\right) = 0
\end{gathered}
$$

Then

$$
\lim_{k\to\infty} \frac{\left\|x\left(k + 1\right) - x_\star\right\|}{\left\|x\left(k\right) - x_\star\right\|} = 0
$$


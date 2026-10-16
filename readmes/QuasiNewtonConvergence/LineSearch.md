# LineSearch

LineSearch.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/LineSearch.lean)

Let $E$ be a real inner product space with its induced norm.

## Theorem: `directional_derivative_lipschitz`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L17)

Let $E$ a set; $g, g_+, p: E$; $L, \alpha: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\left\|g_+ - g\right\| \le L \, \alpha \, \left\|p\right\|
\end{gathered}
$$

Then

$$
\left\langle g_+,p\right\rangle - \left\langle g,p\right\rangle \le L \, \alpha \, \left\|p\right\|^{2}
$$

## Structure: `WolfeStep`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L33)

Let $c_{1}, c_{2}, \alpha, g, g_+, f, f_+: \mathbb{R}$.

Define

$$
\operatorname{WolfeStep}(c_1,c_2,\alpha,g,g_+,f,f_+)\Longleftrightarrow\bigl(f_+\le f+c_1\alpha g\bigr)\land\bigl(c_2g\le g_+\bigr).
$$

## Theorem: `wolfe_directional_curvature_positive`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L39)

Let $c_{2}, g, g_+: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
c_{2} < 1\\[4pt]g < 0\\[4pt]c_{2} \, g \le g_+
\end{gathered}
$$

Then

$$
0 < g_+ - g
$$

## Theorem: `wolfe_secant_curvature_positive`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L47)

Let $E$ a set; $g, g_+, p: E$; $\alpha, c_{2}: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \alpha\\[4pt]c_{2} < 1\\[4pt]\left\langle g,p\right\rangle < 0\\[4pt]c_{2} \, \left\langle g,p\right\rangle \le \left\langle g_+,p\right\rangle
\end{gathered}
$$

Then

$$
0 < \left\langle g_+ - g,\alpha \, p\right\rangle
$$

## Theorem: `wolfe_descent_bound`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L65)

Let $c_{1}, c_{2}, L, \alpha, g, g_+, d, f, f_+: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]g < 0\\[4pt]0 < d\\[4pt]\operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha,\,g,\,g_+,\,f,\,f_+\right)\\[4pt]g_+ - g \le L \, \alpha \, d
\end{gathered}
$$

Then

$$
c_{1} \, \left(1 - c_{2}\right) \, g^{2} \le L \, d \, \left(f - f_+\right)
$$

## Theorem: `summable_of_descent`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L87)

Let $\operatorname{energy}, \operatorname{weight}: \mathbb{N}\to \mathbb{R}$; $\ell_{\rm low}, \operatorname{rate}: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < \operatorname{rate}\\[4pt]\forall k,\quad 0 \le \operatorname{weight}\left(k\right)\\[4pt]\forall k,\quad \ell_{\rm low} \le \operatorname{energy}\left(k\right)\\[4pt]\forall k,\quad \operatorname{rate} \, \operatorname{weight}\left(k\right) \le \operatorname{energy}\left(k\right) - \operatorname{energy}\left(k + 1\right)
\end{gathered}
$$

Then

$$
\sum_{k=0}^{\infty}\left|\operatorname{weight}\left(k\right)\right|<\infty
$$

## Theorem: `zoutendijk_summable`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L119)

Let $\operatorname{energy}, g, g_+, d, \alpha: \mathbb{N}\to \mathbb{R}$; $\ell_{\rm low}, c_{1}, c_{2}, L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]\forall k,\quad g\left(k\right) < 0\\[4pt]\forall k,\quad 0 < d\left(k\right)\\[4pt]\forall k,\quad \ell_{\rm low} \le \operatorname{energy}\left(k\right)\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha\left(k\right),\,g\left(k\right),\,g_+\left(k\right),\,\operatorname{energy}\left(k\right),\,\operatorname{energy}\left(k + 1\right)\right)\\[4pt]\forall k,\quad g_+\left(k\right) - g\left(k\right) \le L \, \alpha\left(k\right) \, d\left(k\right)
\end{gathered}
$$

Then

$$
\sum_{k=0}^{\infty}\left|\frac{g\left(k\right)^{2}}{d\left(k\right)}\right|<\infty
$$

## Theorem: `zoutendijk_of_lipschitz_gradient`

[Source](../../QuasiNewtonConvergence/LineSearch.lean#L148)

Let $E$ a set; $f: E\to \mathbb{R}$; $G: E\to E$; $x, p: \mathbb{N}\to E$; $\alpha: \mathbb{N}\to \mathbb{R}$; $\ell_{\rm low}, c_{1}, c_{2}, L: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < c_{1}\\[4pt]c_{2} < 1\\[4pt]0 < L\\[4pt]\forall k,\quad 0 \le \alpha\left(k\right)\\[4pt]\forall k,\quad x\left(k + 1\right) = x\left(k\right) + \alpha\left(k\right) \, p\left(k\right)\\[4pt]\forall k,\quad \left\langle G\left(x\left(k\right)\right),p\left(k\right)\right\rangle < 0\\[4pt]\forall k,\quad \ell_{\rm low} \le f\left(x\left(k\right)\right)\\[4pt]\forall u,v,\quad \left\|G\left(v\right) - G\left(u\right)\right\| \le L \, \left\|v - u\right\|\\[4pt]\forall k,\quad \operatorname{WolfeStep}\left(c_{1},\,c_{2},\,\alpha\left(k\right),\,\left\langle G\left(x\left(k\right)\right),p\left(k\right)\right\rangle,\,\left\langle G\left(x\left(k + 1\right)\right),p\left(k\right)\right\rangle,\,f\left(x\left(k\right)\right),\,f\left(x\left(k + 1\right)\right)\right)
\end{gathered}
$$

Then

$$
\sum_{k=0}^{\infty}\left|\frac{\left\langle G\left(x\left(k\right)\right),p\left(k\right)\right\rangle^{2}}{\left\|p\left(k\right)\right\|^{2}}\right|<\infty
$$


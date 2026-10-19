# Traditional FISTA / Nesterov parameters

[Lean source](../../QuasiNewtonConvergence/NesterovTraditional.lean)

Let $F=f+g$ on a real inner product space. Assume $L>0$, the smooth upper
inequality and convex first-order inequality for $f$ and its supplied gradient,
segment convexity of $F$, and a global minimizer $u$ of $F$. Each proximal step
is assumed to satisfy `ProximalOptimality`, as in the existing proximal results.

The parameters and updates are

$$
t_0=0,\qquad
t_{k+1}=\frac{1+\sqrt{1+4t_k^2}}2,\qquad
\theta_k=\frac1{t_{k+1}},\qquad \alpha=\frac1L,
$$

$$
y_0=x_0,\qquad
x_{k+1}=\operatorname{prox}_{g/L}\left(y_k-\frac1L\nabla f(y_k)\right),
\qquad
y_{k+1}=x_{k+1}+\frac{t_{k+1}-1}{t_{k+2}}(x_{k+1}-x_k).
$$

Thus $t_1=1$ and $\theta_0=1$. The proximal notation above refers to the exact
variational optimality condition; these theorems do not construct a proximal
minimizer or assume its existence follows from segment convexity alone.

`fistaTime_sq_succ` proves $t_{k+1}^2=t_k^2+t_{k+1}$. Set

$$
A_k=\frac{t_k^2}{L},\qquad a_k=\frac{t_{k+1}}{L}.
$$

These choices give $A_0=0$, nonnegative $A_k$, positive $a_k$,
$0<\theta_k\le1$, and all three exact weight equations:

$$
A_{k+1}=A_k+a_k,\qquad
(A_k+a_k)\theta_k=a_k,\qquad
(A_k+a_k)L\theta_k^2=1.
$$

Define $z_0=x_0$ and $z_{k+1}=x_k+t_{k+1}(x_{k+1}-x_k)$. The usual
momentum update implies

$$
y_k=(1-\theta_k)x_k+\theta_k z_k,\qquad
x_{k+1}=(1-\theta_k)x_k+\theta_k z_{k+1}.
$$

`fista_quadratic_rate` now applies `proximalNesterov_quadratic_rate` directly:

$$
0\le F(x_n)-F(u)\le\frac{2L\|x_0-u\|^2}{n^2}\qquad(n\ge1).
$$

`fista_tendsto` squeezes this gap to zero, proving $F(x_n)\to F(u)$.
`fista_iterates_tendsto_of_quadratic_growth` additionally proves $x_n\to u$
if, for some $\mu>0$,

$$
\frac\mu2\|v-u\|^2\le F(v)-F(u)\qquad\text{for every }v.
$$

For $g=0$, `ConvexFirstOrder.segmentConvex` supplies the segment inequality
and a gradient step satisfies the proximal optimality condition.
`nesterov_fista_quadratic_rate` and `nesterov_fista_tendsto` therefore give
the same bound and objective convergence for the ordinary smooth method.
`nesterov_fista_strong_converges` uses the existing strongly convex minimizer
theorem on a complete space to supply $u$, derives quadratic growth from the
strong first-order inequality and stationarity, and proves both $x_n\to u$
and $f(x_n)\to f(u)$. No geometric rate is asserted for this varying-momentum
schedule.

The complete declaration list is below. The parameters, hypotheses, and
sequences in the preceding statements apply to the corresponding rate and
convergence declarations. All natural indices start at zero.

| Declaration | Mathematical statement |
| --- | --- |
| `fistaTime` | $t_0=0$, $t_{k+1}=(1+\sqrt{1+4t_k^2})/2$ |
| `fistaTime_zero` | $t_0=0$ |
| `fistaTime_one` | $t_1=1$ |
| `fistaTime_succ_ge_one` | $1\le t_{k+1}$ |
| `fistaTime_nonneg` | $0\le t_k$ |
| `fistaTime_sq_succ` | $t_{k+1}^2=t_k^2+t_{k+1}$ |
| `fistaTheta` | $\theta_k=1/t_{k+1}$ |
| `fistaTheta_pos` | $0<\theta_k$ |
| `fistaTheta_le_one` | $\theta_k\le1$ |
| `fistaMomentum` | $\beta_k=(t_{k+1}-1)/t_{k+2}$ |
| `fistaAuxiliary` (private) | $z_0=x_0$, $z_{k+1}=x_k+t_{k+1}(x_{k+1}-x_k)$ |
| `fista_coupling` (private) | For arbitrary $x,y$ satisfying the initial and momentum equations, both coupling identities displayed above hold for every $k$. |
| `fista_weights` (private) | For $L>0$, the displayed $A,a,\theta$ satisfy $A_0=0$, $A_k\ge0$, $a_k>0$, and the three exact weight equations. |
| `fista_quadratic_rate` | Under the composite assumptions and updates above, $F(x_n)-F(u)\le2L\|x_0-u\|^2/n^2$ for $n>0$. |
| `fista_tendsto` | Under the same assumptions, $F(x_n)\to F(u)$. |
| `fista_iterates_tendsto_of_quadratic_growth` | Replace the minimizer assumption by the displayed quadratic growth condition with $\mu>0$; then $x_n\to u$. |
| `ConvexFirstOrder.segmentConvex` | The convex first-order inequality for $f,G$ implies $f((1-\theta)x+\theta u)\le(1-\theta)f(x)+\theta f(u)$ for $0\le\theta\le1$. |
| `gradientStep_proximal_zero` (private) | For any gradient map, $L>0$, and $y$, the point $y-L^{-1}G(y)$ satisfies `ProximalOptimality` with $g=0$. |
| `nesterov_fista_quadratic_rate` | For smooth convex $f$, a supplied minimizer $u$, the same momentum rule, and $x_{k+1}=y_k-L^{-1}G(y_k)$, $f(x_n)-f(u)\le2L\|x_0-u\|^2/n^2$ for $n>0$. |
| `nesterov_fista_tendsto` | Under the preceding smooth assumptions, $f(x_n)\to f(u)$. |
| `nesterov_fista_strong_converges` | On a complete space, $L,\mu>0$, smoothness and strong first-order convexity of $f$, and the same gradient and momentum updates imply the existence of a global minimizer $u$ with $x_n\to u$ and $f(x_n)\to f(u)$. |

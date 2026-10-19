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

## Harmonic and variable steps

Keep the same time parameters, momentum, and initialization, and let the
step from $x_k$ to $x_{k+1}$ have size $1/M_k$. Assume $M_k>0$, the sequence
$M_k$ is nondecreasing, and the smooth upper inequality holds with constant
$M_k$ at every step. The exact proximal update is expressed by
`ProximalOptimality g gradient (M k) (y k) (x (k+1))`. Then
`fista_variable_step_weighted_rate` proves

$$
\frac{t_{n+1}^2}{M_n}\bigl(F(x_{n+1})-F(u)\bigr)
\le \frac12\|x_0-u\|^2.
$$

The sharp bound $t_{n+1}\ge(n+2)/2$ gives `fista_variable_step_rate`:

$$
F(x_{n+1})-F(u)\le\frac{2M_n\|x_0-u\|^2}{(n+2)^2}.
$$

For an $L$-smooth objective with $L>0$, choose $M_k=L(k+1)$. Thus the
proximal step size is $1/(L(k+1))$, and `fista_harmonic_rate` proves

$$
0\le F(x_n)-F(u)\le\frac{2Ln\|x_0-u\|^2}{(n+1)^2}
\qquad(n\ge1).
$$

`fista_harmonic_tendsto` concludes $F(x_n)\to F(u)$.

For literal steps $1/(k+1)$, put $M_k=k+1$. When $L>1$, some initial
steps exceed $1/L$. Choose a finite $m$ with $m>L$. For $n\ge m$, the
decreasing tail potential is

$$
P_n=\frac{t_n^2}{n+1}\bigl(F(x_n)-F(u)\bigr)
  +\frac12\|z_n-u\|^2\le P_m.
$$

Since $t_n\ge n/2$ and $P_m\ge0$, this gives

$$
F(x_n)-F(u)\le\frac{8P_m}{n}
\qquad(n\ge\max(m,1)).
$$

`fista_reciprocal_eventual_rate` expresses this as the existence of a
nonnegative constant $C$ with an eventual bound $C/n$;
`fista_reciprocal_tendsto` concludes objective convergence. These two
theorems need only a finite smooth upper constant $L$; its positivity is
unnecessary. They impose no restriction on the finite initial steps and
do not reset the momentum.

The two `*_iterates_tendsto_of_quadratic_growth` results prove $x_n\to u$
for their corresponding schedules under the same quadratic growth condition
as above. The `nesterov_fista_harmonic_*` results specialize the scaled
harmonic rate and objective convergence to $g=0$ and ordinary gradient steps.

## Declarations

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
| `fistaTime_lower_bound` | $t_{k+1}\ge(k+2)/2$ for every $k\in\mathbb N$. |
| `fista_smoothUpper_mono` (private) | If $f,G$ satisfy the smooth upper inequality at $L$ and $L\le M$, they satisfy it at $M$. |
| `fista_variable_step_potential_step` (private) | For a valid step with inverse size $M>0$, $t_{k+1}^2(F(x_{k+1})-F(u))/M+\|z_{k+1}-u\|^2/2\le t_k^2(F(x_k)-F(u))/M+\|z_k-u\|^2/2$. |
| `fista_variable_step_potential_from` (private) | With positive nondecreasing $M_k$, a minimizer $u$, and smooth upper inequalities for $k\ge m$, $t_n^2(F(x_n)-F(u))/M_n+\|z_n-u\|^2/2$ is at most its value at $m$ for every $n\ge m$. |
| `fista_variable_step_weighted_rate` | Under the variable-step assumptions above, $t_{n+1}^2(F(x_{n+1})-F(u))/M_n\le\|x_0-u\|^2/2$. |
| `fista_variable_step_rate` | Under the same assumptions, $F(x_{n+1})-F(u)\le2M_n\|x_0-u\|^2/(n+2)^2$. |
| `fista_harmonic_rate` | For $L>0$, steps $1/(L(k+1))$ satisfy $F(x_n)-F(u)\le2Ln\|x_0-u\|^2/(n+1)^2$ for $n\ge1$. |
| `fista_harmonic_tendsto` | Under the scaled harmonic assumptions, $F(x_n)\to F(u)$. |
| `fista_reciprocal_eventual_rate` | For steps $1/(k+1)$ and any finite smooth upper constant, there is $C\ge0$ such that $F(x_n)-F(u)\le C/n$ for all sufficiently large $n$. |
| `fista_reciprocal_tendsto` | Under the literal reciprocal-step assumptions, $F(x_n)\to F(u)$. |
| `fista_iterates_of_objective_tendsto` (private) | On a normed additive group, quadratic growth with $\mu>0$ and $F(x_n)\to F(u)$ imply $x_n\to u$. |
| `fista_harmonic_iterates_tendsto_of_quadratic_growth` | Under scaled harmonic updates and quadratic growth with $\mu>0$, $x_n\to u$. |
| `fista_reciprocal_iterates_tendsto_of_quadratic_growth` | Under literal reciprocal-step updates and quadratic growth with $\mu>0$, $x_n\to u$. |
| `nesterov_fista_harmonic_rate` | The scaled harmonic bound holds for $g=0$ and $x_{k+1}=y_k-G(y_k)/(L(k+1))$. |
| `nesterov_fista_harmonic_tendsto` | Under these smooth scaled harmonic updates, $f(x_n)\to f(u)$. |

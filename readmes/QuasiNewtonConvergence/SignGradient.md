# SignGradient

[Lean source](../../QuasiNewtonConvergence/SignGradient.lean)

Let $n=|\iota|$ and $E=\mathbb R^\iota$ with its Euclidean norm.
`gradientSign(g)` is the coordinate vector $\sigma(g)_i=\operatorname{sign}(g_i)$,
with $\operatorname{sign}(0)=0$. Ordinary signGD is

$$x_{k+1}=x_k-\eta_k\sigma(G(x_k)).$$

`signGradientStep` defines that update. Only exact coordinate signs are used;
the theorem `signGradientStep_congr` proves that replacing $G(x)$ by any
vector with identical signs leaves the update unchanged. The proofs may use
gradient magnitudes, but the algorithm and prescribed schedules do not.
No stochastic or corrupted-sign oracle is considered here.

## The Frank–Wolfe connection

`signBox(c,R)` means $|y_i-c_i|\le R$ for every coordinate $i$.
For $R\ge0$, the linear minimization oracle on this box is

$$s=c-R\sigma(g).$$

`sign_box_oracle_mem` proves feasibility and `sign_box_oracle` proves
$\langle g,s\rangle\le\langle g,y\rangle$ for every $y$ in the box.
`sign_oracle_scalar` is the coordinate inequality
$g(-R\operatorname{sign}(g))\le gz$ when $|z|\le R$.
`signGradientStep_as_frankWolfe` proves the exact identity

$$x-\gamma R\sigma(G(x))=x+\gamma\big((x-R\sigma(G(x)))-x\big).$$

Here the box is centered at $x$ and moves with the iterate. A fixed box
centered at zero would instead give $(1-\gamma)x-\gamma R\sigma(G(x))$.
Thus the fixed-domain Frank–Wolfe theorem cannot be applied to ordinary
signGD without checking the comparator remains in each moving box.

The identities `gradientSign_norm_sq`, `inner_gradientSign`, and
`gradient_norm_sq_le_sign_inner_sq` establish

$$\|\sigma(g)\|_2^2\le n,\quad
\langle g,\sigma(g)\rangle=\|g\|_1,\quad
\|g\|_2^2\le\|g\|_1^2.$$

## Convex objective rate from the Frank–Wolfe recurrence

Assume `SmoothUpper f G L` with $L\ge0$ and `ConvexFirstOrder f G`, the
global first-order inequalities documented in [GradientDescent](GradientDescent.md).
These hold for a differentiable convex objective with an $L$-Lipschitz gradient.
For a feasible comparator $u$ in the moving box,
`signGradient_error_bound` proves

$$h_k=f(x_k)-f(u)\le R\|G(x_k)\|_1.$$

`signGradientStep_descent` proves, for every real step $\eta$,

$$f(x-\eta\sigma(G(x)))\le f(x)-\eta\|G(x)\|_1+\frac{nL}{2}\eta^2.$$

Suppose $|u_i-x_{k,i}|\le R$ for every $k,i$, and use
$\eta_k=2R/(k+2)=\gamma_kR$. Combining the two bounds gives exactly

$$h_{k+1}\le(1-\gamma_k)h_k+\frac{nLR^2}{2}\gamma_k^2.$$

`signGradient_rate` invokes `frankWolfe_scalar_rate` to conclude
$f(x_k)-f(u)\le2nLR^2/(k+2)$ for $k\ge1$.
`signGradient_values_tendsto` additionally assumes $u$ is a global minimizer
and proves $f(x_k)\to f(u)$. The uniform distance bound is an explicit
assumption of this rate theorem, not a conclusion of convexity alone.

## Strong convexity: no assumed iterate bound

The remaining theorems use $\eta_k=1/\sqrt{k+1}$, which is positive, at most
one, tends to zero, and has a divergent sum on every tail. Assume
`SmoothUpper f G L` and `StrongConvexFirstOrder f G μ` with $L,\mu>0$.
The latter is the strong-convexity first-order inequality with term
$(\mu/2)\|y-x\|^2$.

Write $e_k=f(x_k)-f(u)$, $a_k=\|G(x_k)\|_1$, and $C=nL/2$.
The descent and strong-convexity estimates give

$$e_{k+1}\le e_k-\eta_k a_k+C\eta_k^2,
\qquad a_k^2\ge2\mu e_k.$$

`sign_scalar_decay` proves convergence for any nonnegative sequences $e,a$
satisfying these inequalities and any steps in $[0,1]$ tending to zero with
divergent sums on every tail. Its proof derives a uniform bound first:

$$e_k\le H=\max\{e_0,C^2/(2\mu)+C\}.$$

Indeed, when $a_k>C$, the error cannot increase, because $\eta_k\le1$.
When $a_k\le C$, the PL estimate bounds $e_k$ by $C^2/(2\mu)$ and the
next-step error by that quantity plus $C$.
Set $c=\min\{2\mu,1/(H+1)\}>0$. If $a_k\le1$, then
$a_k\ge a_k^2\ge2\mu e_k\ge ce_k$; otherwise $ce_k\le1<a_k$.
The recurrence therefore implies

$$e_{k+1}\le e_k-c\eta_k e_k+C\eta_k^2.$$

The reusable `scalar_subgradient_decay` lemma now forces $e_k\to0$.
Its existing proof is unchanged; it is made public for reuse here.

* `signGradient_strong_sqrt_values_tendsto` supplies this argument for a
  given global minimizer $u$ and proves objective convergence.
* `signGradient_strong_sqrt_iterates_tendsto` uses a stationary minimizer
  $G(u)=0$ and the bound $\|x_k-u\|^2\le2e_k/\mu$ to prove $x_k\to u$.
* `signGradient_strong_sqrt_converges` obtains the stationary minimizer
  from smooth strong convexity and proves both limits. Neither a minimizer
  nor an iterate bound is an input.
* `signGradientIterate` recursively constructs the ordinary signGD trajectory
  from any $x_0$ with square-root steps. `signGradientIterate_converges`
  proves both limits for this constructed trajectory under the same assumptions.

The strong-convexity result asserts convergence, without an explicit rate.
It uses the sign oracle and descent bound shared with the Frank–Wolfe proof;
the moving domains require the additional boundedness argument above.
The fixed-step sign method is not covered: it can oscillate even on $f(x)=x^2/2$.

All seventeen theorems are included in the enforcing axiom audit.

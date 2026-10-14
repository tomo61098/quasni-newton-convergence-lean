# Proximal convergence proofs

Let \(F=f+g\), where \(f\) is convex and differentiable with \(L\)-Lipschitz gradient, \(L>0\), and \(g\) is proper closed convex. Assume a minimizer \(x_*\) exists. The Lean files use a finite-valued \(g\) and explicitly assume exact proximal optimality.

## Basic proximal gradient

For \(z=\operatorname{prox}_{g/L}(x-\nabla f(x)/L)\), optimality says
\[
g(u)-g(z)\ge\langle-\nabla f(x)-L(z-x),u-z\rangle.
\]
Add this to the smooth upper bound for \(f(z)\) and the convex lower bound for \(f(u)\). The polarization identity
\[
2\langle z-x,u-z\rangle=\|u-x\|^2-\|z-x\|^2-\|u-z\|^2
\]
then gives
\[
F(z)-F(u)\le \frac L2(\|x-u\|^2-\|z-u\|^2). \tag{1}
\]
Putting \(u=x\) proves descent. Putting \(u=x_*\), telescoping, and using descent to bound the last gap by the average gives
\[
F(x_n)-F(x_*)\le \frac{L\|x_0-x_*\|^2}{2n},\quad n\ge1. \tag{2}
\]

If \(f\) is \(\mu\)-strongly convex, its lower bound adds \(-\mu\|x-u\|^2/2\) to the right of (1). For \(0<\mu\le L\), with \(u=x_*\), the nonnegative objective gap yields
\[
\|x_n-x_*\|^2\le(1-\mu/L)^n\|x_0-x_*\|^2.
\]
Using (1) again gives \(F(x_{n+1})-F(x_*)\le (L/2)(1-\mu/L)^n\|x_0-x_*\|^2\). Thus both iterates and objective values converge geometrically.

## Accelerated proximal gradient

Set \(A_0=0\), \(A_{k+1}=A_k+a_k\), and choose \(a_k>0\) so that \(La_k^2=A_{k+1}\). Put \(\theta_k=a_k/A_{k+1}\), and use the three-sequence form
\[
y_k=(1-\theta_k)x_k+\theta_kz_k,\quad
x_{k+1}=\operatorname{prox}_{g/L}(y_k-\nabla f(y_k)/L),\quad
x_{k+1}=(1-\theta_k)x_k+\theta_kz_{k+1}.
\]
Let \(v=(1-\theta_k)x_k+\theta_kx_*\). Convexity gives \(F(v)\le(1-\theta_k)F(x_k)+\theta_kF(x_*)\). In (1), take the base point \(y_k\) and comparison point \(v\). Since \(y_k-v=\theta_k(z_k-x_*)\) and \(x_{k+1}-v=\theta_k(z_{k+1}-x_*)\), the weight identity yields
\[
A_{k+1}(F(x_{k+1})-F(x_*))+\tfrac12\|z_{k+1}-x_*\|^2
\le A_k(F(x_k)-F(x_*))+\tfrac12\|z_k-x_*\|^2.
\]
With \(z_0=x_0\), this telescopes to \(A_k(F(x_k)-F(x_*))\le\|x_0-x_*\|^2/2\). Writing \(t_k=\sqrt{LA_k}\), the weight recurrence gives \(t_{k+1}^2=t_k^2+t_{k+1}\), hence \(t_{k+1}\ge t_k+1/2\) and \(A_k\ge k^2/(4L)\). Therefore
\[
F(x_k)-F(x_*)\le \frac{2L\|x_0-x_*\|^2}{k^2},\quad k\ge1. \tag{3}
\]
The Lean quadratic-rate theorem derives weight growth from these exact weight
equations using a scalar induction; callers no longer supply a separate growth
hypothesis. The weighted-potential theorem remains available independently.

If the full \(F\) is \(\mu\)-strongly convex, restart after each block of \(N\) accelerated steps. Strong convexity gives \(\|x-x_*\|^2\le 2(F(x)-F(x_*))/\mu\). By (3), each block contracts the objective gap by \(q=4L/(\mu N^2)\). Choose \(N>\sqrt{4L/\mu}\); then \(q<1\), and after \(r\) blocks the gap is at most \(q^r\) times its initial value. This is the restarted accelerated guarantee.

## Proximal BFGS

Let \(B_k\) be a symmetric positive definite BFGS approximation and minimize the proximal model
\[
g(z)+\langle\nabla f(x_k),z-x_k\rangle+
\tfrac12\langle B_k(z-x_k),z-x_k\rangle.
\]
If \(\langle B_kv,v\rangle\ge m\|v\|^2\), model optimality and smoothness give
\[
F(x_{k+1})\le F(x_k)-(m-L/2)\|x_{k+1}-x_k\|^2. \tag{4}
\]
When \(m>L/2\) and \(F\) is bounded below, summing (4) shows that squared steps are summable and step lengths tend to zero. Step lengths alone do not establish convergence to a minimizer.

For a linear objective rate, additionally assume \(F\) is \(\mu\)-strongly convex, \(\|B_k\|\le M\), and \(\nabla f\) is \(L\)-Lipschitz. Proximal optimality supplies
\[
s_{k+1}=\nabla f(x_{k+1})-\nabla f(x_k)-B_k(x_{k+1}-x_k)\in\partial F(x_{k+1}),
\]
so \(\|s_{k+1}\|\le(L+M)\|x_{k+1}-x_k\|\). Strong convexity implies \(F(x_{k+1})-F(x_*)\le\|s_{k+1}\|^2/(2\mu)\). Set \(C=(L+M)^2/(2\mu)\). Combining with (4) yields
\[
F(x_k)-F(x_*)\le
\left(\frac{C}{C+m-L/2}\right)^k(F(x_0)-F(x_*)). \tag{5}
\]
The Lean linear-rate theorem states the resulting error bound explicitly. The BFGS secant update alone does not ensure uniform bounds \(m,M\); those require additional update or line-search conditions.

Primary sources: [Beck–Teboulle, FISTA](https://epubs.siam.org/doi/abs/10.1137/080716542), [Parikh–Boyd, Proximal Algorithms](https://stanford.edu/~boyd/papers/prox_algs.html), and [Lee–Sun–Saunders, Proximal Newton-type Methods](https://stanford.edu/group/SOL/reports/SOL-2013-1.pdf).

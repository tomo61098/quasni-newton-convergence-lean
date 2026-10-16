# Dennis–Moré and Bregman convergence proofs

## Smooth and proximal Dennis–Moré

Let \(F=f+g\), with \(f\) twice differentiable near a solution \(x_*\) and \(g\) convex. Write \(H_*=\nabla^2 f(x_*)\), and let \(d_k=x_{k+1}-x_k\) solve the full proximal quasi-Newton subproblem with metric \(B_k\):
\[
0\in \nabla f(x_k)+B_kd_k+\partial g(x_{k+1}).
\]
At the solution, \(0\in\nabla f(x_*)+\partial g(x_*)\). Assume \(H_*\succeq\mu I\) for \(\mu>0\), and the directional Dennis–Moré condition
\[
\|(B_k-H_*)d_k\|\le\delta_k\|d_k\|,\qquad \delta_k\longrightarrow0.
\]
The Lean theorem also takes a quadratic Taylor bound
\(\|\nabla f(x_k)-\nabla f(x_*)-H_*(x_k-x_*)\|\le L\|x_k-x_*\|^2\). It derives this bound from a Lipschitz Hessian in a separate lemma.

Set \(e_k=x_k-x_*\), \(q_k=x_{k+1}-x_*\), and \(r_k=\nabla f(x_k)-\nabla f(x_*)-H_*e_k\). Monotonicity of \(\partial g\) between \(x_{k+1}\) and \(x_*\) gives
\[
\langle H_*q_k+(B_k-H_*)d_k+r_k,\ q_k\rangle\le0.
\]
Coercivity of \(H_*\), Cauchy–Schwarz, and cancellation of \(\|q_k\|\) yield
\[
\|q_k\|\le\frac1\mu\bigl(\|(B_k-H_*)d_k\|+\|r_k\|\bigr). \tag{1}
\]
If \(mI\preceq B_k\) and \(\|B_kv\|\le M\|v\|\), while \(\|\nabla f(x_k)-\nabla f(x_*)\|\le G\|e_k\|\), the same monotonicity inequality gives
\[
\|d_k\|\le \left(1+\frac{M+G}{m}\right)\|e_k\|. \tag{2}
\]
Substitution in (1) shows
\[
\frac{\|x_{k+1}-x_*\|}{\|x_k-x_*\|}
\le\frac{\delta_k(1+(M+G)/m)+L\|x_k-x_*\|}{\mu}
\longrightarrow0.
\]
The ratio is defined as zero once an iterate has reached \(x_*\). Setting \(g=0\) and using \(\nabla f(x_k)+B_kd_k=0\) gives the smooth Dennis–Moré theorem. The Lean file also packages a BFGS run with its secant update. It proves the conditional superlinear result for such a run; it does not infer Dennis–Moré or uniform spectral bounds from the BFGS formula alone. This matches the conditional proximal quasi-Newton theorem of [Lee, Sun, and Saunders, §3.2](https://web.stanford.edu/group/SOL/reports/SOL-2013-1.pdf).

## Bregman divergence and gradient method

For a differentiable convex kernel \(h\), define
\[
D_h(x,y)=h(y)-h(x)-\langle\nabla h(x),y-x\rangle\ge0.
\]
The algebraic identity used by both methods is
\[
\langle\nabla h(z)-\nabla h(x),u-z\rangle
=D_h(x,u)-D_h(z,u)-D_h(x,z). \tag{3}
\]

Let \(f\) be convex and \(L\)-smooth relative to \(h\):
\[
f(z)\le f(x)+\langle\nabla f(x),z-x\rangle+L D_h(x,z).
\]
For the composite Bregman gradient step, minimize the model
\(g(z)+\langle\nabla f(x),z-x\rangle+L D_h(x,z)\).
Its variational optimality condition, the convex first-order inequality for \(f\), relative smoothness, and (3) give
\[
F(z)-F(u)\le L\bigl(D_h(x,u)-D_h(z,u)\bigr),\qquad F=f+g. \tag{4}
\]
Taking \(u=x\) gives descent. Taking \(u=x_*\), telescoping (4), and using descent yields
\[
F(x_n)-F(x_*)\le\frac{L D_h(x_0,x_*)}{n},\qquad n\ge1.
\]
Thus the objective values converge to the minimum. Setting \(g=0\) gives ordinary mirror descent. Relative smoothness and the resulting Bregman first-order rates are studied by [Bauschke, Bolte, and Teboulle](https://cmps-people.ok.ubc.ca/bauschke/Research/103.pdf).

If \(f\) is also relatively \(\mu\)-strongly convex, its lower first-order
bound contributes \(-\mu D_h(x,u)\) to (4). For \(0<\mu\le L\) and a minimizer
\(x_*\), this yields
\[
D_h(x_n,x_*)\le(1-\mu/L)^nD_h(x_0,x_*),\qquad
F(x_{n+1})-F(x_*)\le L(1-\mu/L)^nD_h(x_0,x_*).
\]
If \(D_h(v,x_*)\ge\kappa\|v-x_*\|^2\) for some \(\kappa>0\), the iterates
themselves converge to \(x_*\).

## Bregman proximal point

For a convex objective \(F\), the exact Bregman proximal step minimizes
\(F(z)+L D_h(x,z)\). Its variational condition and (3) give the stronger inequality
\[
F(z)-F(u)\le
L\bigl(D_h(x,u)-D_h(z,u)-D_h(x,z)\bigr). \tag{5}
\]
Nonnegativity of \(D_h\) gives both descent and the same telescoping bound:
\[
F(x_n)-F(x_*)\le\frac{L D_h(x_0,x_*)}{n},\qquad n\ge1.
\]
This establishes convergence of objective values. Convergence of the points themselves needs an additional separation condition on the kernel; the Lean development proves it when \(D_h(v,x_*)\ge\kappa\|v-x_*\|^2\). See the original [Bregman proximal convergence analysis](https://epubs.siam.org/doi/abs/10.1137/0803026).

If the objective has the oriented relative growth bound
\(F(v)-F(x_*)\ge\mu D_h(v,x_*)\), then (5) gives
\[
D_h(x_n,x_*)\le
\left(\frac{L}{L+\mu}\right)^nD_h(x_0,x_*),\qquad
F(x_{n+1})-F(x_*)\le
L\left(\frac{L}{L+\mu}\right)^nD_h(x_0,x_*).
\]
The orientation of this growth assumption matters because Bregman divergence
need not be symmetric.

The Lean definitions use finite-valued functions and state exact variational
optimality explicitly. `BregmanExistence.lean` constructs proximal minimizers
under finite-dimensional continuity, an affine lower bound for the objective,
and strong convexity of the kernel. The recursive trajectory supplies an
affine support at every objective point, implying convexity. When the kernel
is differentiable with the supplied gradient, minimization implies variational
optimality and gives the rate theorem for that trajectory.
The differentiability assumption matters: the strong first-order
inequality alone also permits nonsmooth kernels with selected subgradients.

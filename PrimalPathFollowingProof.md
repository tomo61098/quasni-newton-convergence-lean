# Polynomial iteration rate of primal path following

Consider the standard-form linear program

\[
  \min\{c^\top x:Ax=b,\ x\geq0\}
\]

with a strictly feasible starting point. Write \(n\geq1\) for the number of
nonnegative coordinates. On \(Ax=b,\ x>0\), use the logarithmic barrier

\[
  F(x)=-\sum_{i=1}^n\log x_i,
  \qquad g_t(x)=t c^\top x+F(x),\quad t>0.
\]

Assume an initial point \(x_0\) is strictly feasible and has Newton decrement
\(\lambda_{t_0}(x_0)\leq1/4\). At iteration \(k\), set
\(t_{k+1}=(1+1/(16\sqrt n))t_k\), then take one *full feasible Newton step*
for \(g_{t_{k+1}}\) from \(x_k\) to \(x_{k+1}\). The Hessian on the tangent space
\(T=\ker A\) is positive definite, so the Newton direction is well defined.

## Neighborhood preservation

The local norm is
\(\|d\|_x^2=\sum_i(d_i/x_i)^2\) for \(d\in T\). Its dual norm on \(T^*\)
defines the Newton decrement
\(\lambda_t(x)=\|\nabla g_t(x)|_T\|_{x,*}\). Direct differentiation gives

\[
 D^2F(x)[d,d]=\sum_i(d_i/x_i)^2,
 \qquad
 |D^3F(x)[d,d,d]|
 \leq 2\left(\sum_i(d_i/x_i)^2\right)^{3/2}.
\]

Thus the barrier is self-concordant on the feasible affine space. Also
\(\|\nabla F(x)|_T\|_{x,*}\leq\sqrt n\): in the ambient space the scaled
gradient has all coordinates equal to \(-1\), and restriction cannot increase
the dual norm. If \(\lambda_{t_k}(x_k)\leq1/4\), the parameter change obeys

\[
\begin{aligned}
 \lambda_{t_{k+1}}(x_k)
 &\leq \lambda_{t_k}(x_k)
   +\frac{t_{k+1}-t_k}{t_k}\|t_kc|_T\|_{x_k,*}\\
 &\leq \frac14+\frac{1}{16\sqrt n}
       \left(\sqrt n+\frac14\right)
 \leq \frac{21}{64}<1.
\end{aligned}
\]

The standard full-Newton estimate for a self-concordant function says that,
when the decrement before the step is \(\lambda<1\), the step stays in the
domain and its new decrement is at most
\((\lambda/(1-\lambda))^2\). Therefore

\[
 \lambda_{t_{k+1}}(x_{k+1})
 \leq \left(\frac{21}{43}\right)^2<\frac14.
\]

Induction proves strict feasibility and the \(1/4\) neighborhood invariant
for every iterate. The self-concordant Newton estimate is the essential
algorithmic lemma; it cannot be replaced by a claim that each subproblem is
solved exactly.

## Primal objective gap

The restricted dual-norm definition of the decrement gives a multiplier
\(y_k\) and a residual \(e_k\) such that

\[
 t_kc+A^\top y_k=X_k^{-1}(\mathbf1+e_k),
 \qquad \|e_k\|_2=\lambda_{t_k}(x_k)\leq\frac14,
 \quad X_k=\operatorname{diag}(x_k).
\]

Consequently every coordinate of \(\mathbf1+e_k\) is positive. For *any*
feasible \(z\geq0\), the equality \(A(x_k-z)=0\) and \(z_i/x_{k,i}\geq0\)
imply

\[
\begin{aligned}
 t_k c^\top(x_k-z)
 &=\sum_i(1+e_{k,i})\left(1-\frac{z_i}{x_{k,i}}\right)\\
 &\leq\sum_i(1+e_{k,i})
 \leq\frac54 n.
\end{aligned}
\]

The argument holds against every feasible comparator, so it also bounds the
gap to the infimum when the optimal value is finite.

## Iteration count

Since \(t_k=t_0(1+1/(16\sqrt n))^k\) and
\(\log(1+u)\geq u/2\) for \(0\leq u\leq2\),

\[
 c^\top x_k-p^*
 \leq \frac{5n}{4t_0}
       \left(1+\frac1{16\sqrt n}\right)^{-k}.
\]

In particular, any nonnegative integer satisfying

\[
 k\geq32\sqrt n\log\left(\frac{5n}{4t_0\varepsilon}\right)
\]

has objective gap at most \(\varepsilon>0\). This proves
\(O(\sqrt n\log(n/(t_0\varepsilon)))\) **Newton iterations**. Establishing
polynomial *bit complexity* additionally requires a precision and linear-system
implementation analysis.

## Lean status

`QuasiNewtonConvergence/PrimalPathFollowing.lean` proves the exact and
coordinatewise residual gap inequalities and the logarithmic iteration
thresholds for sequences satisfying the stated centrality conditions. The
self-concordant full-Newton neighborhood lemma, the construction of the
multiplier/residual from the Newton decrement, and the induction tying the
defined Newton updates to those conditions are not yet formalized in Lean.

The analytic short-step argument follows the classical self-concordant barrier
method; see [Vishnoi's interior-point lecture notes](https://theory.epfl.ch/vishnoi/CargeseLectures.pdf)
and [Boyd–Vandenberghe, *Convex Optimization*, chapter 11](https://www.seas.ucla.edu/~vandenbe/cvxbook.html).

# BFGS satisfies the Dennis–Moré condition: Nocedal–Wright, Theorem 6.6

This proves the directional claim in the proof of Theorem 6.6 of Nocedal and
Wright, *Numerical Optimization*, second edition, pp. 156–160. The source is
available [here](https://studylib.net/doc/27835099/numerical-optimization-jorge-nocedal-ste).

## Statement and hypotheses

Let \(f:\mathbb R^n\to\mathbb R\) be twice continuously differentiable, let
\(G(x)=\nabla^2 f(x)\), and suppose a BFGS run has nonzero steps
\(s_k=x_{k+1}-x_k\), secant vectors
\(y_k=\nabla f(x_{k+1})-\nabla f(x_k)\), and symmetric positive definite matrices
\(B_k\). Assume \(x_k\to x_*\), \(G_*=G(x_*)\) is positive definite,
\(G\) is Lipschitz near \(x_*\), and

\[
  \sum_{k=0}^\infty\|x_k-x_*\|<\infty. \tag{6.52}
\]

The positive curvature of the secants is required so that BFGS preserves
positive definiteness. It follows locally from positive definiteness of
\(G_*\); for finitely many earlier updates it is an assumption on the run
(normally ensured by a Wolfe line search). Then

\[
  \frac{\|(B_k-G_*)s_k\|}{\|s_k\|}\longrightarrow 0.
  \tag{DM}
\]

Convergence \(x_k\to x_*\) alone is insufficient for this proof: (6.52) is
the extra hypothesis explicitly used in the book. The book states that it
follows from a separate linear convergence result in its convex setting, but
does not prove that intermediate claim in this section.

## Proof

Set \(T=G_*^{1/2}\), \(\tilde s_k=Ts_k\),
\(\tilde y_k=T^{-1}y_k\), and
\(\tilde B_k=T^{-1}B_kT^{-1}\). Congruence preserves positive
definiteness, and direct substitution shows that \(\tilde B_{k+1}\) is the
BFGS update of \(\tilde B_k\) with \(\tilde s_k,\tilde y_k\).

Let \(\bar G_k=\int_0^1G(x_k+t s_k)\,dt\). The fundamental theorem of
calculus gives \(y_k=\bar G_k s_k\). If
\(\epsilon_k=\max(\|x_k-x_*\|,\|x_{k+1}-x_*\|)\), the Lipschitz
condition and convexity of the norm imply
\(\|\bar G_k-G_*\|\le L\epsilon_k\) for all sufficiently large \(k\).
Consequently, for some constant \(a>0\),

\[
  \|\tilde y_k-\tilde s_k\|
  \le a\epsilon_k\|\tilde s_k\|. \tag{1}
\]

Moreover \(\sum_k\epsilon_k<\infty\) by (6.52). In particular,
\(\epsilon_k\to0\).

For brevity omit the subscript \(k\) and define

\[
q=\frac{\tilde s^{\mathsf T}\tilde B\tilde s}{\|\tilde s\|^2},
\qquad
c=\frac{\tilde s^{\mathsf T}\tilde B\tilde s}
        {\|\tilde s\|\,\|\tilde B\tilde s\|},
\qquad
m=\frac{\tilde y^{\mathsf T}\tilde s}{\|\tilde s\|^2},
\qquad
M=\frac{\|\tilde y\|^2}{\tilde y^{\mathsf T}\tilde s}.
\]

Positive definiteness gives \(q,m,M>0\) and \(0<c\le1\). From (1),
\(\|\tilde y\|\le(1+a\epsilon)\|\tilde s\|\) and
\(m\ge1-a\epsilon\). For sufficiently small \(\epsilon\), elementary
algebra and \(-\log(1-t)\le2t\) for \(0\le t\le1/2\) yield a constant
\(C>0\) with

\[
 M-\log m-1\le C\epsilon. \tag{2}
\]

For example, the coarse bound
\(M\le (1+a\epsilon)^2/(1-a\epsilon)\) suffices. This avoids needing the
sharper estimate printed as (6.57) in the book.

Write \(\psi(A)=\operatorname{tr}A-\log\det A\) for positive definite
\(A\). Each eigenvalue \(\lambda>0\) contributes
\(\lambda-\log\lambda\ge1\), so \(\psi(A)\ge n\). The two BFGS identities
are

\[
\operatorname{tr}(\tilde B_{k+1})
 =\operatorname{tr}(\tilde B_k)
  -\frac{\|\tilde B_k\tilde s_k\|^2}
         {\tilde s_k^{\mathsf T}\tilde B_k\tilde s_k}
  +\frac{\|\tilde y_k\|^2}
         {\tilde y_k^{\mathsf T}\tilde s_k},
\qquad
\det\tilde B_{k+1}
 =\det\tilde B_k\,
  \frac{\tilde y_k^{\mathsf T}\tilde s_k}
       {\tilde s_k^{\mathsf T}\tilde B_k\tilde s_k}.
\]

The trace identity follows by taking traces of the rank two update. The
determinant identity follows from the matrix determinant lemma, or by
restricting the update to the span of \(\tilde B_k\tilde s_k\) and
\(\tilde y_k\). Since
\(\|\tilde B\tilde s\|^2/
 (\tilde s^{\mathsf T}\tilde B\tilde s)=q/c^2\), they give exactly

\[
\psi(\tilde B_{k+1})-\psi(\tilde B_k)
 = M-\log m-1
   -\underbrace{(-\log c^2)}_{A_k}
   -\underbrace{\left(\frac q{c^2}-1-
                     \log\frac q{c^2}\right)}_{R_k}.
 \tag{3}
\]

Both \(A_k\) and \(R_k\) are nonnegative: \(c^2\le1\) and
\(t-1-\log t\ge0\) for \(t>0\). Combining (2) and (3), summing from a
sufficiently large index \(K\) through \(N\), and using the lower bound
for \(\psi\), gives

\[
 \sum_{k=K}^{N}(A_k+R_k)
 \le \psi(\tilde B_K)-n+C\sum_{k=K}^{N}\epsilon_k
 \le \psi(\tilde B_K)-n+C\sum_{k=K}^{\infty}\epsilon_k<\infty.
\]

Thus \(A_k\to0\) and \(R_k\to0\). As \(-\log t=0\) on \((0,1]\)
only at \(t=1\), we obtain \(c_k^2\to1\). Also
\(t-1-\log t\) has its unique zero at \(t=1\) and tends to infinity as
\(t\downarrow0\) or \(t\to\infty\); hence
\(q_k/c_k^2\to1\), so \(q_k\to1\).

Finally, expansion of the square gives

\[
 \frac{\|(\tilde B_k-I)\tilde s_k\|^2}{\|\tilde s_k\|^2}
 =\frac{q_k^2}{c_k^2}-2q_k+1\longrightarrow0.
\]

Because
\((\tilde B_k-I)\tilde s_k=T^{-1}(B_k-G_*)s_k\), and because
\(T,T^{-1}\) are fixed bounded invertible operators, this is equivalent
to (DM). This is the Dennis–Moré conclusion of Theorem 6.6.

## Lean status

[`BFGSDennisMore.lean`](QuasiNewtonConvergence/BFGSDennisMore.lean)
formalizes the exact scalar identity (3), proves both defects are
nonnegative, and proves the telescoping implication: a nonnegative potential
and summable error imply summability, hence convergence to zero, of both
defects. It also links indexed scalar trace and determinant equations to
the normalized directional error, proves the two ratios tend to one, and
formalizes the geometric identity (6.47).
[`BFGSMatrix.lean`](QuasiNewtonConvergence/BFGSMatrix.lean) proves the trace
and determinant identities for the bundled `bfgsUpdateMap`, positivity of the
determinant, and the trace–logdet lower bound.
[`BFGSDirectional.lean`](QuasiNewtonConvergence/BFGSDirectional.lean) uses
these results to derive the normalized directional condition from initial
positive definiteness, positive secant curvature, and a summable secant-error
bound. The change-of-coordinates and secant-error estimates from local Hessian
regularity remain to be connected in Lean.

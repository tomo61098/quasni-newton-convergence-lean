# Why Karmarkar's interior point algorithm is polynomial time

This is a proof for Karmarkar's **projective** algorithm. Its defining map is
the fractional transformation (1), whose denominator cancels in the invariant
potential calculation (5). It follows the canonical problem and potential
argument in [Karmarkar, *A new polynomial-time algorithm for linear
programming* (1984)](https://www.stat.uchicago.edu/~lekheng/courses/302/classics/karmarkar.pdf),
Sections 2–5. The elementary estimate below gives a slightly different
constant from the paper. The paper's sharper implementation bound is stated
at the end.

## The precise claim

Let rational LP input have total encoding length \(B\), and let \(n\) be
the number of variables after the usual polynomial-size reduction. Karmarkar's
method solves it with a number of bit operations polynomial in \(n+B\).
This is a **polynomial** bound, not merely a quasipolynomial one. The core
canonical algorithm needs \(O(nL)\) projective steps, where \(L\) is a
determinant and coefficient length bounded polynomially by \(n+B\). The
historical paper
gives the sharper implementation count \(O(n^{3.5}L)\) arithmetic operations
on \(O(L)\)-bit numbers, where \(L\) is its determinant-based input-size
parameter.

The canonical decision problem is

\[
 P=\{x\in\mathbb R^n:Ax=0,\;\mathbf1^Tx=1,\;x\ge0\},
 \qquad \min_{x\in P}c^Tx.
\]

The data are rational, the center \(x^{(0)}=\mathbf1/n\) belongs to \(P\),
and the task is to decide whether the minimum is zero or positive. We assume
\(c^Tx^{(0)}>0\); otherwise the starting point is already a zero. We take
\(n\ge2\), since \(n=1\) is immediate. The canonical reduction ensures
\(c^Tx\ge0\) on \(P\), which is essential for the logarithm of the objective.
Section 5 of the paper supplies a polynomial-size reduction from a general
rational LP, including a strictly feasible artificial start and a zero-target
feasibility problem. We first analyze the zero-target case and then the
positive-minimum case.

## One projective step

At a strictly positive feasible point \(a\), put \(D=\operatorname{diag}(a)\).
Map the simplex to itself by

\[
 y_i=\frac{x_i/a_i}{\sum_jx_j/a_j},\qquad
 x_i=\frac{a_i y_i}{\sum_j a_jy_j}.
 \tag{1}
\]

The point \(a\) becomes \(u=\mathbf1/n\). In the \(y\)-coordinates the
feasible affine space is \(ADy=0,\;\mathbf1^Ty=1\). Its tangent space is
\(S=\ker(AD)\cap\mathbf1^\perp\). Let \(p\) be the orthogonal projection
of \(Dc\) onto \(S\). Let

\[
 r=\frac1{\sqrt{n(n-1)}},\qquad \alpha=\frac14,
 \qquad y=u-\alpha r\frac p{\|p\|}. \tag{2}
\]

The case \(p=0\) with \(c^Ta>0\) cannot occur while the optimum is zero:
it would make the transformed objective constant on the feasible affine
space. The radius \(r\) is the inscribed radius of the standard simplex
in its affine hull. Thus (2) is feasible and strictly positive. Applying
the inverse of (1) gives the next iterate \(a^+\).

The normalization denominator \(\sum_j a_jy_j\) depends on the new point.
The inverse map preserves both \(Ax=0\) and \(\mathbf1^Tx=1\); its denominator
is essential to the potential identity below.

More precisely, if \(d=y-u\), then \(\mathbf1^Td=0\) and
\(\|d\|=\alpha r\). Cauchy–Schwarz applied to
\(d_i=\langle e_i-u,d\rangle\) gives

\[
 |d_i|\le \sqrt{\frac{n-1}{n}}\|d\|=\frac\alpha n.
 \tag{3}
\]

Hence \(y_i=(1+t_i)/n\), where \(|t_i|\le\alpha\),
\(\sum_i t_i=0\), and all \(y_i>0\).

## A constant drop in Karmarkar's potential

Use the potential

\[
 \Phi(x)=n\log(c^Tx)-\sum_{i=1}^n\log x_i. \tag{4}
\]

Substitution in (1) cancels the projective denominator exactly:

\[
 \Phi(a^+)-\Phi(a)
 =n\log\frac{(Dc)^Ty}{(Dc)^Tu}
   -\sum_i\log\frac{y_i}{u_i}. \tag{5}
\]

Let \(z\) be the image under (1) of a feasible optimum. Then
\((Dc)^Tz=0\). Since \(u-z\in S\),

\[
 (Dc)^Tu=p^T(u-z)
 \le\|p\|\,\|u-z\|
 \le\|p\|R,
 \qquad R=\sqrt{\frac{n-1}{n}}.
\]

The last inequality holds for every point of the simplex. Thus the
fractional objective decrease in the transformed space is

\[
 \theta:=\frac{\alpha r\|p\|}{(Dc)^Tu}
 \ge\frac{\alpha r}{R}=\frac\alpha{n-1}.
\]

In the zero-target case \(0<\theta<1\): a positive feasible point cannot
have zero objective unless the objective vanishes throughout the feasible
affine space, contrary to \(c^Ta>0\). Using
\(\log(1-\theta)\le-\theta\), the first term in (5) is at most
\(-n\alpha/(n-1)\le-\alpha\).

For the second term use the elementary inequality

\[
 -\log(1+t)\le -t+\frac{t^2}{2(1-\alpha)}
 \quad\text{when }|t|\le\alpha<1.
\]

It follows by integrating the derivative of \(t-\log(1+t)\). Since
\(\sum_i t_i=0\) and
\(\sum_i t_i^2=n^2\|d\|^2=\alpha^2n/(n-1)\),

\[
 -\sum_i\log(y_i/u_i)
 \le\frac{\alpha^2n}{2(n-1)(1-\alpha)}
 \le\frac{\alpha^2}{1-\alpha}=\frac1{12}.
\]

Combining these bounds in (5) proves the uniform decrease

\[
 \boxed{\Phi(a^+)\le\Phi(a)-\tfrac16.} \tag{6}
\]

This explicit constant is for the exact projected step. The original paper
uses a related potential estimate and permits a smaller fixed constant
under approximate computations.

## Iteration bound and exact termination

For any positive point in the simplex, the arithmetic–geometric mean
inequality gives \(\prod_i x_i\le n^{-n}\). Therefore

\[
 \Phi(x)\ge n\log(nc^Tx).
\]

At \(x^{(0)}=\mathbf1/n\), equality holds. Applying (6) repeatedly yields

\[
 c^Tx^{(k)}
 \le c^Tx^{(0)}\exp\!\left(-\frac{k}{6n}\right). \tag{7}
\]

Thus \(O(n\log(c^Tx^{(0)}/\varepsilon))\) steps make the objective at
most \(\varepsilon\).

For rational data, clear denominators to obtain integer constraint
coefficients **and an integer objective vector**. Every vertex is a basic
solution, so Cramer's rule expresses its coordinates with integer numerators
and a nonzero integer basis determinant.
Hadamard's inequality bounds the absolute determinant by a number
\(D\le2^{\operatorname{poly}(n,B)}\). Consequently, a strictly positive
objective value at a vertex is at least \(1/D\). Choose
\(\varepsilon<1/D\). Starting from \(x^{(k)}\), move along feasible
directions of nonincreasing objective until reaching a vertex. Each move
sets at least one positive coordinate to zero, so at most \(n\) such
linear-algebra steps are needed. The resulting vertex has objective below
\(1/D\), and therefore has objective **exactly zero**. This gives an
optimal rational certificate. Since \(\log D=\operatorname{poly}(n,B)\),
(7) gives a polynomial iteration bound. Karmarkar's determinant-based
parameter \(L\) packages these bounds to obtain \(O(nL)\) iterations.

The same bound handles a **positive minimum**. The algorithm checks whether
each step gives the guaranteed potential decrease. If the check fails, (6)
implies that the minimum is positive. If every check succeeded for more than
\(\max\{0,6n\log(Dc^Tx^{(0)})\}\) steps, (7) would give an interior point with objective
below \(1/D\). Moving to a vertex without increasing the objective would
then yield a zero-objective vertex, contradicting a positive minimum. Hence
within polynomially many steps either a zero certificate is found or a failed
decrease certifies a positive minimum. This is the canonical decision
procedure.

## Why this is a bit-complexity result

Counting exact real-arithmetic steps alone would not prove polynomial
Turing time: (2) involves a norm, and unrestricted rational denominators
could grow. Here a polynomial-precision implementation suffices.

Equation (3) and the inverse map give the coordinate-wise estimate

\[
 \frac{a_i^+}{a_i}
 =\frac{1+t_i}{\sum_j a_j(1+t_j)}
 \ge\frac{1-\alpha}{1+\alpha}=\frac35.
 \tag{8}
\]

If each computed point is rounded within one tenth of the current minimum
coordinate **inside the fixed feasible affine space**, its next coordinates
remain at least half their previous values. Up to the polynomial iteration
limit \(K\), all coordinates are therefore at least \(1/(n2^K)\). At a
step whose exact output still has objective at least \(\varepsilon/2\),
the objective along a sufficiently short rounding segment stays above
\(\varepsilon/4\). On that region the gradient
of (4),

\[
 \nabla\Phi(x)=\frac{nc}{c^Tx}-(1/x_1,\ldots,1/x_n),
\]

has norm at most \(2^{\operatorname{poly}(n,B,K)}\). Hence rounding to
\(2^{-\operatorname{poly}(n,B,K)}\) absolute accuracy changes the potential by
less than \(1/48\). Approximation of the projected step to the same accuracy
costs another \(1/48\), leaving a decrease of at least \(1/8\) per step.
If the exact output instead has objective below \(\varepsilon/2\), choose
the rounding accuracy also below
\(\varepsilon/(2n\|c\|_\infty)\); its rounded objective is then at most
\(\varepsilon\), and the algorithm stops.
Compute a rational basis for the fixed affine feasible space by Gaussian
elimination, round coordinates in that basis to a common dyadic grid of
\(P=\operatorname{poly}(n,B,K)\) bits, and choose \(P\) large enough to absorb
the basis condition number. The grid bounds every stored iterate's bit length
by \(O(P+\operatorname{poly}(n,B))\), independently of earlier denominators.
For each stored iterate, the transformed matrix and cost vector therefore
have polynomial bit length. A rational linear solve computes the exact
projection \(p\); Cramer's rule and Hadamard's bound give polynomial bit
length for its coordinates. Square-root approximation and normalization to
\(P\) bits take polynomial bit time. The projected direction does not become
too small to normalize before termination: the estimate above gives
\(\|p\|\ge(Dc)^Tu/R=(c^Ta)/(nR)\ge\varepsilon/(nR)\).
Use a rational scalar multiple of the exact rational vector \(p\), so the
approximate projected point remains in the transformed feasible affine space.
Round its inverse projective image in the original affine feasible space.
Thus each step consists of polynomially many operations on polynomial-bit
rationals. With the verified decrease \(1/8\), increase the iteration cap by
the corresponding constant factor; it remains polynomial.

The original paper optimizes the linear algebra further: Sections 6.1–6.3
use rank-one inverse updates, obtaining \(O(n^{2.5})\) arithmetic operations
per step on average. Its abstract and Section 1.6 state the resulting
\(O(n^{3.5}L)\) arithmetic operations on \(O(L)\)-bit numbers. This sharper
bound is separate from the simpler polynomial implementation proved above.

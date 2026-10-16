# KarmarkarBitBounds

Integer gaps and bit bounds.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains.

Definitions from other modules: [KarmarkarProjective](KarmarkarProjective.md).

## Definition: `karmarkarCommonDenominatorPoint`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L30)

Let $n: \mathbb{N}$; $q: I_{n}\to \mathbb{Z}$; $D: \mathbb{N}$.

Define

$$
\operatorname{rationalPoint}\left(q,\,D\right) := \left(i\mapsto \frac{q\left(i\right)}{D}\right)
$$

## Theorem: `karmarkar_integer_objective_common_denominator`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L36)

Let $n: \mathbb{N}$; $c, q: I_{n}\to \mathbb{Z}$; $D: \mathbb{N}$.

Then

$$
\operatorname{cost}\left(\left(i\mapsto c\left(i\right)\right),\,\operatorname{rationalPoint}\left(q,\,D\right)\right) = \frac{\sum_{i} c\left(i\right) \, q\left(i\right)}{D}
$$

## Theorem: `karmarkar_positive_vertex_gap`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L54)

Let $n: \mathbb{N}$; $c, q: I_{n}\to \mathbb{Z}$; $D: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < D\\[4pt]0 < \operatorname{cost}\left(\left(i\mapsto c\left(i\right)\right),\,\operatorname{rationalPoint}\left(q,\,D\right)\right)
\end{gathered}
$$

Then

$$
\frac{1}{D} \le \operatorname{cost}\left(\left(i\mapsto c\left(i\right)\right),\,\operatorname{rationalPoint}\left(q,\,D\right)\right)
$$

## Theorem: `karmarkar_integer_determinant_bound`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L74)

Let $n, B: \mathbb{N}$; $M: \mathbb{Z}^{I_{n}\times I_{n}}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,j,\quad \left|M\left(i,\,j\right)\right| \le B
\end{gathered}
$$

Then

$$
\left|\det\left(M\right)\right| \le n! \, B^{n}
$$

## Theorem: `karmarkar_determinant_polynomial_bit_bound`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L105)

Let $n, B, b: \mathbb{N}$; $M: \mathbb{Z}^{I_{n}\times I_{n}}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,j,\quad \left|M\left(i,\,j\right)\right| \le B\\[4pt]B \le 2^{b}
\end{gathered}
$$

Then

$$
\left|\det\left(M\right)\right| \le 2^{n \, \left(n + b\right)}
$$

## Theorem: `karmarkar_positive_gap_from_bit_bound`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L130)

Let $n: \mathbb{N}$; $c, q: I_{n}\to \mathbb{Z}$; $D, P: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < D\\[4pt]D \le 2^{P}\\[4pt]0 < \operatorname{cost}\left(\left(i\mapsto c\left(i\right)\right),\,\operatorname{rationalPoint}\left(q,\,D\right)\right)
\end{gathered}
$$

Then

$$
\frac{1}{2^{P}} \le \operatorname{cost}\left(\left(i\mapsto c\left(i\right)\right),\,\operatorname{rationalPoint}\left(q,\,D\right)\right)
$$

## Theorem: `karmarkar_cramer_common_denominator`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L146)

Let $n: \mathbb{N}$; $M: \mathbb{Z}^{I_{n}\times I_{n}}$; $b: I_{n}\to \mathbb{Z}$; $x: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\det\left(M\right) \ne 0\\[4pt]M \, x = \left(i\mapsto b\left(i\right)\right)
\end{gathered}
$$

Then

$$
\exists q\in I_{n}\to \mathbb{Z},\quad \forall i,\quad x\left(i\right) = \frac{q\left(i\right)}{\det\left(M\right)}
$$

## Theorem: `karmarkar_dyadic_numerator_bits`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L187)

Let $P, q: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
q \le 2^{P}
\end{gathered}
$$

Then

$$
q < 2^{P + 1}
$$

## Theorem: `karmarkar_inverse_coordinate_retention`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L197)

Let $n: \mathbb{N}$; $a, y: I_{n}\to \mathbb{R}$; $U: \mathbb{R}$; $i: I_{n}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad 0 < a\left(i\right)\\[4pt]\sum_{i} a\left(i\right) = 1\\[4pt]0 < U\\[4pt]\forall i,\quad \frac{3}{5} \, U \le y\left(i\right)\\[4pt]\forall i,\quad y\left(i\right) \le U
\end{gathered}
$$

Then

$$
\frac{3}{5} \, a\left(i\right) \le \operatorname{Kinv}\left(a,\,y,\,i\right)
$$

## Theorem: `karmarkar_coordinate_margin_after_steps`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L224)

Let $n: \mathbb{N}$; $a: \mathbb{N}\to I_{n}\to \mathbb{R}$; $k: \mathbb{N}$; $i: I_{n}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad a\left(0,\,i\right) = \frac{1}{n}\\[4pt]\forall k,i,\quad \frac{3}{5} \, a\left(k,\,i\right) \le a\left(k + 1,\,i\right)
\end{gathered}
$$

Then

$$
\frac{\left(\frac{3}{5}\right)^{k}}{n} \le a\left(k,\,i\right)
$$

## Theorem: `karmarkar_binary_coordinate_margin`

[Source](../../QuasiNewtonConvergence/KarmarkarBitBounds.lean#L245)

Let $n: \mathbb{N}$; $a: \mathbb{N}\to I_{n}\to \mathbb{R}$; $k: \mathbb{N}$; $i: I_{n}$.

Assume all of the following.

$n\ne0$.

$$
\begin{gathered}
\forall i,\quad a\left(0,\,i\right) = \frac{1}{n}\\[4pt]\forall k,i,\quad \frac{3}{5} \, a\left(k,\,i\right) \le a\left(k + 1,\,i\right)
\end{gathered}
$$

Then

$$
\frac{\left(\frac{1}{2}\right)^{k}}{n} \le a\left(k,\,i\right)
$$


# SimplexPhaseOne

Phase I feasibility constructions.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean)

All scalar inequalities are over the indicated real, integer, or natural-number domains. Let $n,m\in\mathbb{N}$.

Definitions from other modules: [KarmarkarProjective](KarmarkarProjective.md).

## Definition: `phaseOneOriginalFeasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L21)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{OriginalFeasible}\left(A,\,b,\,x\right) \Longleftrightarrow \begin{gathered}
\forall j,\quad 0 \le x\left(j\right)\\
\land\quad A\left(x\right) = b
\end{gathered}
$$

## Definition: `phaseOneAuxiliaryFeasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L27)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$; $a: I_{m}\to \mathbb{R}$.

Define

$$
\operatorname{AuxFeasible}\left(A,\,b,\,x,\,a\right) \Longleftrightarrow \begin{gathered}
\forall j,\quad 0 \le x\left(j\right)\\
\land\quad \forall i,\quad 0 \le a\left(i\right)\\
\land\quad \forall i,\quad A\left(x,\,i\right) + a\left(i\right) = b\left(i\right)
\end{gathered}
$$

## Definition: `phaseOneObjective`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L34)

Let $a: I_{m}\to \mathbb{R}$.

Define

$$
\operatorname{phaseOneObjective}\left(a\right) := \sum_{i} a\left(i\right)
$$

## Theorem: `phaseOne_initial_feasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L38)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 \le b\left(i\right)
\end{gathered}
$$

Then

$$
\operatorname{AuxFeasible}\left(A,\,b,\,0,\,b\right)
$$

## Theorem: `phaseOne_all_zero_iff_rhs_zero`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L48)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$.

Then

$$
\operatorname{AuxFeasible}\left(A,\,b,\,0,\,0\right) \Longleftrightarrow b = 0
$$

## Definition: `phaseOneInequalityFeasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L62)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$.

Define

$$
\operatorname{InequalityFeasible}\left(A,\,b,\,x\right) \Longleftrightarrow \begin{gathered}
\forall j,\quad 0 \le x\left(j\right)\\
\land\quad \forall i,\quad A\left(x,\,i\right) \le b\left(i\right)
\end{gathered}
$$

## Theorem: `simplex_slack_iff_inequality`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L69)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$.

Then

$$
\operatorname{InequalityFeasible}\left(A,\,b,\,x\right) \Longleftrightarrow \left(\exists s,\quad \operatorname{AuxFeasible}\left(A,\,b,\,x,\,s\right)\right)
$$

## Theorem: `phaseOne_objective_nonneg`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L87)

Let $a: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 \le a\left(i\right)
\end{gathered}
$$

Then

$$
0 \le \operatorname{phaseOneObjective}\left(a\right)
$$

## Theorem: `phaseOne_artificials_zero`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L94)

Let $a: I_{m}\to \mathbb{R}$; $i: I_{m}$.

Assume all of the following.

$$
\begin{gathered}
\forall i,\quad 0 \le a\left(i\right)\\[4pt]\operatorname{phaseOneObjective}\left(a\right) = 0
\end{gathered}
$$

Then

$$
a\left(i\right) = 0
$$

## Theorem: `phaseOne_zero_gives_original`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L104)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$; $a: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{AuxFeasible}\left(A,\,b,\,x,\,a\right)\\[4pt]\operatorname{phaseOneObjective}\left(a\right) = 0
\end{gathered}
$$

Then

$$
\operatorname{OriginalFeasible}\left(A,\,b,\,x\right)
$$

## Theorem: `phaseOne_original_gives_zero`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L119)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{OriginalFeasible}\left(A,\,b,\,x\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\operatorname{AuxFeasible}\left(A,\,b,\,x,\,0\right)\\
\land\quad \operatorname{phaseOneObjective}\left(0\right) = 0
\end{gathered}
$$

## Theorem: `phaseOne_feasible_iff_zero_objective`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L133)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$.

Then

$$
\left(\exists x,\quad \operatorname{OriginalFeasible}\left(A,\,b,\,x\right)\right) \Longleftrightarrow \left(\exists x,a,\quad \operatorname{AuxFeasible}\left(A,\,b,\,x,\,a\right) \land \operatorname{phaseOneObjective}\left(a\right) = 0\right)
$$

## Theorem: `phaseOne_positive_optimum_infeasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L147)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $\operatorname{astar}: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\forall x,a,\quad \operatorname{AuxFeasible}\left(A,\,b,\,x,\,a\right) \Longrightarrow \operatorname{phaseOneObjective}\left(\operatorname{astar}\right) \le \operatorname{phaseOneObjective}\left(a\right)\\[4pt]0 < \operatorname{phaseOneObjective}\left(\operatorname{astar}\right)
\end{gathered}
$$

Then

$$
\neg\left(\exists x,\quad \operatorname{OriginalFeasible}\left(A,\,b,\,x\right)\right)
$$

## Theorem: `phaseOne_optimum_zero_iff_original_feasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L162)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x_\star: I_{n}\to \mathbb{R}$; $\operatorname{astar}: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{AuxFeasible}\left(A,\,b,\,x_\star,\,\operatorname{astar}\right)\\[4pt]\forall x,a,\quad \operatorname{AuxFeasible}\left(A,\,b,\,x,\,a\right) \Longrightarrow \operatorname{phaseOneObjective}\left(\operatorname{astar}\right) \le \operatorname{phaseOneObjective}\left(a\right)
\end{gathered}
$$

Then

$$
\operatorname{phaseOneObjective}\left(\operatorname{astar}\right) = 0 \Longleftrightarrow \left(\exists x,\quad \operatorname{OriginalFeasible}\left(A,\,b,\,x\right)\right)
$$

## Definition: `phaseOnePositivePart`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L182)

Let $b: I_{m}\to \mathbb{R}$.

Define

$$
\operatorname{PositivePart}\left(b\right) := \left(i\mapsto \max\{b\left(i\right),0\}\right)
$$

## Definition: `phaseOneNegativePart`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L185)

Let $b: I_{m}\to \mathbb{R}$.

Define

$$
\operatorname{NegativePart}\left(b\right) := \left(i\mapsto \max\{-b\left(i\right),0\}\right)
$$

## Theorem: `phaseOne_positive_negative_parts`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L188)

Let $b: I_{m}\to \mathbb{R}$; $i: I_{m}$.

Then

$$
\operatorname{PositivePart}\left(b,\,i\right) - \operatorname{NegativePart}\left(b,\,i\right) = b\left(i\right)
$$

## Definition: `phaseOneSignedAuxiliaryFeasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L200)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$; $p, q: I_{m}\to \mathbb{R}$.

Define

$$
\operatorname{SignedAuxFeasible}\left(A,\,b,\,x,\,p,\,q\right) \Longleftrightarrow \begin{gathered}
\forall j,\quad 0 \le x\left(j\right)\\
\land\quad \forall i,\quad 0 \le p\left(i\right)\\
\land\quad \forall i,\quad 0 \le q\left(i\right)\\
\land\quad \forall i,\quad A\left(x,\,i\right) + p\left(i\right) - q\left(i\right) = b\left(i\right)
\end{gathered}
$$

## Definition: `phaseOneSignedObjective`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L207)

Let $p, q: I_{m}\to \mathbb{R}$.

Define

$$
\operatorname{SignedObjective}\left(p,\,q\right) := \sum_{i} p\left(i\right) + q\left(i\right)
$$

## Theorem: `phaseOne_signed_initial_feasible`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L210)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$.

Then

$$
\operatorname{SignedAuxFeasible}\left(A,\,b,\,0,\,\operatorname{PositivePart}\left(b\right),\,\operatorname{NegativePart}\left(b\right)\right)
$$

## Theorem: `phaseOne_signed_zero_gives_original`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L223)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$; $p, q: I_{m}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SignedAuxFeasible}\left(A,\,b,\,x,\,p,\,q\right)\\[4pt]\operatorname{SignedObjective}\left(p,\,q\right) = 0
\end{gathered}
$$

Then

$$
\operatorname{OriginalFeasible}\left(A,\,b,\,x\right)
$$

## Theorem: `phaseOne_signed_original_gives_zero`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L242)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$; $x: I_{n}\to \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{OriginalFeasible}\left(A,\,b,\,x\right)
\end{gathered}
$$

Then

$$
\begin{gathered}
\operatorname{SignedAuxFeasible}\left(A,\,b,\,x,\,0,\,0\right)\\
\land\quad \operatorname{SignedObjective}\left(0,\,0\right) = 0
\end{gathered}
$$

## Theorem: `phaseOne_signed_feasible_iff_zero_objective`

[Source](../../QuasiNewtonConvergence/SimplexPhaseOne.lean#L255)

Let $A: \mathcal{L}_{\mathbb{R}}(I_{n}\to \mathbb{R},I_{m}\to \mathbb{R})$; $b: I_{m}\to \mathbb{R}$.

Then

$$
\left(\exists x,\quad \operatorname{OriginalFeasible}\left(A,\,b,\,x\right)\right) \Longleftrightarrow \left(\exists x,p,q,\quad \operatorname{SignedAuxFeasible}\left(A,\,b,\,x,\,p,\,q\right) \land \operatorname{SignedObjective}\left(p,\,q\right) = 0\right)
$$


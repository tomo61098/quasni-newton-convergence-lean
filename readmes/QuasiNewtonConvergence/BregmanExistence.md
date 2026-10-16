# BregmanExistence

Bregman proximal existence and optimality.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BregmanExistence.lean)

Let $E$ be a real inner product space with its induced norm. Here $E$ is finite dimensional.

Definitions from other modules: [Bregman](Bregman.md).

## Theorem: `convexOn_of_affine_support` (private helper)

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L27)

Let $F: E\to \mathbb{R}$; $v: E\to E$.

Assume all of the following.

$$
\begin{gathered}
\forall x,y,\quad F\left(x\right) + \left\langle v\left(x\right),y - x\right\rangle \le F\left(y\right)
\end{gathered}
$$

Then

$$
\operatorname{ConvexOn}(F,\mathrm{univ})
$$

## Theorem: `bregmanProximalOptimality_of_minimizes`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L51)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $L: \mathbb{R}$; $x, z: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{ConvexOn}(F,\mathrm{univ})\\[4pt]\nabla h\left(z\right) = \operatorname{dh}\left(z\right)\\[4pt]\forall u,\quad F\left(z\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,z\right) \le F\left(u\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right)
\end{gathered}
$$

Then

$$
\operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x,\,z\right)
$$

## Theorem: `exists_bregmanProximal_minimizer`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L109)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x, v: E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall z,\quad F\left(x\right) + \left\langle v,z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)
\end{gathered}
$$

Then

$$
\exists z\in E,\quad \forall u\in E,\quad F\left(z\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,z\right) \le F\left(u\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right)
$$

## Definition: `bregmanProximalStep`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L173)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)
\end{gathered}
$$

Define

$$
\operatorname{BregmanStep}(F,h,dh,v,L,\mu,x)\in\underset{z\in E}{\operatorname{argmin}}\,\bigl\{F(z)+L\operatorname{D}(h,dh,x,z)\bigr\}.
$$
A minimizer is selected once for each input point.

## Theorem: `bregmanProximalStep_minimizes`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L181)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x, u: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)
\end{gathered}
$$

Then

$$
F\left(\operatorname{BregmanStep}\left(F,\,h,\,\operatorname{dh},\,v,\,L,\,\mu,\,x\right)\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,\operatorname{BregmanStep}\left(F,\,h,\,\operatorname{dh},\,v,\,L,\,\mu,\,x\right)\right) \le F\left(u\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x,\,u\right)
$$

## Definition: `bregmanProximalIterate`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L196)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x_{0}: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)
\end{gathered}
$$

Define

$$
\begin{gathered}
X:=\operatorname{BregmanIterate}(F,h,dh,v,L,\mu,x_0),\\
X(0)=x_0,\\
X(k+1)=\operatorname{BregmanStep}(F,h,dh,v,L,\mu,X(k))\quad(k\in\mathbb N).
\end{gathered}
$$

## Theorem: `bregmanProximalIterate_minimizes`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L206)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x_{0}: E$; $k: \mathbb{N}$; $u: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)
\end{gathered}
$$

Set

$$
x:=\operatorname{BregmanIterate}\left(F,\,h,\,\operatorname{dh},\,v,\,L,\,\mu,\,x_{0}\right)
$$

Then

$$
F\left(x\left(k + 1\right)\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,x\left(k + 1\right)\right) \le F\left(u\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,u\right)
$$

## Theorem: `bregmanProximalIterate_optimality`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L221)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x_{0}: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)\\[4pt]\forall z,\quad \nabla h\left(z\right) = \operatorname{dh}\left(z\right)
\end{gathered}
$$

Set

$$
x:=\operatorname{BregmanIterate}\left(F,\,h,\,\operatorname{dh},\,v,\,L,\,\mu,\,x_{0}\right)
$$

Then

$$
\operatorname{BregmanProxOpt}\left(F,\,h,\,\operatorname{dh},\,L,\,x\left(k\right),\,x\left(k + 1\right)\right)
$$

## Theorem: `bregmanProximalIterate_convex_rate`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L237)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x_{0}, u: E$; $k: \mathbb{N}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)\\[4pt]\forall z,\quad \nabla h\left(z\right) = \operatorname{dh}\left(z\right)
\end{gathered}
$$

Set

$$
x:=\operatorname{BregmanIterate}\left(F,\,h,\,\operatorname{dh},\,v,\,L,\,\mu,\,x_{0}\right)
$$

Then

$$
\left(k + 1\right) \, \left(F\left(x\left(k + 1\right)\right) - F\left(u\right)\right) \le L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x_{0},\,u\right)
$$

## Theorem: `bregmanProximalIterate_tendsto`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L257)

Let $F, h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $v: E\to E$; $L, \mu: \mathbb{R}$; $x_{0}, u: E$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\operatorname{Continuous}(F)\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall x,z,\quad F\left(x\right) + \left\langle v\left(x\right),z - x\right\rangle \le F\left(z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)\\[4pt]\forall z,\quad \nabla h\left(z\right) = \operatorname{dh}\left(z\right)\\[4pt]\forall z,\quad F\left(u\right) \le F\left(z\right)
\end{gathered}
$$

Set

$$
x:=\operatorname{BregmanIterate}\left(F,\,h,\,\operatorname{dh},\,v,\,L,\,\mu,\,x_{0}\right)
$$

Then

$$
\lim_{k\to\infty} F\left(x\left(k\right)\right) = F\left(u\right)
$$

## Theorem: `exists_bregmanProximal_steps`

[Source](../../QuasiNewtonConvergence/BregmanExistence.lean#L273)

Let $F: \mathbb{N}\to E\to \mathbb{R}$; $h: E\to \mathbb{R}$; $\operatorname{dh}: E\to E$; $x, v: \mathbb{N}\to E$; $L, \mu: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
0 < L\\[4pt]0 < \mu\\[4pt]\forall k,\quad \operatorname{Continuous}(F\left(k\right))\\[4pt]\operatorname{Continuous}(h)\\[4pt]\forall k,z,\quad F\left(k,\,x\left(k\right)\right) + \left\langle v\left(k\right),z - x\left(k\right)\right\rangle \le F\left(k,\,z\right)\\[4pt]\operatorname{StrongConvexFirstOrder}\left(h,\,\operatorname{dh},\,\mu\right)
\end{gathered}
$$

Then

$$
\exists z\in \mathbb{N}\to E,\quad \forall k,u,\quad F\left(k,\,z\left(k\right)\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,z\left(k\right)\right) \le F\left(k,\,u\right) + L \, \operatorname{D}\left(h,\,\operatorname{dh},\,x\left(k\right),\,u\right)
$$


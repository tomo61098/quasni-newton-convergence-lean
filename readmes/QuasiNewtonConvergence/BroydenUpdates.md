# BroydenUpdates

Quasi-Newton update formulas.

[Module index and notation](README.md) · [Lean source](../../QuasiNewtonConvergence/BroydenUpdates.lean)

Let $E$ be a real inner product space with its induced norm.

## Definition: `PositiveDefinite`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L18)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$.

Define

$$
\operatorname{PositiveDefinite}\left(B\right) \Longleftrightarrow \forall z\in E,\quad z \ne 0 \Longrightarrow 0 < \left\langle B\left(z\right),z\right\rangle
$$

## Definition: `bfgsUpdate`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L22)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $z: E$.

Define

$$
\operatorname{bfgsUpdate}\left(B,\,s,\,y,\,z\right) := B\left(z\right) - \frac{\left\langle B\left(s\right),z\right\rangle}{\left\langle B\left(s\right),s\right\rangle} \, B\left(s\right) + \frac{\left\langle y,z\right\rangle}{\left\langle y,s\right\rangle} \, y
$$

## Theorem: `bfgsUpdate_secant`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L27)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\left\langle B\left(s\right),s\right\rangle \ne 0\\[4pt]\left\langle y,s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\operatorname{bfgsUpdate}\left(B,\,s,\,y,\,s\right) = y
$$

## Theorem: `bfgsUpdate_secant_of_curvature`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L32)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle
\end{gathered}
$$

Then

$$
\operatorname{bfgsUpdate}\left(B,\,s,\,y,\,s\right) = y
$$

## Definition: `broydenVector`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L38)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{broydenVector}\left(B,\,s,\,y\right) := \frac{1}{\left\langle y,s\right\rangle} \, y - \frac{1}{\left\langle B\left(s\right),s\right\rangle} \, B\left(s\right)
$$

## Definition: `broydenUpdate`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L42)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $\varphi: \mathbb{R}$; $z: E$.

Define

$$
\operatorname{broydenUpdate}\left(B,\,s,\,y,\,\varphi,\,z\right) := \operatorname{bfgsUpdate}\left(B,\,s,\,y,\,z\right) + \varphi \, \left\langle B\left(s\right),s\right\rangle \, \left\langle \operatorname{broydenVector}\left(B,\,s,\,y\right),z\right\rangle \, \operatorname{broydenVector}\left(B,\,s,\,y\right)
$$

## Definition: `dfpUpdate`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L48)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $z: E$.

Define

$$
\operatorname{dfpUpdate}\left(B,\,s,\,y,\,z\right) := \operatorname{broydenUpdate}\left(B,\,s,\,y,\,1,\,z\right)
$$

## Definition: `sr1Update`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L52)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $z: E$.

Define

$$
r:=y-B(s),\qquad
\operatorname{sr1Update}(B,s,y,z)=B(z)+\frac{\langle r,z\rangle}{\langle r,s\rangle}r.
$$

## Definition: `sr1UpdateOrSkip`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L57)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $z: E$.

Define

$$
\operatorname{sr1UpdateOrSkip}\left(B,\,s,\,y,\,z\right) := \begin{cases}B\left(z\right)&\text{if }\left\langle y - B\left(s\right),s\right\rangle = 0\\\operatorname{sr1Update}\left(B,\,s,\,y,\,z\right)&\text{otherwise}\end{cases}
$$

## Definition: `rankOne`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L61)

Let $a, b: E$.

Define

$$
\operatorname{rankOne}(a,b)(z)=\langle a,z\rangle b\quad(z\in E).
$$

## Definition: `bfgsUpdateMap`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L67)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right) := B - \frac{1}{\left\langle B\left(s\right),s\right\rangle} \, \operatorname{rankOne}\left(B\left(s\right),\,B\left(s\right)\right) + \frac{1}{\left\langle y,s\right\rangle} \, \operatorname{rankOne}\left(y,\,y\right)
$$

## Definition: `broydenUpdateMap`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L72)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $\varphi: \mathbb{R}$.

Define

$$
\operatorname{broydenUpdateMap}\left(B,\,s,\,y,\,\varphi\right) := \operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right) + \varphi \, \left\langle B\left(s\right),s\right\rangle \, \operatorname{rankOne}\left(\operatorname{broydenVector}\left(B,\,s,\,y\right),\,\operatorname{broydenVector}\left(B,\,s,\,y\right)\right)
$$

## Definition: `dfpUpdateMap`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L76)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{dfpUpdateMap}\left(B,\,s,\,y\right) := \operatorname{broydenUpdateMap}\left(B,\,s,\,y,\,1\right)
$$

## Definition: `sr1UpdateMap`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L79)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{sr1UpdateMap}\left(B,\,s,\,y\right) := B + \frac{1}{\left\langle y - B\left(s\right),s\right\rangle} \, \operatorname{rankOne}\left(y - B\left(s\right),\,y - B\left(s\right)\right)
$$

## Definition: `sr1UpdateOrSkipMap`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L82)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{sr1UpdateOrSkipMap}\left(B,\,s,\,y\right) := \begin{cases}B&\text{if }\left\langle y - B\left(s\right),s\right\rangle = 0\\\operatorname{sr1UpdateMap}\left(B,\,s,\,y\right)&\text{otherwise}\end{cases}
$$

## Definition: `sr1UpdateSafeguardedMap`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L87)

Let $\rho: \mathbb{R}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{sr1UpdateSafeguardedMap}\left(\rho,\,B,\,s,\,y\right) := \begin{cases}\operatorname{sr1UpdateMap}\left(B,\,s,\,y\right)&\text{if }\rho \, \left\|s\right\| \, \left\|y - B\left(s\right)\right\| \le \left|\left\langle y - B\left(s\right),s\right\rangle\right| \land \left\langle y - B\left(s\right),s\right\rangle \ne 0\\B&\text{otherwise}\end{cases}
$$

## Theorem: `bfgsUpdateMap_apply`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L93)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Then

$$
\operatorname{bfgsUpdateMap}\left(B,\,s,\,y,\,z\right) = \operatorname{bfgsUpdate}\left(B,\,s,\,y,\,z\right)
$$

## Theorem: `broydenUpdateMap_apply`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L97)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $\varphi: \mathbb{R}$; $z: E$.

Then

$$
\operatorname{broydenUpdateMap}\left(B,\,s,\,y,\,\varphi,\,z\right) = \operatorname{broydenUpdate}\left(B,\,s,\,y,\,\varphi,\,z\right)
$$

## Theorem: `dfpUpdateMap_apply`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L101)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Then

$$
\operatorname{dfpUpdateMap}\left(B,\,s,\,y,\,z\right) = \operatorname{dfpUpdate}\left(B,\,s,\,y,\,z\right)
$$

## Theorem: `sr1UpdateMap_apply`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L105)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Then

$$
\operatorname{sr1UpdateMap}\left(B,\,s,\,y,\,z\right) = \operatorname{sr1Update}\left(B,\,s,\,y,\,z\right)
$$

## Theorem: `sr1UpdateOrSkipMap_apply`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L109)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Then

$$
\operatorname{sr1UpdateOrSkipMap}\left(B,\,s,\,y,\,z\right) = \operatorname{sr1UpdateOrSkip}\left(B,\,s,\,y,\,z\right)
$$

## Definition: `HessianUpdateMethod`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L117)

Define

$$
\operatorname{HessianUpdateMethod}=
\{\mathrm{BFGS},\mathrm{DFP}\}\;\sqcup\;
\{\mathrm{SR1}(\rho):\rho\in\mathbb R\}\;\sqcup\;
\{\mathrm{Broyden}(\varphi):\varphi\in\mathbb R\}.
$$

## Definition: `hessianUpdate`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L123)

Let $\operatorname{method}: \operatorname{HessianUpdateMethod}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Define

$$
\operatorname{hessianUpdate}(\operatorname{method},B,s,y)=\begin{cases}
\operatorname{bfgsUpdateMap}(B,s,y)&\operatorname{method}=\mathrm{BFGS},\\
\operatorname{dfpUpdateMap}(B,s,y)&\operatorname{method}=\mathrm{DFP},\\
\operatorname{sr1UpdateSafeguardedMap}(\rho,B,s,y)&\operatorname{method}=\mathrm{SR1}(\rho),\\
\operatorname{broydenUpdateMap}(B,s,y,\varphi)&\operatorname{method}=\mathrm{Broyden}(\varphi).
\end{cases}
$$

## Theorem: `broydenVector_orthogonal`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L131)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\left\langle B\left(s\right),s\right\rangle \ne 0\\[4pt]\left\langle y,s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\left\langle \operatorname{broydenVector}\left(B,\,s,\,y\right),s\right\rangle = 0
$$

## Theorem: `broydenUpdate_secant`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L137)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $\varphi: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\left\langle B\left(s\right),s\right\rangle \ne 0\\[4pt]\left\langle y,s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\operatorname{broydenUpdate}\left(B,\,s,\,y,\,\varphi,\,s\right) = y
$$

## Theorem: `dfpUpdate_secant`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L143)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\left\langle B\left(s\right),s\right\rangle \ne 0\\[4pt]\left\langle y,s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\operatorname{dfpUpdate}\left(B,\,s,\,y,\,s\right) = y
$$

## Theorem: `sr1Update_secant`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L148)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\left\langle y - B\left(s\right),s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\operatorname{sr1Update}\left(B,\,s,\,y,\,s\right) = y
$$

## Theorem: `sr1UpdateOrSkip_secant`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L153)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\left\langle y - B\left(s\right),s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\operatorname{sr1UpdateOrSkip}\left(B,\,s,\,y,\,s\right) = y
$$

## Theorem: `sr1UpdateOrSkip_eq_old`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L158)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Assume all of the following.

$$
\begin{gathered}
\left\langle y - B\left(s\right),s\right\rangle = 0
\end{gathered}
$$

Then

$$
\operatorname{sr1UpdateOrSkip}\left(B,\,s,\,y,\,z\right) = B\left(z\right)
$$

## Theorem: `sr1UpdateSafeguardedMap_secant`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L163)

Let $\rho: \mathbb{R}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\rho \, \left\|s\right\| \, \left\|y - B\left(s\right)\right\| \le \left|\left\langle y - B\left(s\right),s\right\rangle\right| \land \left\langle y - B\left(s\right),s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\operatorname{sr1UpdateSafeguardedMap}\left(\rho,\,B,\,s,\,y,\,s\right) = y
$$

## Theorem: `sr1UpdateSafeguardedMap_skip`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L171)

Let $\rho: \mathbb{R}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\neg\left(\rho \, \left\|s\right\| \, \left\|y - B\left(s\right)\right\| \le \left|\left\langle y - B\left(s\right),s\right\rangle\right| \land \left\langle y - B\left(s\right),s\right\rangle \ne 0\right)
\end{gathered}
$$

Then

$$
\operatorname{sr1UpdateSafeguardedMap}\left(\rho,\,B,\,s,\,y\right) = B
$$

## Definition: `SymmetricHessian`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L179)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$.

Define

$$
\operatorname{SymmetricHessian}\left(B\right) \Longleftrightarrow \forall u,v,\quad \left\langle B\left(u\right),v\right\rangle = \left\langle u,B\left(v\right)\right\rangle
$$

## Theorem: `bfgs_quadratic_identity`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L184)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)\\[4pt]\left\langle B\left(s\right),s\right\rangle \ne 0
\end{gathered}
$$

Then

$$
\left\langle \operatorname{bfgsUpdate}\left(B,\,s,\,y,\,z\right),z\right\rangle = \left\langle B\left(z - \frac{\left\langle B\left(s\right),z\right\rangle}{\left\langle B\left(s\right),s\right\rangle} \, s\right),z - \frac{\left\langle B\left(s\right),z\right\rangle}{\left\langle B\left(s\right),s\right\rangle} \, s\right\rangle + \frac{\left\langle y,z\right\rangle^{2}}{\left\langle y,s\right\rangle}
$$

## Theorem: `bfgsUpdate_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L202)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle\\[4pt]z \ne 0
\end{gathered}
$$

Then

$$
0 < \left\langle \operatorname{bfgsUpdate}\left(B,\,s,\,y,\,z\right),z\right\rangle
$$

## Theorem: `broydenUpdate_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L228)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$; $\varphi: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle\\[4pt]0 \le \varphi\\[4pt]z \ne 0
\end{gathered}
$$

Then

$$
0 < \left\langle \operatorname{broydenUpdate}\left(B,\,s,\,y,\,\varphi,\,z\right),z\right\rangle
$$

## Theorem: `dfpUpdate_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L243)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle\\[4pt]z \ne 0
\end{gathered}
$$

Then

$$
0 < \left\langle \operatorname{dfpUpdate}\left(B,\,s,\,y,\,z\right),z\right\rangle
$$

## Theorem: `bfgsUpdate_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L250)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z, w: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\left\langle \operatorname{bfgsUpdate}\left(B,\,s,\,y,\,z\right),w\right\rangle = \left\langle z,\operatorname{bfgsUpdate}\left(B,\,s,\,y,\,w\right)\right\rangle
$$

## Theorem: `broydenUpdate_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L261)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z, w: E$; $\varphi: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\left\langle \operatorname{broydenUpdate}\left(B,\,s,\,y,\,\varphi,\,z\right),w\right\rangle = \left\langle z,\operatorname{broydenUpdate}\left(B,\,s,\,y,\,\varphi,\,w\right)\right\rangle
$$

## Theorem: `dfpUpdate_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L271)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z, w: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\left\langle \operatorname{dfpUpdate}\left(B,\,s,\,y,\,z\right),w\right\rangle = \left\langle z,\operatorname{dfpUpdate}\left(B,\,s,\,y,\,w\right)\right\rangle
$$

## Theorem: `sr1Update_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L276)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y, z, w: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\left\langle \operatorname{sr1Update}\left(B,\,s,\,y,\,z\right),w\right\rangle = \left\langle z,\operatorname{sr1Update}\left(B,\,s,\,y,\,w\right)\right\rangle
$$

## Theorem: `bfgsUpdateMap_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L284)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle
\end{gathered}
$$

Then

$$
\operatorname{PositiveDefinite}\left(\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right)\right)
$$

## Theorem: `broydenUpdateMap_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L291)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $\varphi: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle\\[4pt]0 \le \varphi
\end{gathered}
$$

Then

$$
\operatorname{PositiveDefinite}\left(\operatorname{broydenUpdateMap}\left(B,\,s,\,y,\,\varphi\right)\right)
$$

## Theorem: `dfpUpdateMap_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L298)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle
\end{gathered}
$$

Then

$$
\operatorname{PositiveDefinite}\left(\operatorname{dfpUpdateMap}\left(B,\,s,\,y\right)\right)
$$

## Theorem: `bfgsUpdateMap_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L305)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\operatorname{SymmetricHessian}\left(\operatorname{bfgsUpdateMap}\left(B,\,s,\,y\right)\right)
$$

## Theorem: `broydenUpdateMap_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L311)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$; $\varphi: \mathbb{R}$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\operatorname{SymmetricHessian}\left(\operatorname{broydenUpdateMap}\left(B,\,s,\,y,\,\varphi\right)\right)
$$

## Theorem: `dfpUpdateMap_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L317)

Let $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\operatorname{SymmetricHessian}\left(\operatorname{dfpUpdateMap}\left(B,\,s,\,y\right)\right)
$$

## Definition: `NonnegativeBroyden`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L325)

Define

$$
\begin{gathered}
\operatorname{NonnegativeBroyden}(\mathrm{BFGS})\Longleftrightarrow\mathrm{true},\\
\operatorname{NonnegativeBroyden}(\mathrm{DFP})\Longleftrightarrow\mathrm{true},\\
\operatorname{NonnegativeBroyden}(\mathrm{SR1}(\rho))\Longleftrightarrow\mathrm{false},\\
\operatorname{NonnegativeBroyden}(\mathrm{Broyden}(\varphi))\Longleftrightarrow0\le\varphi.
\end{gathered}
$$

## Theorem: `hessianUpdate_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L331)

Let $\operatorname{method}: \operatorname{HessianUpdateMethod}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{NonnegativeBroyden}\left(\operatorname{method}\right)\\[4pt]\operatorname{PositiveDefinite}\left(B\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)\\[4pt]s \ne 0\\[4pt]0 < \left\langle y,s\right\rangle
\end{gathered}
$$

Then

$$
\operatorname{PositiveDefinite}\left(\operatorname{hessianUpdate}\left(\operatorname{method},\,B,\,s,\,y\right)\right)
$$

## Theorem: `hessianUpdate_symmetric`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L344)

Let $\operatorname{method}: \operatorname{HessianUpdateMethod}$; $B: \mathcal{L}_{\mathbb{R}}(E,E)$; $s, y: E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{NonnegativeBroyden}\left(\operatorname{method}\right)\\[4pt]\operatorname{SymmetricHessian}\left(B\right)
\end{gathered}
$$

Then

$$
\operatorname{SymmetricHessian}\left(\operatorname{hessianUpdate}\left(\operatorname{method},\,B,\,s,\,y\right)\right)
$$

## Theorem: `broydenSequence_positive`

[Source](../../QuasiNewtonConvergence/BroydenUpdates.lean#L357)

Let $B: \mathbb{N}\to \mathcal{L}_{\mathbb{R}}(E,E)$; $\operatorname{method}: \mathbb{N}\to \operatorname{HessianUpdateMethod}$; $s, y: \mathbb{N}\to E$.

Assume all of the following.

$$
\begin{gathered}
\operatorname{PositiveDefinite}\left(B\left(0\right)\right) \land \operatorname{SymmetricHessian}\left(B\left(0\right)\right)\\[4pt]\forall k,\quad B\left(k + 1\right) = \operatorname{hessianUpdate}\left(\operatorname{method}\left(k\right),\,B\left(k\right),\,s\left(k\right),\,y\left(k\right)\right)\\[4pt]\forall k,\quad \operatorname{NonnegativeBroyden}\left(\operatorname{method}\left(k\right)\right)\\[4pt]\forall k,\quad s\left(k\right) \ne 0\\[4pt]\forall k,\quad 0 < \left\langle y\left(k\right),s\left(k\right)\right\rangle
\end{gathered}
$$

Then

$$
\forall k,\quad \operatorname{PositiveDefinite}\left(B\left(k\right)\right) \land \operatorname{SymmetricHessian}\left(B\left(k\right)\right)
$$


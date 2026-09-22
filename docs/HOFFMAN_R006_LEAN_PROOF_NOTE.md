# A complete Lean proof of the
Euclidean chromatic upper bound

R006 companion  |  F004  |  21 September 2026

Mathematical source: Ilya Hoffman, publication revision R006. This companion presents the complete argument checked in Lean 4.19.0. The article itself is unchanged.

## 1. The result and the separated cores

For every integer d ≥ 2 there is a periodic Borel coloring of real Euclidean space, with no monochromatic pair at distance one, using at most the following number of colors:

$$
K_d=\left\lceil4\left(1+d\log(64d^2+1)\right)\left[b\left(1+\frac{1}{d}\right)\right]^d\right\rceil,\qquad b=\frac{3\sqrt{3}}{2}.
$$

$$
K_d\le(40e+1)d\log d\,b^d,\qquad \limsup_{d\to\infty}\chi(\mathbb{R}^d)^{1/d}\le b.
$$

The proof below uses a translated enclosing ball for the exclusion region. It proves the full main upper bound without the spherical-moment and Poisson-density calculations used in R006.

Fix 0 < η < 1 and set R=(1−η)/2 and h=(1+η)/2, so R+h=1. Take a finite list of points on the torus T=(ℝ/5ℤ)^d and lift it periodically to a set Λ in Euclidean space. Define the inward-offset halfspace by

$$
x\in H_h(p,z)\quad\Longleftrightarrow\quad\langle x-p,z-p\rangle\le\frac{\Vert z-p\Vert^2}{2}-h\Vert z-p\Vert.
$$

$$
C_p=\overline{B}(p,R)\cap\bigcap_{z\in\Lambda\setminus\{p\}}H_h(p,z),\qquad A=\bigcup_{p\in\Lambda}C_p.
$$

Points of one core are at distance at most 2R=1−η. If x belongs to C_p and y belongs to C_z with p≠z, the two halfspace inequalities give

$$
\langle y-x,z-p\rangle\ge 2h\Vert z-p\Vert,\qquad\Vert y-x\Vert\ge2h=1+\eta.
$$

Thus A avoids every distance in (1−η,1+η). The set is periodic. A competing center with distance at least 2(R+h)=2 from p cannot cut the ball of radius R. In particular, nontrivial period copies of a center cannot cut its own core.

Lean: Geometry.core_union_avoids_gap; PeriodicCores.configurationCore_periodic.


<!-- page -->


## 2. The enclosing-ball estimate

Let x=p+v with ||v||≤h. A competing center z excludes x when its halfspace inequality fails. Put t=||z−p||. Then

$$
\langle v,z-p\rangle>\frac{t^2}{2}-ht.
$$

Use the shifted center c=p+(3/2)v. Expanding the square gives the complete geometric estimate:

$$
\Vert z-c\Vert^2=t^2-3\langle v,z-p\rangle+\frac{9}{4}\Vert v\Vert^2
$$

$$
\Vert z-c\Vert^2< -\frac{1}{2}t^2+3ht+\frac{9}{4}\Vert v\Vert^2
$$

$$
-\frac{1}{2}t^2+3ht+\frac{9}{4}\Vert v\Vert^2\le\frac{27}{4}h^2-\frac{1}{2}(t-3h)^2\le\frac{27}{4}h^2.
$$

Consequently every excluding center belongs to the open ball B(c,bh), where b=3√3/2. If v_d denotes the volume of the Euclidean unit ball, the exclusion volume is at most

$$
W\le v_d(bh)^d.
$$

This is the source of the exponential base. The estimate is valid in every real inner-product space; its volume consequence uses the ordinary finite-dimensional Haar scaling law.

## Local balls on the torus

Write π for coordinatewise reduction modulo 5. Every torus point has a canonical representative in (−5/2,5/2]^d. For a radius 0<r<5/2, a Euclidean ball centered at zero lies within this fundamental cube and projects injectively. Its normalized torus measure is

$$
\mu\left(\pi(B(0,r))\right)=\frac{v_dr^d}{5^d}.
$$

Lean proves this identity from the measure-preserving quotient map on a half-open interval and finite product measure. It also proves that each nonzero vector in the kernel of π has Euclidean norm at least 5. No volume-preservation assertion from the manuscript is left as an assumption.

Lean: ExclusionBall.exclusionRegion_subset_ball; Torus.torusBall_volume and torus_kernel_norm.


<!-- page -->


## 3. A finite random-center calculation

Assume R>0, r=bh<5/2 and (3/2)R≤r. The final parameters will satisfy these conditions. Fix a point x. Choose N=n+1 torus centers independently and uniformly. Define

$$
a=\frac{v_dR^d}{5^d},\qquad w=\frac{v_dr^d}{5^d},\qquad n=\left\lfloor\frac{1}{2w}\right\rfloor.
$$

The event E_i(x) says that center i has a lift p_i=x+v_i with ||v_i||<R, and every other sampled center avoids the projection of the ball of radius r centered at

$$
c_i=p_i+\frac{3}{2}(x-p_i)=x-\frac{1}{2}v_i.
$$

Conditional on center i, each other center avoids that projected ball with probability 1−w. A measure-preserving translation of the other coordinates of the product space formalizes this conditional calculation directly, giving

$$
\mathbb{P}(E_i(x))=a(1-w)^n.
$$

The events are pairwise disjoint. If both i and j are within radius R of x, then their selected lifts satisfy

$$
\Vert p_j-c_i\Vert=\Vert v_j+\frac{1}{2}v_i\Vert<\frac{3}{2}R\le r,
$$

which contradicts E_i(x). Therefore their union has probability N a(1−w)^n. Since nw≤1/2, Bernoulli’s inequality gives (1−w)^n≥1−nw≥1/2. Also N≥1/(2w). Hence

$$
\mathbb{P}\left(\bigcup_i E_i(x)\right)\ge\frac{a}{4w}=\frac{1}{4}\left(\frac{R}{r}\right)^d=:\delta>0.
$$

On E_i(x), every lift of every other center is outside the enclosing exclusion ball. All their halfspace constraints therefore hold. Copies of center i are too far away to cut its ball, by the period-length estimate. Thus x belongs to the actual core union A of this configuration. Repeated sampled torus points cause no gap: their mutual exclusion prevents the corresponding survival events.

The lower bound is uniform in x. We only need these events for the finitely many points of a net; no expected-volume interchange or continuous Poisson process is used.

Lean: RandomSurvival.any_survival_lower; TorusRandom.torus_survival_lower; PeriodicCores.survivalEvent_mem_core.


<!-- page -->


## 4. From a finite net to a Borel coloring

For a positive integer q, use all grid indices j_i in {0,…,q} and points with coordinates −5/2+5j_i/q. There are m=(q+1)^d indices. Every Euclidean point x has a grid point z and a period t such that

$$
\Vert x-(z+t)\Vert\le d\frac{5}{q}<\rho.
$$

Indeed, reduce x to the canonical cube and round each coordinate down to the grid. The Euclidean norm of the error is at most the sum of its coordinate errors. Adding back the period gives a global lift of the selected grid point.

Now sample k independent center configurations, where

$$
k=\left\lceil\frac{1+\log m}{\delta}\right\rceil.
$$

For any fixed net point, the probability that all configurations fail is at most (1−δ)^k. The union bound over the m net points gives

$$
\mathbb{P}(\hbox{some net point is uncovered})\le m(1-\delta)^k\le me^{-k\delta}\le e^{-1}<1.
$$

Thus there exist k actual configurations whose core unions A_1,…,A_k together cover the net. Their periodicity covers all period translates of the net. Let U_i be the open ρ-neighborhood of A_i. The U_i cover the entire Euclidean space by the net estimate.

If 2ρ<η, each U_i is unit-distance-free. Otherwise, for points x,y in U_i at distance 1, choose u,v in A_i with ||x−u||<ρ and ||y−v||<ρ. The triangle inequality yields

$$
1-2\rho<\Vert u-v\Vert<1+2\rho,
$$

contradicting the forbidden interval (1−η,1+η) for A_i. Assign each point the least index i for which it belongs to U_i. Each color class is a Borel set, since U_i is open and only finitely many preceding open sets are removed. The assignment respects all periods 5ℤ^d, which contain the real basis 5e_1,…,5e_d.

This proves a coloring of all points, including boundaries. The finite product probability spaces supply existence of the configurations; the first-index rule supplies the Borel and periodic coloring.

Lean: TorusNet.periodic_grid_net; ProbabilityCover.exists_samples_hitting_sets; RandomCover.random_net_coloring; FiniteUpperBound.finite_upper_bound.


<!-- page -->


## 5. The complete upper bound

For d≥2, choose the following exact parameters:

$$
\eta=\frac{1}{2d+1},\quad R=\frac{d}{2d+1},\quad h=\frac{d+1}{2d+1},\quad\rho=\frac{\eta}{4},\quad q=64d^2.
$$

They satisfy 2ρ<η, d(5/q)<ρ, h≤3/5 and bh<5/2. Also (3/2)R≤bh. The probability estimate becomes

$$
\delta^{-1}=4\left[b\left(1+\frac{1}{d}\right)\right]^d\le4e\,b^d.
$$

The final inequality follows by raising 1+1/d≤exp(1/d) to the power d. Because q+1≤128d² and log 2≤log d,

$$
\log(q+1)\le9\log d,\qquad \log m=d\log(q+1)\le9d\log d.
$$

Furthermore d log d≥1 for d≥2: log 2≥1/2 follows from 1−1/x≤log x at x=2. Combining these bounds with the ceiling estimate gives

$$
K_d\le\frac{1+d\log(q+1)}{\delta}+1\le40e\,d\log d\,b^d+1
$$

$$
K_d\le(40e+1)d\log d\,b^d.
$$

Here b≥1 and d log d≥1 absorb the last 1. This proves the explicit finite count stated on page 1 and the entire main periodic Borel coloring theorem.

## The ordinary chromatic number and its exponential base

A proper finite coloring bounds the ordinary chromatic number χ. Lean defines the unit-distance graph using mathlib’s SimpleGraph and proves that its adjacency condition is exactly the sum of squared coordinate differences equal to 1. Its chromatic number is finite for d≥2. With C=40e+1, log d≤d gives

$$
\chi(\mathbb{R}^d)^{1/d}\le\exp\left(\log b+\frac{\log C}{d}+2\frac{\log d}{d}\right).
$$

The right-hand side tends to b, since 1/d and (log d)/d tend to zero. Taking the limit superior proves the stated exponential-base bound. This limit argument is also checked in Lean.

Lean: AsymptoticEstimate.colorBound_eq_explicit and colorBound_le; Main.main_upper_bound; Chromatic.chromatic_root_limsup.


<!-- page -->


## 6. What the formal check establishes

The completed release includes the following unconditional main declarations. Their only dimension condition is d≥2; no density, covering or spherical-moment theorem from the article is assumed.

```text
Hoffman.main_upper_bound : Hoffman.MainUpperBound
Hoffman.main_upper_bound_explicit
Hoffman.colorBound_periodic_borel
Hoffman.chromatic_root_limsup
```

The definition of MainUpperBound quantifies over every integer dimension d≥2 and includes a finite coloring, Borel measurability, properness at unit distance, and a real basis of periods. The graph formulation is checked by unitDistanceGraph_adj_iff_coordinates.

## Recorded verification

A clean build of the project passed with Lean 4.19.0. The axiom audit covers the compiled logical declarations, including the main theorem and the chromatic-number limsup; it also rechecks the theorem proof terms with Lean’s kernel. Only the standard Lean foundations propext, Classical.choice and Quot.sound occur. No sorry, admit, custom axiom, unsafe declaration or native_decide is used in the project proof modules.

```text
Lean:    4.19.0
mathlib: c44e0c8ee63ca166450922a373c7409c5d26b00b

python3 scripts/fetch_cache.py
bash verify.sh
```

The first command retrieves the pinned dependencies and the cache for their actual mathlib imports. The verification script checks versions, clears the project build, recompiles the source and audits the compiled declarations. Compiler binaries and mathlib are not bundled. The archive contains the source, dependency lockfile, build logs, axiom reports and the original R006 publication archive.

## Precise scope relative to R006

The principal upper-bound theorem and its limit-superior consequence are fully proved. The enclosing-ball route gives its own explicit finite bound K_d. It does not establish all of the sharper finite prefactors, the exact spherical-moment identities, or the appendix’s optimization of the Poisson expected density. Those refinements are not premises of the completed proof.

The proof is an existence proof using classical choice. It does not claim an efficient procedure for finding the random configurations or evaluating a coloring. The R006 article and its AI disclosure are preserved without edits.

The Lean companion and this explanatory note were prepared with OpenAI Codex. The original publication archive is identified by its full SHA-256 in README.md and verification/BUILD_INFO.json. See BLUEPRINT.md for the module-by-module correspondence.

# F004 proof map

The complete dependency chain reaches `Hoffman.main_upper_bound : MainUpperBound` and `Hoffman.chromatic_root_limsup`. No hypothesis asserting a missing manuscript theorem remains in either conclusion.

| Mathematical step | Lean module and key declaration | Status |
|---|---|---|
| Euclidean space, proper coloring, Borel structure and a basis of periods | `Targets`: `PeriodicBorelColoring`, `MainUpperBound` | Definitions, discharged in `Main` |
| Inward-offset Voronoi cores avoid the interval `(1−η,1+η)` | `Geometry`: `core_union_avoids_gap` | Proved |
| The exclusion region is in a shifted ball of radius `(3√3/2)h` | `ExclusionBall`: `exclusionRegion_subset_ball` | Proved |
| Haar-volume bound for the enclosing ball | `ExclusionVolume`: `exclusionRegion_volume_le` | Proved |
| Finite independent sampling covers finitely many events | `ProbabilityCover`: `exists_samples_hitting_sets` | Proved using product measure and union bound |
| Exact survival mass and its lower bound | `RandomSurvival`: `any_survival_measure`, `any_survival_lower` | Proved |
| Survival implies membership in an actual periodic core | `PeriodicCores`: `survivalEvent_mem_core` | Proved, including periodic copies |
| Uniform torus probability, local ball measure, period separation | `Torus`: `torusBall_volume`, `torusBall_probability`, `torus_kernel_norm` | Proved |
| Pointwise coverage probability at least `(1/4)(R/r)^d` | `TorusRandom`: `torus_survival_lower` | Proved |
| Finite grid with global lifts and full-rank periods | `TorusNet`: `periodic_grid_net`, `periodBasis_projection` | Proved |
| Open neighborhoods and first-color selection | `Net`, `PeriodicCover`, `RandomCover` | Proved; no measurability of arbitrary random core unions is assumed |
| Concrete finite-dimensional periodic Borel coloring | `FiniteUpperBound`: `finite_upper_bound` | Proved |
| Explicit count `K_d` and the universal prefactor | `AsymptoticEstimate`: `colorBound_eq_explicit`, `colorBound_le` | Proved |
| Entire main upper-bound statement | `Main`: `main_upper_bound` | Proved |
| Ordinary graph chromatic number and d-th-root limsup | `Chromatic`: `ordinary_chromaticNumber_le`, `chromatic_root_limsup` | Proved |

## Difference from the paper's proof

R006 computes the exclusion volume by spherical integration and uses a Poisson mixture to obtain expected density. The formal main proof bounds that region by a translated ball and samples a fixed finite number of centers. Disjoint survival events give a uniform coverage probability for each point of the net. A second finite product probability space supplies finitely many core unions covering that net. Small open neighborhoods then produce the coloring.

The parameter choice is `η=1/(2d+1)`, `ρ=η/4`, `q=64d²`, with `(q+1)^d` grid indices. These parameters give the same main exponential base and polynomial factor as Theorem 1, with the explicitly proved constant `40e+1`. They do not claim the sharper finite prefactors printed elsewhere in R006.

## Other checked source components

`Planar.lean` verifies the scalar maximum associated with `3√3/2`; it does not define polygon area as Lebesgue measure. `MomentPolynomial.lean` verifies properties of the printed coefficient polynomial; its identification with a spherical integral is not part of the completed proof. `PoissonSeries.lean` verifies the scalar Poisson-series identities; it is not a formal Poisson-process construction.

The exact spherical-moment identity, refined finite bounds involving `M_d`, and the appendix's optimal expected-density constant remain outside the fully checked scope. Their absence creates no gap in the main theorem, whose proof does not depend on them.

## Additional semantic audit

`Semantics.main_upper_bound_coordinates` exposes Borel fibers, the sum-of-squares unit-distance condition, positive finite color count and periodicity under every integer combination of the basis. `Semantics.ordinary_chromatic_value_exact` identifies `chromaticReal` with the finite minimum ordinary number of colors. Both are consequences of the original F003 result.

# Main results A–F

[← Project overview](../README.md)

The public interface follows the manuscript order. All declarations below live
in the `ConditionedStableLaws` namespace. Import
`ConditionedStableLaws.MainResults` for the full interface, or import a single
`ConditionedStableLaws.TheoremX` module for one letter.

## Theorem A · Poisson point processes

`TheoremA` combines vague convergence of the normalized empirical point measures,
joint convergence of every finite disjoint interval-count vector, and the Poisson
random-measure characterization of the limit.

- `TheoremA.pointProcess` — the vague point-process limit.
- `TheoremA.intervalCounts` — joint interval-count convergence.
- `TheoremA.poissonLaw` — Poisson counts and independence of the limit.

## Theorem B · Stable and Gaussian laws

`TheoremB` combines the four conditional limit regimes of the singular observable.
The companion declarations give the law formulas and stability identifications.

- `TheoremB.part_i` — 0 < α < 1, without centering.
- `TheoremB.part_ii` — α = 1, with truncated-mean centering.
- `TheoremB.part_iii` — 1 < α < 2, with full-mean centering.
- `TheoremB.part_iv` — α = 2, with √(C n log n) normalization.
- `TheoremB.laplace_i` — the Laplace transform in part (i).
- `TheoremB.characteristic_ii`, `TheoremB.characteristic_iii` — the characteristic functions.
- `TheoremB.stable_i`, `TheoremB.stable_ii`, `TheoremB.stable_iii` — the stable-law identifications.

## Theorem C · Conditional central limit theorem

`TheoremC` gives the L²(μ) conditional CLT, absolute convergence of the covariance
series and nonnegativity of its asymptotic variance, for every live initial state.
The zero-variance case is included.

## Theorem D · Exponential concentration

`TheoremD` gives the deviation bound Cₓ exp(−aₕ ε² n), with aₕ > 0 independent
of the initial state, ε and n. The prefactor may depend on the initial state.

- `TheoremD.explicitRate` — the min{tₕ/4, ε²/(16 Kₕ)} rate form.

## Theorem E · Shrinking-target Poisson law

`TheoremE` gives the Poisson limit for the number of visits to measurable shrinking
neighborhoods, with the initial point distinct from the target center.
The nonnegative-parameter statement includes the positive-parameter case of the paper.

## Theorem F · Refined laws of large numbers

`TheoremF` combines the three refined conditional LLN statements.

- `TheoremF.part_i` — bounded observables, conditional L¹ convergence, every live initial state.
- `TheoremF.part_ii` — L¹(μ) observables vanishing on Z, conditional L¹ convergence, ν-almost every initial state.
- `TheoremF.part_iii` — L¹(ν) observables vanishing on Z, conditional probability convergence, ν-almost every initial state.

## Mathematical interface

The proofs use the actual canonical survival-conditioned law, sums over
0,…,n−1 and conditioning on τ > n. Hypothesis H produces the normalized
spectral data through `HypothesisH.exists_eigenData_survivalGap`; these data
are explicit parameters of the public theorems, not independent assumptions
of a spectral gap or a limit law.

The public wrappers do not change the implementation theorems. In particular,
`TheoremF.part_iii` preserves the original arbitrary-left-eigenmeasure signature.
The aggregate `TheoremF` uses the probability eigenmeasure from the manuscript,
which is the common input to parts (i) and (ii).

Changing the normalization at n = 0 is an explicit totalization convention and
does not affect any limiting assertion. No transport theorem from an arbitrary
filtered realization to the canonical path law is claimed here.

## Compatibility and auditing

Original implementation names remain available. The aggregate theorems and
all public companion declarations are checked by `AuditMainTheorems.lean`;
the source inventory also maps the new names alongside the original names.
Only the standard classical foundations are allowed for A–F.

# Development and proof coverage

[← Project overview](../README.md)

The public theorem interface is documented in [Main results](MainResults.md).
This document retains the detailed implementation and coverage reference.

**Status: main results A–F and all nine remarks proved; whole-paper coverage incomplete.**

The scope is the external manuscript snapshot identified in `coverage.json`,
excluding the five examples at the user's explicit request.
Of the 23 theorem, lemma and proposition statements in the current inventory,
21 are proved, one is proved modulo a registered cited axiom, and one is partial:
the general compact-interpolation theorem (`thm:compact-interpolation`). Its
finite-measure real `L¹`–`L∞` midpoint instance, which is the only instance
used by the article, is now proved in `LpCompactInterpolation.lean` without
cited axioms. The proved results include
all four parts of `thm:main-stable-laws` (with the stable limits identified by
the proved scaling identity, and the Gaussian boundary case α = 2), the L² CLT, the
bounded CLT (deduced from the triangular-array lemma as in the manuscript),
exponential concentration, `lem:mix` for signed observables, and the
`Q`-process definition. All nine remarks are proved without cited axioms,
with the precise interpretations described below. The five examples are
outside the requested scope.

**Manuscript snapshot.** The inventory (`coverage.json`, line ranges and
labels) records `main.tex` (SHA-256 `02e95e900bea…`) and `appendix.tex`
(`a8365c9a3912…`). These external files are not bundled in this repository.

All main results A–F, including all three refined conditional LLN parts,
are proved without cited axioms. Only `thm:Qprocess` remains proved modulo a
cited axiom for its stationary-path ergodicity conclusion. The Lean modules also include definitions and
supporting infrastructure. Lean's declaration count includes generated helpers
and is not a count of manuscript results.

## Remarks

The focused import is `ConditionedStableLaws.Remarks`. The exact source spans,
declaration names, and scope notes are recorded in `coverage.json`.

| Manuscript remark | Proof entry points |
| --- | --- |
| Birkhoff indexing | `EndpointReindexing.lean`, `EndpointMeanReindexing.lean`: both bounded estimates, endpoint control from H, and the shifted/inclusive conditional mean LLNs. |
| No killing | `ConservativeCase.lean`: conditioning has no effect, the normalized weight is one, and the two invariant measures coincide. |
| Admissibility | `RiemannianRegularityRemark.lean`, `AdmissibleRiemannian.lean`: interior volume regularity, almost-everywhere absolute-error differentiation, and admissibility of continuous positive densities. |
| Independent limiting counts | `RemarkConsequences.lean`, `FiniteCountRemark.lean`, `SingularFiniteCountExample.lean`: independent Poisson limits, an H-chain with dependent actual singular-observable interval counts, and independence of deterministic initial counts. `FiniteCountConcrete.lean` also gives an unconditional three-state witness. |
| Continuous multipliers | `ContinuousMultiplierLimits.lean`: `stable_law_small_signed`, `stable_law_one_signed`, `stable_law_mid_signed`, `stable_law_boundary_signed`. |
| Starting at the target | `PoissonTargetStart.lean`: the positive-time count converges to Poisson, and starting at the target adds exactly one. |
| Integrability with respect to μ and ν | `WeightedLp.lean`, `RemarkConsequences.lean`: inclusion, equivalent norms under a lower weight bound, and the corresponding conditional LLNs. |
| Canonical Q-process | `RemarkConsequences.lean`: existence from H and probability one of staying in the surviving set at every time simultaneously. |
| Random-measure semiring | `VagueConvergence.lean`, `IntervalRefinement.lean`: the interval semiring and random-measure convergence implication. |

The multiplier proofs cover all four regimes, use exactly `|g(x₀)|Bₙ`, and
allow any fixed finite value at the singularity. At α=1 the centering is
the integral truncated by the absolute value of the signed observable.
Negative `g(x₀)` reflects the stable limits and preserves the centered Gaussian.

For Riemannian volume, `HasRiemannianVolumeDensity` specifies the usual local
coordinate identity with density `sqrt(det g)`, using the actual metric tensor.
The ball-volume asymptotic, local finiteness, and differentiation are proved
from that identity. The construction of a global canonical Riemannian volume
measure is not asserted. The ambient manifold can be noncompact and the
measurable domain need not have a null boundary.

Two points in the prose need precise interpretation. Finite counts **need not
be independent**; a universal assertion that they are dependent is false for
deterministic or zero counts. The integrability remark explicitly leaves its
general `L¹(ν)` conditional-mean question open, so no theorem asserts an answer
to that question. The vanishing-weight counterexample is a weighted-measure
example, not a construction of a chain satisfying H.

The finite-count existence claim is proved directly. The refresh chain draws
from the reference probability at every positive time; `FiniteCountExample.lean`
verifies all of H and the stationary measure identity. Given the paper's local
regularity assumption, `refresh_hypothesisH_and_singular_two_counts_dependent`
constructs two disjoint positive-endpoint intervals whose actual `N₂` counts
are dependent, with a positive arbitrary normalization (including the paper's
`B₂`). The targets' positive probabilities are derived from regularity.

To check the remark declarations and reject cited axioms in all nine items:

```sh
python3 scripts/check.py --require-remarks
```

Add `--require-manuscript --manuscript-dir /path/to/source` to verify both
external source hashes as well.

## Checked results

- **Conditional stable law for 0 < α < 1** (`thm:main-stable-laws` (i)):
  `StableLawSmall.stable_law_small` proves, for every initial state in M∖Z,
  convergence in distribution of the normalized Birkhoff sums of `f_β` to
  `∫ y N(dy)`, whose Laplace transform `exp(-Γ(1-α)tᵅ)` is proved in
  `PositiveStableLaw.lean`. No cited axiom is used.
- **Conditional stable laws for α = 1 and 1 < α < 2** (`thm:main-stable-laws`
  (ii)–(iii)): `StableLawCompensated.stable_law_one` and `stable_law_mid` prove
  `B_n⁻¹(Σ f_β(X_j) - A_n) → Z₁` and `B_n⁻¹(Σ f_β(X_j) - nν(f_β)) → Z_α`, with
  the characteristic functions in `CompensatedStableLaw.lean`. The compensated
  small jumps use `lem:conditional-second-moment` and the proved midpoint
  interpolation estimate in `LpMidpointInterpolation.lean`.
- **L² compactness** (`lem:l2-compactness`) is proved without cited axioms.
  `LpCompactInterpolation.midpoint_compact_interpolation` transfers compactness
  from `L∞` to `L²` for compatible finite-measure `L¹`, `L²`, and `L∞` operators,
  using finite conditional expectations and the proved midpoint norm estimate.
  `L2Compactness.lean` applies it directly to the actual kernel remainder.
- **Refined conditional laws of large numbers**: all three parts are proved
  without cited axioms. Part (ii) uses the Hopf maximal inequality and L1
  Cesàro closure (`KernelMaximal.lean`, `KernelCesaro.lean`,
  `QProcessCesaro.lean`, `RefinedLLNMean.lean`). Part (iii), in
  `RefinedLLNProbability.lean`, uses the L1(nu) Q-process mean LLN,
  truncation and the proved **transfer theorem** (`thm:conditional-transfer`).
  `DoobHistoryChange.lean`, `QProcessEndpoint.lean` and
  `KilledLiveTransfer.lean` establish the finite-history identity and uniform
  integrability of the inverse terminal weight required by
  `WeightedProbabilityTransfer.lean`. `QProcessReference.lean` preserves the
  original arbitrary-left-eigenmeasure signature; no probability hypothesis
  is added to F(iii).
- **Conditional CLT for bounded observables** (`thm:conditional-clt-bounded`):
  `ConditionalCLT.conditional_clt_bounded` (`BoundedCLT.lean`; absolute
  convergence of the variance series, `σ² ≥ 0`, Gaussian limit), deduced as in
  the manuscript from the triangular-array lemma with `g_n = ḡ`, `a_n = √n`.
- **Conditional CLT for L² observables** (`thm:conditional-clt-l2`):
  `L2Variance.conditional_clt_l2` (`L2CLT.lean`), via truncation, the
  conditional second-moment estimate and the conditioned large-observation
  estimate `L2Variance.large_observation_tendsto_zero`.
- **Gaussian boundary case** (`thm:main-stable-laws` (iv)):
  `GaussianBoundary.stable_law_boundary`: `f_β ∈ L¹(ν)` and
  `B_n⁻¹(Σ f_β(X_j) - nν(f_β)) → 𝒩(0,1)` with `B_n = √(C n log n)`.
- **Stable limits** (`thm:main-stable-laws` (i)–(iii)): identified as α-stable
  laws without cited axioms. `StableScaling.lean` scales the explicit
  power-density characteristic exponent, compensates the finite interval
  between the unit cutoff and the scaled cutoff, and proves the independent-sum
  stability identity. The same proof handles α = 1 and arbitrary real drift;
  no general Lévy–Khintchine representation theorem is required.
- **Bounded conditional L¹ LLN** (`thm:refined-conditional-lln` (i)):
  `RefinedLLN.lln_bounded` now follows directly from the proved conditional
  exponential concentration theorem and bounded convergence for changing
  measures. It uses no cited ergodic or transfer theorem and allows nonzero
  observables on the escaping set. The two unbounded parts are also proved
  without cited results, under their original vanishing-on-Z hypotheses.
- **Mixing of all orders** (`lem:mix`): `MixingAllOrders.mixing_all_orders`, for
  bounded measurable observables of any sign, without cited axioms.
- **Conditional triangular-array CLT** (`lem:conditional-triangular-clt`):
  `TriangularCLT.conditional_triangular_clt`. Steps 1–2 (the eigenvalue
  expansion, `TriangularExpansion.eigenvalue_expansion`) are proved without
  cited axioms in `L²(μ)` through the embedding of `L∞(ρ)` (`L2Bridge.lean`); the
  uniform perturbed eigen-data come from the proved real perturbation theorem
  `OperatorPerturbation.stability_of_rank_one_gap`.
- **Conditional exponential concentration** (`thm:conditional-exponential-concentration`):
  `Concentration.conditional_exponential_concentration`, with the manuscript's
  rate `γ(ε,f) = min{t_f/4, ε²/(16K_f)}`, via Feynman–Kac, twisted operators on
  `L∞(ρ)` (`TwistedOperators.lean`) and the proved perturbation theorem; the
  second-order bound `|Λ(t) - 1| = O(t²)` is derived from the eigenrelation.
- **Conditional second moment of Birkhoff sums**
  (`lem:conditional-sum-second-moment`): `SecondMoment.conditional_sum_second_moment`
  proves `E_x[(Σ_{i<n} g(Xᵢ))² | τ>n] ≤ Cₓ(n μ(g²) + G²)` for bounded `g` with
  `ν(g)=0`, via the Feynman–Kac word expansion (`FeynmanKac.lean`) and the L²
  decay of `lem:l2-compactness`, using the proved midpoint interpolation estimate.
  `SmallJumpMoment.conditional_small_jump_second_moment_singular` derives the
  compensated small-jump bound `lem:conditional-second-moment` for `f_β`.

- **Spectral and quasi-ergodic theorems** (`thm:Castro`, `thm:spectralgap`):
  all source clauses now follow from H, including the unique quasi-stationary
  and quasi-ergodic probabilities, actual spectral radius, exponential L∞
  remainder, exact projection identities, eigenfunction support, density,
  and conditioned averages of every bounded measurable observable.
  The separate L² operators are constructed directly; their decay and
  compactness use the proved finite-measure real midpoint interpolation theorems.
- **Conditional Poisson theorems** (`thm:ppp`, `thm:conditional-poisson`):
  `ChainPoissonProcess.lean` proves actual conditioned vague convergence and
  joint disjoint-interval counts from H and admissibility.
  `ShrinkingTargetPoisson.lean` proves the actual scalar visit-count limit
  from shrinking neighborhoods and the prescribed rate. All required chain
  estimates, normalization, and endpoint removal are proved.
- **Tail-asymptotics proposition** (`thm:tail-asymptotics`):
  `LocalDensity.lean` and `Tails.lean` derive the weighted small-ball asymptotic,
  singleton nullity, exact superlevel sets, the power tail, and its normalized
  limit. The final theorem constructs the weighted measure using `withDensity`.
  It assumes the manuscript's explicit density/admissibility data; the earlier
  spectral construction now produces the normalized eigen-data from H;
  regularity and admissibility remain the manuscript's local assumptions.
- **Method of moments** (`thm:methodofmoments`): `MethodOfMoments.lean`
  proves the full real-valued criterion, deriving tightness and moment transfer
  and identifying subsequential limits from genuine moment determinacy.
  It includes the random-variable formulation with changing underlying laws.
- **Cramér–Wold** (`thm:cramerwold`): `WeakConvergence.lean` proves the coordinate
  criterion, including changing underlying probability measures. It uses
  mathlib's verified characteristic-function and Lévy convergence results.
- **Kallenberg random-measure criterion** (`thm:kallenberg-random-measures`):
  `VagueConvergence.lean`, `RandomMeasureConvergence.lean`, and
  `IntervalRefinement.lean` derive weak convergence in the actual vague topology
  from joint count convergence on disjoint intervals, including changing
  probability spaces. The proof includes the deterministic interval criterion,
  measurable count maps, count cylinders, and finite disjoint refinement.
- **Uniform-small-target arguments**:
  `SmallTargets.lean` proves uniform absolute continuity using a compact L¹
  family and a finite net. `KernelSmallTargets.lean` states the conclusion for
  actual transition probabilities. `QuasiErgodicSmallTargets.lean` proves the
  second argument from explicit eigenmeasure/eigenfunction data, including
  the required absolute continuity. `EigenfunctionSupport.lean` derives
  positivity exactly on the nonescaping set and the eigenmeasure support
  inclusion from H2. Normalized eigen-data now exist directly from H.
- **Compactness, strong Feller, positivity, and spectral algebra**:
  `StrongFeller.lean` constructs the actual integral operator, proves its
  compactness by Arzelà–Ascoli and identifies it with killed-kernel integration.
  `SpectralAlgebra.lean` proves projection idempotence,
  remainder annihilation and the positive-power decomposition from normalized
  left/right eigenvector identities. `CompactSpectral.lean` proves contraction
  and extracts continuous eigenfunctions from nonzero spectral points or
  positive approximate eigenvectors. `NonEscapingOpen.lean` and
  `FiniteReturnMinorization.lean` prove openness of the nonescaping set and a
  positive finite-power minorization directly from H. `OperatorGrowth.lean`,
  `PositiveResolvent.lean`, `PositiveEigenpair.lean`, and
  `PositiveEigenmeasure.lean` construct positive right and left eigenvectors
  at the same positive rate. `EigenmeasurePositivity.lean` proves their pairing
  is positive using Fredholm on the escaping restriction.
  `NormalizedEigenData.lean` derives normalization, quasi-stationary existence
  with reference density, and uniqueness of the quasi-stationary rate.
  `PeripheralCyclic.lean`, `KernelSpectralGap.lean`, and
  `HypothesisSpectralGap.lean` prove spectral simplicity and the exponential
  gap from H. `SpectralRadiusIdentification.lean` identifies the rate with
  the actual spectral radius. `ConditionedCesaro.lean` and `QuasiErgodic.lean`
  prove the conditioned bounded Birkhoff limits and quasi-ergodic uniqueness.
- **Doob transform**: `DoobTransform.lean` constructs the Markov kernel on the
  positive-eigenfunction set, proves the full power formula, and proves
  invariance of the weighted eigenmeasure. `QProcessLimit.lean` constructs
  its actual canonical path law and proves exact cylinder formulas.
  `SpectralSurvival.lean` derives uniform normalized survival convergence and
  the canonical Q-process limit from a gap for the actual transition operator.
  The stationary Doob probability is now constructed from H; stationary
  ergodicity remains unfinished; the required exponential gap is now proved.
- **Quantitative mixing mechanism**: `ConditionalMixing.lean` proves exact
  telescoping, all-orders operator bounds and rank-one factorization.
  `KernelMixing.lean` identifies these with genuine nested killed-kernel
  integrals at each state. `PathMixing.lean` connects them to actual multitime
  conditioned-path expectations and event probabilities. Its mixing corollary
  covers nonnegative bounded observations, including rare-event indicators;
  the spectral gap is explicit input. `StationaryClusters.lean` identifies
  actual stationary cluster probabilities and proves the uniform cluster
  error bound, including small gaps and the original time convention.
- **Random point measures and counting**: `PointMeasures.lean` constructs the
  actual vague point-measure space on `(0,∞]`; `PoissonRandomMeasure.lean`
  defines Poisson random measures with genuine count laws and independence.
  `EmpiricalPaths.lean` constructs the paper's empirical observations on
  canonical killed paths and identifies their tail counts under conditioning.
  `PowerIntensity.lean` constructs the power-law intensity with exact tails,
  interval masses, atomlessness, and local finiteness. `FactorialMoments.lean`
  proves the injective-selection factorial identities and configuration counts.
  `RareEventMoments.lean` proves exact expectation identities and mixed moment
  convergence from explicit good-configuration and excluded-configuration
  estimates, including endpoint strips. `PoissonConvergence.lean` and
  `MultivariatePoissonConvergence.lean` derive the univariate and independent
  multivariate Poisson limits by finite inclusion-exclusion.
  `RareEventPoisson.lean` assembles these for actual measurable visit counts;
  `RareTargetNormalization.lean` identifies interval rates with the intensity
  and derives uniform kernel smallness for singular-observation targets.
  `PoissonExistence.lean` proves existence for every intensity finite on
  positive tails by superposing independent finite clouds on shrinking
  annuli. Local finiteness, measurable superposition, all finite-intensity
  count laws, and disjoint independence are proved. The chain-specific
  excluded-configuration estimates and their final assembly are now proved
  in `ChainConfigurationBounds.lean`, `HypothesisConfigurationBounds.lean`,
  and `ChainPoissonProcess.lean`.
  The general random-measure convergence criterion is proved.
- **Gaussian covariance mechanism**: `CompactWeakConvergence.lean`,
  `L2WeakConvergence.lean`, and `CovarianceSeries.lean` prove weak convergence
  from L² boundedness and almost-everywhere convergence, the compact-operator
  improvement, and vanishing of the full covariance series under an explicit
  exponential operator bound. `TruncatedMoments.lean` and
  `TruncatedAsymptotics.lean` derive the exact layer-cake identity and the
  power/logarithmic second-moment asymptotics from the original tail ratio,
  without assuming integrability of the untruncated square.
- **Stable-law centering ingredients**: `FirstMoments.lean` proves exact
  truncated first moments and their power/logarithmic asymptotics, and derives
  integrability above tail exponent one. `PositiveStableLaw.lean` proves the
  positive Poisson integral's finiteness and exact Gamma-normalized Laplace
  transform. `CompensatedSeries.lean`, `CompensatedPoissonIntegral.lean`, and
  `CompensatedCharacteristic.lean` construct the compensated L² integral from
  actual independent clouds and prove its characteristic function and
  intensity isometry. `PowerCompensation.lean` supplies the exact small-jump
  variance and probability bound for all 0<α<2. `StableLawSmall.lean` and
  `StableLawCompensated.lean` use these ingredients to prove conditional
  stable-law convergence in all three stable regimes.
- **Removing approximations**: `ConvergingTogether.lean` proves Slutsky and
  the two-stage converging-together argument for changing probability laws,
  with quantitative bounded-Lipschitz estimates. `SmallJumpMoment.lean`,
  `CompensatedPoissonLimits.lean`, and the stable-law modules supply the
  truncation estimates and limiting distributions used by Theorem B.
- **Birkhoff sums and elementary probability limits**: `Birkhoff.lean` checks
  centering, endpoint changes, stopped sums and normalized finite prefixes.
  `BoundedConvergence.lean` proves bounded convergence in mean from convergence
  in probability under changing measures, together with the Markov converse.
- **Quasi-stationary marginals**: `QuasiStationary.lean` proves the equivalence
  between the eigenmeasure identity and invariance of normalized surviving
  marginals under all positive kernel powers. It does not prove existence or
  uniqueness of the eigenmeasure; existence from H is supplied separately by
  `NormalizedEigenData.lean`.
- **Shrinking targets**: `ShrinkingTargets.lean` checks the definition,
  eventual exclusion of other initial points, and vanishing target mass and
  singleton mass under the prescribed visit-rate scaling.
- **Weights and conservative chains**: `WeightedLp.lean` proves the Lp
  inclusions and norm comparisons for bounded weights and the converse with
  a positive lower bound, with a counterexample when that bound is absent.
  `ConservativeCase.lean` proves equality of conditioned and original path
  laws without killing, and unit spectral weight/rate from normalized data.

`StandingHypothesis.lean` defines the killed kernel and Hypothesis H without
assuming spectral or limit-law conclusions. `CanonicalChain.lean` constructs
actual path laws with Ionescu–Tulcea, checks the initial marginal, and defines
survival conditioning and measurable path sums. `CemeteryBridge.lean` connects
the one-step canonical transition to its killed kernel and verifies the
live/cemetery mass split. `PathSurvival.lean` now proves the all-time bridge:
killed powers are the live endpoint marginals, survival is almost surely
equivalent to a live endpoint, and conditional endpoint laws are normalized
killed powers. No such identity is assumed in the path construction.

## Build and verify

Lean and mathlib are pinned to **v4.35.0**; `lake-manifest.json` fixes mathlib
at commit `56a005855ea17e0b0958f73ec801ae140b0a1679` and pins all dependencies.

From the repository root:

```sh
python3 scripts/check.py
```

The script uses the project-local installation at `.tools/elan` when present,
otherwise the `lake` on your PATH. On a fresh machine with Lean installed, run
`lake update` to fetch dependencies and their compiled cache first.
See [Lean installation instructions](https://lean-lang.org/install/manual/).

The checker builds the umbrella module, audits every declaration in the
`ConditionedStableLaws` namespace, and checks the manuscript hashes when the
external sources are available. `--require-manuscript` requires those files;
ordinary proof verification does not depend on them. The
permitted axioms are `propext`, `Classical.choice`, `Quot.sound`, and the
registered **cited results** described below. `sorryAx` and any unregistered
project axiom fail verification. Declarations mapped in the coverage file are
also checked against the built Lean environment, and the checker confirms
that each item's recorded `citedAxioms` are exactly the cited axioms its
declarations depend on.

`AuditMainTheorems.lean`, also run by the checker, requires all declarations
mapped to all main results A–F to use only `propext`, `Classical.choice`,
and `Quot.sound`. The labels follow the order of the six `maintheorem`
environments. This includes F(iii) and its probability-transfer theorem.

### Cited results stated as axioms

Results that the manuscript quotes from the literature without proof are
stated as axioms in `ConditionedStableLaws/Cited/`, registered in
`Audit.lean` and in `coverage.json` (`citedAxioms`):

| Axiom | Cited result |
|---|---|
| `castro_qProcess_stationary_ergodic` | Castro et al. Prop. 2.6(iii) (`thm:Qprocess`) |

The former Birkhoff and conditional-transfer axioms have been removed.
Neither is needed by A–F. The remaining stationary-path ergodicity axiom
belongs to the separate Q-process theorem, not the main limit laws.

Other cited results need no axiom: Castro–Lamb–Olicón-Méndez–Rasmussen
Theorems A–C, Billingsley's method of moments and Cramér–Wold, Kallenberg's
random-measure criterion, the Poisson Laplace functional, Slutsky and
converging-together, Hewitt–Stromberg (for L²), the rank-one perturbation
theorem replacing the former Kato axiom, and Toeplitz's lemma are proved in this
project; the required real `L¹`–`L∞` midpoint norm estimate is proved from
Hadamard's three-lines theorem, and its finite-measure compactness counterpart
is proved using finite conditional expectations. The general Bennett–Sharpley
theorem for arbitrary exponents is not claimed as proved or assumed as an
axiom. Lévy's continuity theorem is in mathlib.

Coverage status `cited_axiom` marks a quoted theorem stated as an axiom;
`proved_modulo_cited` marks a manuscript result proved from H and the listed
cited axioms only. `python3 scripts/check.py --require-axiom-free` exits with
status 3 while any item relies on a cited axiom.

To require actual whole-paper coverage as well:

```sh
python3 scripts/check.py --require-complete
```

This currently exits with status **2** after successful proof checks, because
manuscript coverage is incomplete. A successful ordinary build certifies only
the declarations included in the umbrella module.

## Coverage and remaining work

`coverage.json` tracks 65 source items: theorem/lemma/proposition statements,
definitions, the standing hypothesis, examples, substantive remarks, and proof
steps. Each has a source span and a separate status; a fragment never marks its
parent theorem proved. Of these, 60 items are in scope and the five examples
are marked `excluded`; they do not count as pending work or block the
completion check. The inventory is kept in `coverage.json` without the manuscript.
This inventory is a guide to the remaining work,
not a set of Lean theorem declarations for the missing results.

The main remaining work is the separate stationary Q-process ergodicity
conclusion and the general compact-interpolation statement. No remark remains
partial, and no item is marked `not_formalized`. The standalone
Keller–Liverani theorem would also need a proof if included in the active
dependency graph; the main results do not depend on it.

A source search of the pinned mathlib found Cramér–Wold, the ordinary CLT,
Poisson distributions and compact-operator/Fredholm theory. It did not identify
ready-made theorems matching the paper's Poisson random-measure, stable-law,
or Keller–Liverani dependencies; those searches are not a proof that no useful
library components exist.

Example verification is outside the requested scope. Source-audit notes and
the manuscript are intentionally excluded from this Lean-only distribution.

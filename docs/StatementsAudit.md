# Statement audit

This document compares Theorems A–F and the nine remarks of
[*Conditional Stable Laws and Rare-Event Limits for Absorbing Markov Chains*](https://arxiv.org/abs/2609.22499)
with their Lean statements. The article labels below identify the statements in the manuscript.

The public declarations are in [MainResults.lean](../ConditionedStableLaws/MainResults.lean), in
the namespace `ConditionedStableLaws`.

| Article | Manuscript label | Lean |
| --- | --- | --- |
| Theorem A | `thm:ppp` | `TheoremA` |
| Theorem B | `thm:main-stable-laws` | `TheoremB` |
| Theorem C | `thm:conditional-clt-l2` | `TheoremC` |
| Theorem D | `thm:conditional-exponential-concentration` | `TheoremD` |
| Theorem E | `thm:conditional-poisson` | `TheoremE` |
| Theorem F | `thm:refined-conditional-lln` | `TheoremF` |

## Shared definitions and hypotheses

### State space, killing and conditioning

The compact metric space `M`, its Borel sigma-algebra and the reference probability `ρ` are the
ones in the article. `Option M` represents the enlarged state space: `some x` is a point of `M`
and `none` is the absorbing cemetery state.

[CanonicalChain.lean](../ConditionedStableLaws/CanonicalChain.lean) specifies a probability transition
kernel on `Option M` with an absorbing cemetery. Its path space is `ℕ → Option M`. The path law
`C.pathMeasure x` is constructed from the Dirac initial law at `some x` and the transition kernel.

- `C.toKilledKernel` restricts transitions to `M`; its mass is at most one.
- `escapingSet` is the set of points whose survival mass vanishes at some positive integer time.
  This is the article's `Z`.
- `survivingSet` is its complement, `M ∖ Z`.
- `survival n` requires every coordinate through time `n` to be different from `none`.
- `C.conditionedMeasure x n` is the actual conditional path law on `survival n`.
- `C.liveConditionedProbabilityMeasure d x n` packages the same measure as a probability measure
  for an initial state in `d.State`.

[PathSurvival.lean](../ConditionedStableLaws/PathSurvival.lean) proves the connection between survival,
the live endpoint and killed-kernel powers. Thus conditioning is on `τ > n`, while the Birkhoff
sum uses the indices `0,…,n−1`.

**Realisation.** The formal statements use this canonical path law. The manuscript also adopts
the canonical realisation for the Q-process argument. A separate transport theorem from an
arbitrary filtered realisation of the chain is not part of this comparison.

### Hypothesis H

[StandingHypothesis.lean](../ConditionedStableLaws/StandingHypothesis.lean) defines
`StandingHypothesis.HypothesisH ρ K`.

| Article assumption | Lean fields and interpretation |
| --- | --- |
| `ρ` is a fully supported Borel probability | `reference_probability`, `reference_fullSupport`; `BorelSpace M` identifies the measurable structure |
| (H1): transition densities, continuous in `L¹(ρ)` | `density : M → Lp ℝ 1 ρ`, `density_nonneg`, `kernel_eq_integral`, `continuous_density` |
| (H2): positive surviving reference mass | `surviving_mass_pos` |
| (H2): reachability of every nonempty relatively open subset of `M ∖ Z` | `irreducible`, with `RelativelyOpen A (survivingSet K.kernel)` and a positive integer iterate |
| (H3): no nontrivial Borel cyclic partition of `M ∖ Z` | `aperiodic`, quantified over `Fin k`-indexed measurable, nonempty, pairwise disjoint partition cells |

The density is represented by `L¹` equivalence classes. `HypothesisH.absolutelyContinuous`
derives absolute continuity of every transition measure from the density equation. Compactness
upgrades continuity of the density map to uniform continuity.

### Spectral data and the two measures

The public statements take explicit eigen-data and, where used, a `SurvivalGapData h d` witness.
The existence of these data is proved from H:

```lean
StandingHypothesis.HypothesisH.exists_eigenData_survivalGap
```

Its conclusion supplies a positive eigen-rate at most one, a continuous finite nonnegative
eigenfunction, its positivity set `d.liveSet = survivingSet K.kernel`, a probability left
eigenmeasure, the normalisation and the spectral-gap witness.

| Article notation | Lean representation |
| --- | --- |
| `λ` | `d.rate.toReal` |
| `η` | `(d.weight ·).toReal`; the weight itself takes values in `ℝ≥0∞` and is proved finite |
| `μ` | the probability measure supplied with `hleft : K.kernel ∘ₘ μ = d.rate • μ` |
| `μ(η) = 1` | `hnorm : ∫⁻ y, d.weight y ∂μ = 1` |
| `ν = η μ` | `μ.withDensity d.weight` |
| `x ∈ M ∖ Z` | `x : d.State`, using the positivity-set identity for the eigen-data produced from H |

The explicit spectral arguments therefore expose data whose existence is proved; they do not
require an independently assumed spectral gap or limit theorem.

### Admissibility, the observable and normalisation

For A and B, the density representative is a function `m : M → ℝ` with `Integrable m ρ`,
nonnegative values and
`μ = ρ.withDensity (fun y => ENNReal.ofReal (m y))`.

[LocalDensity.lean](../ConditionedStableLaws/LocalDensity.lean) defines
`IsAdmissibleAt ρ m x₀ dimension volumeConstant` as the conjunction of:

- positive local exponent and positive ball-volume constant, with the ball-volume ratio tending
  to that constant;
- `0 < m x₀`;
- convergence to zero of the average of `|m(y) − m(x₀)|` over open balls centred at `x₀`.

This is Definition `def:reg`. The `dimension` argument is the local exponent in that definition;
it need not be an integer or the dimension of a manifold. `hx₀ : d.weight x₀ ≠ 0` expresses
that the singularity lies in the surviving set for the chosen normalised eigen-data.

[Tails.lean](../ConditionedStableLaws/Tails.lean) defines `singularObservable x₀ β` to be
`dist x x₀ ^ (-β)` off `x₀`, and exactly `1` at `x₀`. The constant in the scale is
`volumeConstant * (d.weight x₀).toReal * m x₀`, the article's `C(x₀)`.

`positivePowerScale` agrees with `(C(x₀)n)^(1/α)` for positive integer `n` and is set to `1` at
`n = 0`. The Gaussian scale is `sqrt(C(x₀)n log n)`. Lean's total definitions at the finitely many
initial indices do not change convergence along `n → ∞`.

## Theorem A — Poisson point-process convergence

Source: [TheoremA.lean](../ConditionedStableLaws/TheoremA.lean).

**Hypotheses.** H, normalised continuous eigen-data, the density and admissibility above,
`β > 0`, a surviving singularity and a surviving initial state. The exponent is `α = dimension/β`.

**Conclusions.** `TheoremA` is a conjunction of:

1. convergence in distribution of the actual empirical point measures under the changing
   survival-conditioned probability measures, in the vague topology;
2. joint convergence of the counts on every finite family of pairwise disjoint intervals `(a,b]`
   in `(0,∞]`;
3. `IsPoissonRandomMeasure` for the constructed limiting measure with power intensity
   `α y^(-α−1) dy`, including Poisson count laws and independence on disjoint finite-intensity sets.

The component declarations are `TheoremA.pointProcess`, `TheoremA.intervalCounts` and
`TheoremA.poissonLaw`.

**Range.** The manuscript states A for `0 < α < 2`. The Lean declaration has no upper bound on
`α`; admissibility and `β > 0` give `α > 0`. Restricting this stronger point-process statement to
`α < 2` gives the article's theorem.

## Theorem B — Stable laws and the Gaussian boundary

Source: [TheoremB.lean](../ConditionedStableLaws/TheoremB.lean).

**Hypotheses.** H, its normalised spectral data, the original local admissibility assumptions,
`β > 0` and any surviving initial state. `TheoremB` collects the following four implications.

| Article part | Scale | Centring | Lean conclusion |
| --- | --- | --- | --- |
| (i), `0 < α < 1` | `(C(x₀)n)^(1/α)` | none | convergence to `positiveIntegral` |
| (ii), `α = 1` | `C(x₀)n` | `n ν(fβ 1_{fβ ≤ Bₙ})` | convergence to `unitCompensatedStable 1` |
| (iii), `1 < α < 2` | `(C(x₀)n)^(1/α)` | `n ν(fβ)` | `fβ ∈ L¹(ν)` and convergence to `fullyCompensatedStable α` |
| (iv), `α = 2` | `sqrt(C(x₀)n log n)` | `n ν(fβ)` | `fβ ∈ L¹(ν)` and convergence to `gaussianReal 0 1` |

The parts are exposed as `TheoremB.part_i`–`TheoremB.part_iv`. The limiting Poisson integrals
and their compensation conventions are constructed in the development.

The aggregate statement gives the convergence conclusions. The additional declarations
`TheoremB.laplace_i`, `TheoremB.characteristic_ii` and `TheoremB.characteristic_iii` give the
Laplace and characteristic functions specified in the article. `TheoremB.stable_i`,
`TheoremB.stable_ii` and `TheoremB.stable_iii` identify the three non-Gaussian limits as stable
laws, using the proved scaling identities. These identifications are part of the main-result audit.

## Theorem C — Conditional central limit theorem

Source: [TheoremC.lean](../ConditionedStableLaws/TheoremC.lean).

**Hypotheses.** H and its normalised spectral data, `g : M → ℝ`, `Measurable g`, `MemLp g 2 μ`,
and a surviving initial state. A real-valued function is finite at every point, as required by the
manuscript; no vanishing-on-`Z` condition is added.

**Conclusions.** Absolute summability of the covariance series, nonnegativity of the asymptotic
variance and convergence of `n^(-1/2) Sₙ(g − ν(g))` under the survival-conditioned laws to the
centred Gaussian with that variance.

`ConditionalCLT.correlation C μ d g m` uses the lag `m + 1`. Thus the sum over `m : ℕ` in Lean
is precisely the article's sum over positive lags. The diagonal term is integrated against `ν`,
and the remaining terms against `μ`, with the weight `η` inside the killed-kernel iterate.

The Gaussian parameter is written `asymptoticVariance.toNNReal`; the simultaneously proved
nonnegativity shows that this is the stated variance. Zero variance gives the Dirac mass at zero.

**Proof choice.** The bounded approximants in `L2Variance.truncation` set `g` to zero outside
`{|g| ≤ k}`, whereas the manuscript clips at `±k`. Both approximations converge to `g` in `L²`;
this changes the truncation argument, not the final observable class or conclusion.

## Theorem D — Conditional exponential concentration

Source: [TheoremD.lean](../ConditionedStableLaws/TheoremD.lean).

**Hypotheses.** H and its normalised spectral data, a measurable real-valued observable `f` and
an explicit pointwise bound `∀ y, |f y| ≤ F`. This expresses the boundedness assumed in the article.

**Conclusion.** The quantifier order in `TheoremD` is:

```text
∃ a > 0, ∀ surviving x, ∃ Cx > 0, ∀ ε > 0, ∀ n ≥ 1,
  P_x(|n⁻¹ Sₙ f − ν(f)| > ε | τ > n) ≤ Cx exp(−a ε² n).
```

For each fixed observable, the rate is independent of the initial state, the deviation threshold
and time. The prefactor may depend on the initial state and the fixed observable. This gives the
quadratic rate in the main statement. `TheoremD.explicitRate` separately exposes the
`min{t_h/4, ε²/(16 K_h)}` rate form.

## Theorem E — Shrinking-target Poisson law

Source: [TheoremE.lean](../ConditionedStableLaws/TheoremE.lean).

**Hypotheses.** H, normalised continuous eigen-data, a target `x₁` with nonzero eigenfunction,
a surviving initial state different from `x₁`, `ShrinkingNeighborhoods U x₁`, and convergence of
`n ν(Uₙ)` to the prescribed parameter.

[ShrinkingTargets.lean](../ConditionedStableLaws/ShrinkingTargets.lean) requires each `Uₙ` to be
measurable, to contain `x₁`, and eventually to lie in every neighbourhood of `x₁`. This follows
the article's definition: nesting and openness of the sets are not required. Lean indexes the
sequence by `ℕ`; the value at index zero does not affect the limit.

**Conclusion.** The law of the integer-valued count of visits at `0,…,n−1` converges to
`poissonProbabilityMeasure rate`, under the actual survival-conditioned law.

**Range and proof.** `rate : ℝ≥0` also permits zero, extending the positive-parameter statement.
The implementation obtains the scalar limit from its proved joint visit-count results; it does
not assume a Keller–Liverani rare-event theorem.

## Theorem F — Refined conditional laws of large numbers

Source: [TheoremF.lean](../ConditionedStableLaws/TheoremF.lean).

`TheoremF` collects all three parts under H and normalised probability eigen-data.

| Part | Observable assumptions | Initial states | Conclusion |
| --- | --- | --- | --- |
| (i) | measurable and bounded; no restriction on `Z` | every surviving state | conditional expectation of the absolute error tends to zero |
| (ii) | measurable, integrable against `μ`, zero at every point of `Z` | `ν`-almost every surviving state | conditional expectation of the absolute error tends to zero |
| (iii) | measurable, integrable against `ν`, zero at every point of `Z` | `ν`-almost every surviving state | the conditional probability of an error exceeding any fixed `ε > 0` tends to zero |

The almost-everywhere quantifier is expressed using
`(μ.withDensity d.weight).comap (Subtype.val : d.State → M)`. This is the invariant weighted
measure restricted to the surviving-state subtype.

The component names are `TheoremF.part_i`, `TheoremF.part_ii` and `TheoremF.part_iii`.
Part (iii) aliases `RefinedLLN.lln_probability`, whose signature does not require `μ` itself to be
a probability measure: the left eigenrelation and `μ(η) = 1` normalise the weighted measure. The
aggregate theorem uses the probability eigenmeasure common to the article's three statements.

## The nine remarks

The common import is [Remarks.lean](../ConditionedStableLaws/Remarks.lean). Each row below describes
the mathematical assertions represented by the audited declarations.

| Remark | Correspondence and proof entry points |
| --- | --- |
| Birkhoff indexing | The bounded differences are at most `2B/n` and `2B/(n+1)`. Endpoint negligibility on diverging scales is proved from H for finite-valued measurable observables; shifted and inclusive distributional limits and the conditional mean LLNs are transferred. See [EndpointReindexing.lean](../ConditionedStableLaws/EndpointReindexing.lean) and [EndpointMeanReindexing.lean](../ConditionedStableLaws/EndpointMeanReindexing.lean). |
| No killing (`rmk:no-kill`) | The eigen-rate and normalised eigenfunction are one, `ν = μ`, and conditioning leaves the canonical path law unchanged. See [ConservativeCase.lean](../ConditionedStableLaws/ConservativeCase.lean). |
| Admissibility (`rmk:admissible`) | Interior ball-volume regularity, almost-everywhere absolute-error differentiation, and admissibility at regular points with continuous positive density are proved. See [RiemannianRegularityRemark.lean](../ConditionedStableLaws/RiemannianRegularityRemark.lean) and [AdmissibleRiemannian.lean](../ConditionedStableLaws/AdmissibleRiemannian.lean). Riemannian volume is specified by its usual local coordinate identity with density `sqrt(det g)`; a global canonical volume construction is not asserted. |
| Independence of limiting counts | Limiting counts on disjoint finite-intensity sets are independent. A chain satisfying H with dependent finite singular-observable counts witnesses that finite counts need not be independent. Deterministic initial counts are also proved independent, so universal finite-time dependence is not asserted. See [FiniteCountRemark.lean](../ConditionedStableLaws/FiniteCountRemark.lean) and [SingularFiniteCountExample.lean](../ConditionedStableLaws/SingularFiniteCountExample.lean). |
| Continuous multipliers | All four regimes, the exact `|g(x₀)| Bₙ` scale, reflection for negative `g(x₀)` and any fixed finite centre value are proved. See the detailed comparison below. |
| Starting at the target | The positive-time count converges to Poisson even when the initial state is the centre; time zero adds exactly one, giving `1 + Poi(t)`. See [PoissonTargetStart.lean](../ConditionedStableLaws/PoissonTargetStart.lean). |
| Integrability under `μ` and `ν` | The inclusion, equivalent norms under a positive lower bound for `η`, and a weighted-measure counterexample to reverse inclusion are proved. The general conditional mean LLN under only `L¹(ν)` remains an open question, as in the article; no theorem asserts its resolution. See [WeightedLp.lean](../ConditionedStableLaws/WeightedLp.lean) and [RemarkConsequences.lean](../ConditionedStableLaws/RemarkConsequences.lean). |
| Canonical Q-process | Existence from H and probability one of staying in `M ∖ Z` at every time simultaneously are proved. This remark does not use the separate stationary-path ergodicity axiom. See [RemarkConsequences.lean](../ConditionedStableLaws/RemarkConsequences.lean). |
| Random-measure semiring | The measurable dissecting semiring of half-open intervals on `(0,∞]` and the implication from joint interval-count convergence to vague convergence in distribution are proved. See [VagueConvergence.lean](../ConditionedStableLaws/VagueConvergence.lean) and [IntervalRefinement.lean](../ConditionedStableLaws/IntervalRefinement.lean). |

### Continuous multipliers

The observable is `setCenterValue (observable x₀ β g) x₀ v`, where `Continuous g`, `g x₀ ≠ 0`
and `v : ℝ` is arbitrary. It equals `g(x) / dist(x,x₀)^β` off the centre and has value `v` there.
The common assumptions are those of Theorem B.

| Regime | Centring | Declaration in `ContinuousMultiplier` |
| --- | --- | --- |
| `0 < α < 1` | none | `stable_law_small_signed` |
| `α = 1` | `n ν(f 1_{abs(f) ≤ abs(g(x₀)) Bₙ})` | `stable_law_one_signed` |
| `1 < α < 2` | `n ν(f)`; integrability is also concluded | `stable_law_mid_signed` |
| `α = 2` | `n ν(f)`; integrability is also concluded | `stable_law_boundary_signed` |

Every denominator is exactly `|g(x₀)| Bₙ`, using the power scale or the Gaussian boundary scale
as appropriate. The stable limiting random variable is multiplied by `g(x₀)/|g(x₀)|`. The
Gaussian conclusion remains the standard centred Gaussian. In particular, at exponent one the
cutoff uses the absolute value of the signed observable, not a one-sided truncation.

The declarations are in [ContinuousMultiplierLimits.lean](../ConditionedStableLaws/ContinuousMultiplierLimits.lean)
and [ContinuousMultiplierOneSigned.lean](../ConditionedStableLaws/ContinuousMultiplierOneSigned.lean).

## Proof dependencies and the limits of this audit

[AuditMainTheorems.lean](../AuditMainTheorems.lean) checks the six aggregate declarations, their
public component declarations and the mapped implementation results. [AuditRemarks.lean](../AuditRemarks.lean)
checks the declarations for all nine remarks. Both reject any axiom other than `propext`,
`Classical.choice` and `Quot.sound`, including dependencies reached through private declarations.
These audits check proof dependencies; the statement correspondence is the mathematical
comparison documented above.

Two separate results should not be conflated with A–F:

- The required finite-measure real `L¹`–`L∞` midpoint compact-interpolation theorem is proved in
  [LpCompactInterpolation.lean](../ConditionedStableLaws/LpCompactInterpolation.lean). The general
  arbitrary-exponent compact-interpolation statement is not claimed as fully formalised.
- The separate stationary-path ergodicity conclusion for the Q-process retains the registered
  axiom in [Cited/QProcess.lean](../ConditionedStableLaws/Cited/QProcess.lean). A–F and the nine
  remark audits do not permit that axiom.

The supplied main-text manuscript references external settings, bibliography, diagram and
appendix files. This comparison covers its main statements and the audited LLN conclusions;
it is not a line-by-line comparison of the unsupplied appendix proof or every supporting proof.

To build the library and run the declaration and axiom checks:

```sh
lake exe cache get
python3 scripts/check.py --require-remarks
```

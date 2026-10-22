# Conditional stable laws and rare-event limits for absorbing Markov chains — Lean formalisation

This repository contains a Lean 4 formalisation of Theorems A–F and all nine remarks of the article
[*Conditional Stable Laws and Rare-Event Limits for Absorbing Markov Chains*](https://arxiv.org/abs/2609.22499),
by Bernat Bassols Cornudella and Matheus M. Castro.

- Every part of Theorems A–F and all nine remarks is proved.
- These proofs contain no `sorry` and use no additional cited axioms.
- Their axiom dependencies are confined to `propext`, `Classical.choice` and `Quot.sound`.

The project uses Lean 4.35.0 and Mathlib.

## Main theorems

The theorems follow the lettering of the article. They are collected in
[MainResults.lean](ConditionedStableLaws/MainResults.lean), in the namespace
`ConditionedStableLaws`.

| Article | Content | Lean |
| --- | --- | --- |
| Theorem A | Poisson point-process convergence for the normalised singular observations, including joint convergence of disjoint interval counts to independent Poisson variables | `TheoremA` |
| Theorem B | Totally right-skewed stable limits for $`0<\alpha<2`$, with the appropriate centring in each regime, and the Gaussian boundary limit at $`\alpha=2`$ with normalisation $`\sqrt{C(x_0)n\log n}`$ | `TheoremB` |
| Theorem C | Conditional central limit theorem for finite-valued observables in $`L^2(\mu)`$, absolute convergence of the covariance series and nonnegativity of the asymptotic variance | `TheoremC` |
| Theorem D | Conditional exponential concentration for bounded measurable observables, with bound $`C_x e^{-a_h\varepsilon^2 n}`$ for every $`\varepsilon>0`$ and $`n\geq1`$ | `TheoremD` |
| Theorem E | Conditional Poisson law for visits to shrinking neighbourhoods when $`n\nu(U_n)\to t`$, for every surviving initial state distinct from the target | `TheoremE` |
| Theorem F | Conditional mean laws of large numbers for bounded and $`L^1(\mu)`$ observables, and conditional convergence in probability for $`L^1(\nu)`$ observables, with the initial-state and vanishing-on-$`Z`$ conditions of the article | `TheoremF` |

`TheoremB.part_i`–`TheoremB.part_iv` and `TheoremF.part_i`–`TheoremF.part_iii` give the individual
parts. The point-process, interval-count and Poisson-law conclusions are also available separately
as `TheoremA.pointProcess`, `TheoremA.intervalCounts` and `TheoremA.poissonLaw`.

The proofs use the canonical path-space realisation of the chain, sums over $`0,\ldots,n-1`$ and
conditioning on $`\tau>n`$. The normalised eigen-data and spectral gap are derived from Hypothesis H.
Regularity and admissibility at the singularity point are the local assumptions of the article.

[docs/StatementsAudit.md](docs/StatementsAudit.md) compares the hypotheses and conclusions of each
main theorem and all nine remarks with the article. It records the canonical-path encoding,
the spectral data derived from H, and the extended parameter ranges in Theorems A and E.

## Remarks and continuous multipliers

All nine remarks are collected in [Remarks.lean](ConditionedStableLaws/Remarks.lean).
In particular, the formalisation covers the extension of Theorem B to

```math
f(x)=\frac{g(x)}{d_M(x,x_0)^\beta},\qquad x\ne x_0,
```

where $`g`$ is continuous, $`g(x_0)\ne0`$ and $`\beta>0`$. Any fixed finite value may be assigned at
$`x_0`$. With $`\alpha=d/\beta`$, all four regimes are proved with the normalisation

```math
B_{n,g}=\lvert g(x_0)\rvert B_n.
```

| Regime | Lean |
| --- | --- |
| $`0<\alpha<1`$ | `ContinuousMultiplier.stable_law_small_signed` |
| $`\alpha=1`$ | `ContinuousMultiplier.stable_law_one_signed` |
| $`1<\alpha<2`$ | `ContinuousMultiplier.stable_law_mid_signed` |
| $`\alpha=2`$ | `ContinuousMultiplier.stable_law_boundary_signed` |

For $`0<\alpha<1`$, no centring is required. At $`\alpha=1`$, the centring uses the absolute-value
truncation

```math
A_{n,g}=n\nu\!\left(f\,\mathbf{1}_{\{\lvert f\rvert\leq B_{n,g}\}}\right).
```

For $`1<\alpha\leq2`$, the centring is $`n\nu(f)`$. If $`g(x_0)<0`$, the stable limits are reflected
about the origin; the Gaussian limit is unchanged.

The other remarks cover Birkhoff indexing, the conservative case, admissibility, independence of
limiting counts, starting at the shrinking target, integrability with respect to $`\mu`$ and
$`\nu`$, the canonical $`Q`$-process, and the interval-semiring criterion for random measures.

## Mathematics used by the proofs

The development includes the following supporting results:

- **Spectral theory.** Positive eigenfunctions and eigenmeasures, the spectral decomposition and
  exponential gap under Hypothesis H, and the resulting quasi-stationary and quasi-ergodic measures.
- **Conditional mixing and Poisson limits.** Mixing of all orders, estimates for separated clusters,
  short-return bounds, factorial moments, the method of moments and convergence in the vague
  topology on locally finite point measures on $`(0,\infty]`$.
- **Stable laws.** Construction of Poisson random measures and compensated Poisson integrals,
  their Laplace and characteristic functions, small-jump estimates and the stable scaling identities.
- **Gaussian limits.** The finite-measure $`L^1`$–$`L^\infty`$ midpoint compact-interpolation theorem
  used to obtain $`L^2`$ compactness, spectral perturbation for the triangular-array CLT, and the
  covariance and truncation estimates for the Gaussian boundary and $`L^2`$ CLT.
- **Refined laws of large numbers.** Maximal inequalities, Cesàro convergence and transfer of
  convergence from the Doob-transformed chain to the survival-conditioned laws.

## Layout

```text
.
├── README.md
├── lakefile.toml, lake-manifest.json, lean-toolchain
├── ConditionedStableLaws.lean          root library import
├── ConditionedStableLaws/
│   ├── MainResults.lean               main theorem interface
│   ├── TheoremA.lean … TheoremF.lean   the six main results
│   ├── Remarks.lean                   the nine remarks
│   └── …                             supporting proofs
├── Audit.lean                         project axiom audit
├── AuditMainTheorems.lean             standard-axiom audit for A–F
├── AuditRemarks.lean                  standard-axiom audit for the remarks
├── docs/
│   └── StatementsAudit.md              comparison of the article and Lean statements
└── scripts/
    └── check.py                       build, declaration and axiom checks
```

## Build

Install Lean through [elan](https://github.com/leanprover/elan). Then, from this directory:

```sh
lake exe cache get
lake build
```

The compiler and dependency versions are fixed by `lean-toolchain` and `lake-manifest.json`.
Project warnings are treated as errors.

To check that the main results and all nine remarks depend only on the three standard axioms, run:

```sh
lake env lean AuditMainTheorems.lean
lake env lean AuditRemarks.lean
```

With Python 3 installed, `python3 scripts/check.py --require-remarks` runs the build, both audits,
the project-wide axiom audit and the declaration checks. GitHub Actions runs this verification on
pushes and pull requests.

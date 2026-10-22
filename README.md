<div align="center">

# Conditional Stable Laws and Rare-Event Limits for Absorbing Markov Chains

A Lean 4 formalisation of the paper Conditional Stable Laws and Rare-Event Limits for Absorbing Markov Chains  https://arxiv.org/abs/2609.22499.

</div>

The six main results are proved without `sorry` or cited axioms. The formalization
uses the canonical path-space formulation of the chain, under Hypothesis H.
This repository contains only the Lean formalisation, not the manuscript files.
Full-paper coverage is still incomplete; see [Scope](#scope).

## Main results

One letter, one module, one public theorem. The order follows the manuscript.

| Theorem | Result | Lean module |
| :---: | --- | --- |
| **A** | Poisson point-process convergence | [TheoremA](ConditionedStableLaws/TheoremA.lean) |
| **B** | Stable laws and the Gaussian boundary | [TheoremB](ConditionedStableLaws/TheoremB.lean) |
| **C** | Conditional central limit theorem in L²(μ) | [TheoremC](ConditionedStableLaws/TheoremC.lean) |
| **D** | Conditional exponential concentration | [TheoremD](ConditionedStableLaws/TheoremD.lean) |
| **E** | Conditional Poisson law for shrinking targets | [TheoremE](ConditionedStableLaws/TheoremE.lean) |
| **F** | Refined conditional laws of large numbers | [TheoremF](ConditionedStableLaws/TheoremF.lean) |

A includes the point-process limit, joint interval-count limits and the Poisson
law of the limit. B collects its four regimes; F collects its three LLN parts.
Their individual components remain available under the same letter.

### Continuous multipliers

The continuous-multiplier remark extends Theorem B to observables

```text
f(x) = g(x) / d(x, x₀)^β,   with any fixed finite value at x₀,
```

where `g` is continuous, `g(x₀) ≠ 0` and `β > 0`. All four regimes are proved
under Hypothesis H, with `α = dimension / β`, the normalisation `|g(x₀)| Bₙ`,
and no cited axioms. When `g(x₀) < 0`, the stable limits are reflected; the
centred Gaussian is unchanged.

| Regime | Lean theorem |
| :---: | --- |
| 0 < α < 1 | `ContinuousMultiplier.stable_law_small_signed` |
| α = 1 | `ContinuousMultiplier.stable_law_one_signed` |
| 1 < α < 2 | `ContinuousMultiplier.stable_law_mid_signed` |
| α = 2 | `ContinuousMultiplier.stable_law_boundary_signed` |

The theorems are in
[ContinuousMultiplierLimits](ConditionedStableLaws/ContinuousMultiplierLimits.lean)
and, for α = 1,
[ContinuousMultiplierOneSigned](ConditionedStableLaws/ContinuousMultiplierOneSigned.lean).
At α = 1 the centring is the integral truncated by `|f|`. See the other
remarks in [Development](docs/Development.md#remarks).

## Use

A single import exposes the public interface:

```lean
import ConditionedStableLaws.MainResults

open ConditionedStableLaws

#check TheoremA
#check TheoremB
#check TheoremC
#check TheoremD
#check TheoremE
#check TheoremF
```

For example, `TheoremB.part_i` through `TheoremB.part_iv` and
`TheoremF.part_i` through `TheoremF.part_iii` expose the individual parts.
See the [public API guide](docs/MainResults.md) for all companion declarations.

## Verify

Install Lean through [elan](https://lean-lang.org/install/manual/) and Python 3,
then run from the repository root:

```sh
lake exe cache get
python3 scripts/check.py --require-remarks
```

The toolchain and dependency manifest are pinned. Project warnings are treated
as errors (`warningAsError = true`). The project's files do not use Lean's
module system, which mathlib now targets; `allowNonModules = true` in
`lakefile.toml` declares this. Verification builds the library,
checks declaration coverage, audits the built library's axioms, and
checks the six public theorems against only `propext`, `Classical.choice`, and
`Quot.sound`. A successful proof check does not mean complete manuscript coverage.

The manuscript is not needed to build or verify the Lean proofs. Source hashes
are checked only if the corresponding external files are supplied. Use
`python3 scripts/check.py --require-manuscript --manuscript-dir /path/to/source`
to require that extra check. `--require-remarks` additionally requires all nine
remarks to be proved without cited axioms. The GitHub Actions workflow runs
this same proof and coverage check on pushes and pull requests.

The source archive contains a verification log, a source manifest, and
`RELEASE.json` with the checked scope. To prepare a new archive after edits:

```sh
mkdir -p .tools
python3 scripts/check.py --require-remarks > .tools/release-verification.log 2>&1
python3 scripts/package_release.py --verification-log .tools/release-verification.log
```

The packager requires a current successful verification receipt and checks
that the source files have not changed since that run. It excludes dependency
caches, generated binaries, manuscript files, and the unused standalone
Keller–Liverani axiom stub.

## Organization

- [MainResults.lean](ConditionedStableLaws/MainResults.lean) — the main theorem import.
- [Remarks.lean](ConditionedStableLaws/Remarks.lean) — the remark import.
- `TheoremA.lean` … `TheoremF.lean` — uniformly named theorem entry points.
- Other modules in `ConditionedStableLaws/` — the underlying proofs and infrastructure.
- [AuditMainTheorems.lean](AuditMainTheorems.lean) — the main-result axiom audit.
- [AuditRemarks.lean](AuditRemarks.lean) — the nine-remark axiom audit, including the finite-count existence examples.
- [coverage.json](coverage.json) — the checked manuscript-to-Lean inventory.

The public layer reuses the existing proofs. Original declaration names are kept
for compatibility; no proof was replaced by an assumption.

## Scope

All main results A–F and all nine remarks are proved, with the precise
interpretations documented in [Remarks](docs/Development.md#remarks).
The separate stationary Q-process ergodicity
conclusion still uses one registered cited axiom, which A–F do not depend on.
The remarks also use no cited axioms. The general compact-interpolation
theorem remains partial. The five examples are outside the requested scope.

The inventory contains 65 source items: 51 proved, 7 defined, 1 partial,
1 proved modulo a cited axiom and 5 excluded. Additional public
names do not count as additional manuscript results.

For details, see [Development and proof coverage](docs/Development.md) and
the [public API guide](docs/MainResults.md). The source labels and hashes in
`coverage.json` are metadata identifying the external manuscript snapshot;
the manuscript itself is not included. The checked local snapshot still has
the older finite-count sentence; this release covers the revised wording
“finite-n counts need not be independent”, as explained in the remark inventory.

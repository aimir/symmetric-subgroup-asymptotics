# Formal statements

[Statements.lean](SymmetricSubgroupAsymptotics/Statements.lean) defines the
three targets in [SPEC.md](../SPEC.md). They are propositions to be proved:

| Declaration | Meaning |
|---|---|
| `T1` | Exponential relative accuracy of the exact coefficient benchmark. |
| `T2` | Relative `O(1/n)` accuracy of the exact positive-saddle expression. |
| `T3` | The elementary four-periodic expression, with its explicit first correction and `O(n^(-1/2))` remainder. |
| `DefinitionChecks` | Finiteness, positivity, saddle existence/uniqueness, and convergence obligations. |
| `AllTargets` | The conjunction of `DefinitionChecks`, `T1`, `T2`, and `T3`. |

All declarations use the namespace `SymmetricSubgroupAsymptotics`. Defining a
proposition does not prove it. This module contains definitions and an
obligation structure; it has no theorem proofs, asserted axioms or proof
placeholders.

## Definitions to review

* `subgroupCount` counts `Subgroup (Equiv.Perm (Fin n))` directly.
* `binarySubspaceCount` counts every `Submodule (ZMod 2) (Fin r → ZMod 2)`.
* `criticalCoefficient` is a finite rational sum. `parityCoefficient` guards
  the shifted index before natural subtraction. `exactBenchmark` is `L_n`.
* `saddleRadius` is the infimum of the nonnegative upper level set of the
  saddle polynomial. This defines a real number without assuming a root
  exists. `DefinitionChecks.saddle_positive_unique` requires a proof that it
  is precisely the intended unique positive root when the rank is positive.
* `saddleBenchmark` is `Q_n`, with its two unused initial values set to one.
* `eulerProduct`, `kappaEven`, `kappaOdd` and `residueConstant` are the exact
  infinite-product/theta definitions. Their convergence and positivity are
  explicit obligations; default values of divergent sums cannot substitute
  for those proofs.
* `elementaryBenchmark` is `M_n`, with `M_0 = 1`. Its denominator uses
  `Real.exp 7`, equal to the mathematical `e^7`.
* `firstCorrection` subtracts in the reals, retaining the negative correction
  in even degree. All fractional exponents and analytic divisions are real.

Each target quantifies its constants before quantifying `n`, so its bounds are
uniform in parity and residue class. Taking the maximum of the three onset
indices gives the common-threshold formulation in the specification.
`AllTargets` requires the definition obligations as conclusions; it does not
assume them to obtain an implication.

The source imports mathlib. In a compatible Lean environment where mathlib and
its dependencies are on the search path, run from this directory:

```sh
lean SymmetricSubgroupAsymptotics/Statements.lean
```

The permanent project toolchain and mathlib dependency pins are a separate
configuration step. The [verification boundary](../ASSUMPTIONS.md#formal-theorem-boundary)
distinguishes conditional assembly, proofs relative to named published inputs,
and closed theorems.

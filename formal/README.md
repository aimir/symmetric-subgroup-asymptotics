# Lean formalization

The local project pins Lean **4.30.0** and mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Its complete dependency graph is
recorded in `lake-manifest.json`. With elan installed, run from this directory:

```sh
lake exe cache get
lake build
```

The first command obtains mathlib's precompiled objects; the second checks
this project's proofs. Cached dependencies allow the build to run offline.
There are no CI workflows.

## Statements and explicit benchmarks

[Statements.lean](SymmetricSubgroupAsymptotics/Statements.lean) defines the
three targets in [SPEC.md](../SPEC.md):

| Declaration | Meaning |
|---|---|
| `T1` | Exponential relative accuracy of the exact coefficient benchmark. |
| `T2` | Relative `O(1/n)` accuracy of the exact positive-saddle expression. |
| `T3` | The elementary four-periodic expression, with its explicit first correction and `O(n^(-1/2))` remainder. |
| `DefinitionChecks` | Finiteness, the Gaussian counting identity, positivity, saddle existence/uniqueness, and convergence obligations. |
| `AllTargets` | The conjunction of `DefinitionChecks`, `T1`, `T2`, and `T3`. |

All declarations use the namespace `SymmetricSubgroupAsymptotics`.
The three asymptotic targets are propositions to prove; defining them does
not establish them.

The binary factor in `exactBenchmark` and `saddleBenchmark` is the explicit
rational expression

    G_r = sum_(k=0)^r product_(i=0)^(k-1) (2^r - 2^i)/(2^k - 2^i).

`binaryGaussianCoefficient` defines each product, and `binaryGaussianSum`
defines the sum. The empty product is one. Every denominator in the product
is positive. `binarySubspaceCount` is a separate combinatorial object used
in the proof of the counting identity; neither benchmark depends on it.

* `subgroupCount` counts `Subgroup (Equiv.Perm (Fin n))` directly.
* `criticalCoefficient` is the finite rational coefficient sum.
  `parityCoefficient` guards the shifted index before natural subtraction.
* `saddleRadius` is the infimum of the nonnegative upper level set of the
  saddle polynomial. Its positive-root interpretation is proved separately.
  `saddleBenchmark` has its two unused initial values set to one.
* `eulerProduct`, `kappaEven`, `kappaOdd` and `residueConstant` use the exact
  infinite-product/theta definitions. Their convergence and positivity must
  be proved; default values of divergent sums cannot substitute for them.
* `elementaryBenchmark` is the explicit `M_n`, with `M_0 = 1`.
  `firstCorrection` subtracts in the reals, retaining the negative correction
  in even degree. Fractional exponents and analytic divisions are real.

Each target quantifies its constants before `n`, so the bounds are uniform in
parity and residue class. `Targets.lean` proves equivalence with the single
common threshold in Section 5 of the specification. `AllTargets` requires the
definition obligations as conclusions, not hypotheses.

## Proof modules

| Module | Mathematical content |
|---|---|
| [Foundations](SymmetricSubgroupAsymptotics/Foundations.lean) | Finite counts, positive Gaussian products and coefficients, exact-benchmark positivity and initial values. |
| [GaussianCount](SymmetricSubgroupAsymptotics/GaussianCount.lean) | Double counting independent tuples by their span proves the exact Gaussian formula for every dimension, then for all subspaces. |
| [Saddle](SymmetricSubgroupAsymptotics/Saddle.lean) | Positive root existence and uniqueness, identification with the specified infimum, variance bounds and benchmark positivity. |
| [Constants](SymmetricSubgroupAsymptotics/Constants.lean) | Euler-product convergence and positivity, theta summability, and positive residue constants and elementary benchmark. |
| [DefinitionsVerified](SymmetricSubgroupAsymptotics/DefinitionsVerified.lean) | Assembles every field of `DefinitionChecks`, including the counting identity, without added hypotheses. |
| [Recurrence](SymmetricSubgroupAsymptotics/Recurrence.lean) | Eventual row contraction gives boundedness first; scalar and row decay then transfer to error bounds. |
| [Targets](SymmetricSubgroupAsymptotics/Targets.lean) | Equivalence of the separate and common-threshold formulations. |
| [Coefficients](SymmetricSubgroupAsymptotics/Coefficients.lean) | Exact coefficient recurrence, its uniqueness, and bounds for every backwards coefficient shift. |
| [GeneratingFunction](SymmetricSubgroupAsymptotics/GeneratingFunction.lean) | The finite coefficient sum is exactly the coefficient of the formal exponential, including the parity factor and rank-zero convention. |
| [CoefficientBounds](SymmetricSubgroupAsymptotics/CoefficientBounds.lean) | Radius-dependent coefficient bounds and absolute convergence at every real or complex argument. |
| [GaussianEstimates](SymmetricSubgroupAsymptotics/GaussianEstimates.lean) | Explicit geometric errors for Euler products and normalized Gaussian coefficients. |
| [GaussianAsymptotics](SymmetricSubgroupAsymptotics/GaussianAsymptotics.lean) | Full even- and odd-rank Gaussian/theta asymptotics with explicit absolute and relative errors. |
| [SaddleEstimates](SymmetricSubgroupAsymptotics/SaddleEstimates.lean) | Quantitative radius and variance bounds, a two-correction saddle expansion, and ratio limits. |
| [AnalyticGeneratingFunction](SymmetricSubgroupAsymptotics/AnalyticGeneratingFunction.lean) | The convergent complex coefficient series equals the actual exponential, including the guarded parity coefficient. |
| [CoefficientIntegral](SymmetricSubgroupAsymptotics/CoefficientIntegral.lean) | Exact Cauchy, angular and real saddle integral identities for both parities. |
| [SaddleKernel](SymmetricSubgroupAsymptotics/SaddleKernel.lean), [SaddleKernelComplex](SymmetricSubgroupAsymptotics/SaddleKernelComplex.lean) | The decay, centered phase and parity amplitude, with an exact bridge to the complex integrand. |
| [SaddleCentral](SymmetricSubgroupAsymptotics/SaddleCentral.lean) | A uniform central-arc error bounded by `2^27/(r sqrt r)` at every positive rank. |
| [SaddleTails](SymmetricSubgroupAsymptotics/SaddleTails.lean) | Both outer arcs and the full Gaussian complement have proved uniform `O(r^(-3/2))` bounds. |
| [SaddleAssembly](SymmetricSubgroupAsymptotics/SaddleAssembly.lean) | Complete integral partition, Gaussian normalization and uniform relative `O(1/r)` error. |
| [SaddleBenchmarkEstimates](SymmetricSubgroupAsymptotics/SaddleBenchmarkEstimates.lean) | The unconditional `SaddleBenchmarkEstimate` and the implication `T2_of_T1`. |
| [ElementaryClassical](SymmetricSubgroupAsymptotics/ElementaryClassical.lean) | Quantitative logarithmic Stirling remainder and a uniform logarithmic error for the Gaussian sum. |
| [ElementarySaddle](SymmetricSubgroupAsymptotics/ElementarySaddle.lean) | First-order logarithmic saddle, amplitude and variance estimates, retaining the explicit correction. |
| [ElementaryParity](SymmetricSubgroupAsymptotics/ElementaryParity.lean) | Exact four-residue normalization, exact even-degree conversion, and a uniform bound for the odd-degree shift. |
| [ElementaryTransfer](SymmetricSubgroupAsymptotics/ElementaryTransfer.lean) | Exponentiation with the prescribed first correction and square-root remainder. |
| [ElementaryBenchmarkEstimates](SymmetricSubgroupAsymptotics/ElementaryBenchmarkEstimates.lean) | The unconditional `ElementaryBenchmarkEstimate`, `T3_of_T1`, and `AllTargets ↔ T1`. |
| [AsymptoticTransfer](SymmetricSubgroupAsymptotics/AsymptoticTransfer.lean) | T1 transfers the independently stated analytic benchmark estimates to T2 and T3; exponential absorption and correction bounds are proved. |
| [BinaryConstruction](SymmetricSubgroupAsymptotics/BinaryConstruction.lean) | An explicit injective map from binary subspaces to labelled pair-action subgroups gives `G_(n/2) ≤ subgroupCount n` in both parities. |

The Gaussian-sum bounds imply

    G_r = kappa_(r mod 2) * 2^floor(r^2/4) * (1 + O(r * 2^(-r/4))).

Their Lean statements give explicit constants and thresholds separately for
`r = 2m` and `r = 2m+1`. This exponential rate is sufficient for the analytic
targets; the stronger Gaussian error in the manuscript is not asserted here.
The saddle expansion, with `x = (96r)^(1/4)`, is the explicit inequality

    abs(rho_r - (x - 8/x - 12/x^2)) <= 2048/x^3     (r >= 683).

The full saddle coefficient estimate is proved, uniformly across both parities:

    exists K > 0, exists N >= 2, forall n >= N, abs(L_n / Q_n - 1) <= K/n.

Here `L_n = exactBenchmark n` and `Q_n = saddleBenchmark n`, with the approved
explicit Gaussian factor and full parity coefficient unchanged. Analytic
evaluation and Cauchy extraction identify their ratio with the normalized
real integral. The fixed central arc is `[-pi/4, pi/4]`; the linear term
controls all of its complement, including the other quartic peaks.
The real-part estimate retains phase cancellation and is uniform in the
normalized parity amplitude `d` throughout `[0,1]`. Constants are not optimized.

Consequently `T2_of_T1` proves `T1 -> T2` with no further analytic hypothesis.
The elementary estimate is also proved, with the approved formula unchanged:

    exists K > 0, exists N >= 2, forall n >= N,
      abs(L_n / M_n - 1 - (6*(n mod 2)-4)/(48n)^(1/4)) <= K/sqrt(n).

Here `M_n = elementaryBenchmark n`. The proof uses the sharp logarithmic
Stirling remainder `1/(12n)`, the Gaussian/theta bound, and the first saddle
displacement. Writing `v=x*(x-rho)`, the identity
`v^2/48-v/3 = -4/3+(v-8)^2/48` gives the required cancellation without a
higher-order root series. The complete rank-to-degree conversion is exact
in even degree; the odd shift has a proved error at most `128/sqrt(n)`.
Exponentiation preserves the correction because its square is of the
same order as the allowed remainder.

Thus `T3_of_T1` proves `T1 -> T3` with no further analytic hypothesis.
Together with the proved definition obligations, `allTargets_iff_T1` proves
`AllTargets ↔ T1`. Constants and thresholds are uniform in parity and residue
class; they are not optimized.
The pair-action construction counts a single fixed system of pairs and does
not establish the full critical-family lower bound.

The abstract recurrence results retain their kernel and counting hypotheses;
they do not establish a subgroup asymptotic without those estimates.
The [verification boundary](../ASSUMPTIONS.md#formal-theorem-boundary)
distinguishes conditional assembly, proofs relative to named published inputs,
and closed theorems. T1 remains unproved in Lean. The unconditional subgroup
asymptotics T2 and T3 therefore remain open, while both implications from T1
and both independent analytic benchmark estimates are proved.

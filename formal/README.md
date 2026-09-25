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
| [ShiftedCoefficientRatio](SymmetricSubgroupAsymptotics/ShiftedCoefficientRatio.lean) | Exact shifted coefficient extraction at the same saddle and the quantitative relative ratio error `O(1/r)`. |
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
| [CanonicalLifts](SymmetricSubgroupAsymptotics/CanonicalLifts.lean) | Exact subgroup/subspace correspondence through a surjective binary quotient, Gaussian cardinality, simultaneous full-projection counting and faithful permutation transport. |
| [CriticalProfiles](SymmetricSubgroupAsymptotics/CriticalProfiles.lean) | Complete four-colour profile enumeration and exact weighted coefficient identities, retaining the separate V4 and D8 weights and both parity decorations. |
| [FullProjection](SymmetricSubgroupAsymptotics/FullProjection.lean) | Actual hyperplane counts, the finite deficit at most `15r G_(r-1)`, and profile-uniform relative error `O(r 2^(-r/2))`, including canonical subgroup projections. |
| [LabelledOrbitProfiles](SymmetricSubgroupAsymptotics/LabelledOrbitProfiles.lean) | Concrete labelled block atlases, exact original-normalizer and occurrence-factorial weights, and recovery of the atlas from any full subgroup on separated transitive action types. |
| [ComplementCount](SymmetricSubgroupAsymptotics/ComplementCount.lean) | Actual complement/retraction equivalence, exact finite complement count, and weighted retained-annihilator duality with Gaussian expansion. |
| [SquareLiftFibres](SymmetricSubgroupAsymptotics/SquareLiftFibres.lean) | Exact square admissibility, actual lift/complement equivalence and fixed-intersection count, arbitrary-image restriction, and full projection under an explicit Frattini-kernel hypothesis. |
| [AllLifts](SymmetricSubgroupAsymptotics/AllLifts.lean) | Exact all-lifts annihilator and Gaussian-polynomial identities for every image in a finite central binary extension, retaining the original kernel and square coordinates. |
| [BinaryHeisenberg](SymmetricSubgroupAsymptotics/BinaryHeisenberg.lean), [PairedPermutations](SymmetricSubgroupAsymptotics/PairedPermutations.lean), [BinaryPlaneFunctions](SymmetricSubgroupAsymptotics/BinaryPlaneFunctions.lean), [CriticalActions](SymmetricSubgroupAsymptotics/CriticalActions.lean), [CriticalActionModels](SymmetricSubgroupAsymptotics/CriticalActionModels.lean) | Literal regular and Heisenberg actions, faithful transitivity, binary quotients, central kernel charts, Frattini containment, and original symmetric normalizers 2, 24, 8, 384. |
| [OrbitProfileAssembly](SymmetricSubgroupAsymptotics/OrbitProfileAssembly.lean) | Joint label/lift fibres, exact normalizer-weighted counts on a common labelled set and `Fin n`, and disjointness of distinct multiplicity profiles. |
| [CriticalProfileAssembly](SymmetricSubgroupAsymptotics/CriticalProfileAssembly.lean) | Installs the concrete four-action data in actual labelled critical families, proving their exact disjoint profile-weighted sum. |
| [OrbitProfileProduct](SymmetricSubgroupAsymptotics/OrbitProfileProduct.lean) | Faithful independent block action and an exact equivalence between full direct-product subgroups and full permutation-model subgroups. |
| [QuadraticRealization](SymmetricSubgroupAsymptotics/QuadraticRealization.lean), [HyperbolicFrames](SymmetricSubgroupAsymptotics/HyperbolicFrames.lean) | Actual quadratic realization torsors, nonsingular polar forms, and exact orthogonal orders 2 and 72 by kernel-checked hyperbolic-frame enumeration. |
| [CoordinateIncidence](SymmetricSubgroupAsymptotics/CoordinateIncidence.lean), [QuadraticIncidence](SymmetricSubgroupAsymptotics/QuadraticIncidence.lean) | Joint retained relations determine all pivot outcomes; actual surjective coordinate maps have a proved uniform realization-fibre bound, including a free binary summand. |
| [BinaryFrameIncidence](SymmetricSubgroupAsymptotics/BinaryFrameIncidence.lean), [BinaryFrameEstimates](SymmetricSubgroupAsymptotics/BinaryFrameEstimates.lean), [QuadraticSubspaceIncidence](SymmetricSubgroupAsymptotics/QuadraticSubspaceIncidence.lean) | Exact ordered-basis fibres retain any subspace predicate; their Euler-product normalization gives the actual annihilator-aware subspace-incidence bound. |
| [ExceptionalLiftKernel](SymmetricSubgroupAsymptotics/ExceptionalLiftKernel.lean), [ExceptionalGaussianBound](SymmetricSubgroupAsymptotics/ExceptionalGaussianBound.lean) | The complete joint Gaussian dimension sum has a proved profile- and parity-uniform `O(G_R 2^(-d))` bound with an explicit constant. |
| [BinaryRankSums](SymmetricSubgroupAsymptotics/BinaryRankSums.lean), [ExceptionalIncidence](SymmetricSubgroupAsymptotics/ExceptionalIncidence.lean) | Exact rank-binning of the literal weighted sum over actual U and nonzero B, and its uniform quadratic-incidence deficit bound. |
| [NoncanonicalLifts](SymmetricSubgroupAsymptotics/NoncanonicalLifts.lean), [RetainedQuadraticAnnihilator](SymmetricSubgroupAsymptotics/RetainedQuadraticAnnihilator.lean) | Removing the unique canonical lift removes precisely B=0; an explicit dual coordinate equivalence identifies the retained equations with the original square annihilator. |
| [PhysicalExceptionalBound](SymmetricSubgroupAsymptotics/PhysicalExceptionalBound.lean), [CriticalProducts](SymmetricSubgroupAsymptotics/CriticalProducts.lean) | Exact physical noncanonical count as retained incidence; concrete critical direct products satisfy every premise and have a proved uniform `O(G_R 2^(-d))` bound. |
| [ProductCanonicalLifts](SymmetricSubgroupAsymptotics/ProductCanonicalLifts.lean) | Constructs the actual finite-product binary quotient, retains every original projection, proves kernel coverage, and installs the uniform canonical full-projection estimate. |
| [CriticalProductTransport](SymmetricSubgroupAsymptotics/CriticalProductTransport.lean), [CriticalOccurrenceQuotients](SymmetricSubgroupAsymptotics/CriticalOccurrenceQuotients.lean), [CriticalProfileEstimates](SymmetricSubgroupAsymptotics/CriticalProfileEstimates.lean), [CriticalCanonicalProfiles](SymmetricSubgroupAsymptotics/CriticalCanonicalProfiles.lean) | Exact indexed permutation-range transport, original kernel equality, canonical/noncanonical partition, and uniform complete-model estimate; each V4 remains one width-two projection. |
| [PerturbedQuartic](SymmetricSubgroupAsymptotics/PerturbedQuartic.lean) | Bounds the complete original-weight exceptional profile sum by the explicit perturbed polynomial at the original saddle, giving eventual coefficient ratio at most `256 pi 2^(-R/32)`. |
| [WeightedCounting](SymmetricSubgroupAsymptotics/WeightedCounting.lean), [WeightedCriticalAssembly](SymmetricSubgroupAsymptotics/WeightedCriticalAssembly.lean), [EvenCriticalAsymptotic](SymmetricSubgroupAsymptotics/EvenCriticalAsymptotic.lean) | Positive weighted error assembly, exact factorial cancellation, and the complete even critical-family asymptotic and matching subgroup lower bound. |
| [OddMarker](SymmetricSubgroupAsymptotics/OddMarker.lean), [OddProfileActions](SymmetricSubgroupAsymptotics/OddProfileActions.lean), [OddCriticalProfiles](SymmetricSubgroupAsymptotics/OddCriticalProfiles.lean) | Natural S3, its forced A3 kernel and exact contraction preserving the entire exterior image; singleton and S3 model equivalences, original normalizer six, and total quotient rank including the marker. |
| [OddProfileAssembly](SymmetricSubgroupAsymptotics/OddProfileAssembly.lean), [OddCriticalAsymptotic](SymmetricSubgroupAsymptotics/OddCriticalAsymptotic.lean) | Disjoint actual odd-marker sectors with the rank-zero guard, original profile weights, and the complete odd critical-family asymptotic. |
| [CriticalFamilyAsymptotic](SymmetricSubgroupAsymptotics/CriticalFamilyAsymptotic.lean) | A single actual critical family on Fin n, both-parity exponential relative error, and the exponential lower side for the total subgroup count. |
| [BinaryFamilies](SymmetricSubgroupAsymptotics/BinaryFamilies.lean) | Intrinsic complete fixed-point-free binary families, complete critical inclusion, and exact disjoint F=Ccrit+E, with independent critical boundedness. |
| [BinaryAbelianization](SymmetricSubgroupAsymptotics/BinaryAbelianization.lean) | Actual binary character dual, onto evaluation for finite groups, universal quotient and exact homomorphism cardinalities. |
| [TerminalContraction](SymmetricSubgroupAsymptotics/TerminalContraction.lean) | Complete-exterior contraction through O²(T), preserving the entire critical-product image and every predicate on it. |
| [TerminalCentralFibres](SymmetricSubgroupAsymptotics/TerminalCentralFibres.lean), [TerminalRetractions](SymmetricSubgroupAsymptotics/TerminalRetractions.lean), [TerminalFibreCount](SymmetricSubgroupAsymptotics/TerminalFibreCount.lean) | Actual scalar splitting annihilator, kernel-retraction equivalence, and complete central-fibre count for arbitrary finite nonabelian exterior images. |
| [TerminalCohomology](SymmetricSubgroupAsymptotics/TerminalCohomology.lean) | The retained annihilator equals the kernel of the actual scalar H² class map; actual inflation kernels and their pulled-coboundary membership criterion. |
| [TerminalGraphClassification](SymmetricSubgroupAsymptotics/TerminalGraphClassification.lean), [TerminalRecords](SymmetricSubgroupAsymptotics/TerminalRecords.lean), [TerminalRecordAssembly](SymmetricSubgroupAsymptotics/TerminalRecordAssembly.lean) | All exterior-full quotient images, reversible ordered records, faithful original group maps, and exact original divisor for any actual-image weight. |
| [CocycleLifts](SymmetricSubgroupAsymptotics/CocycleLifts.lean), [JointSourceGraphs](SymmetricSubgroupAsymptotics/JointSourceGraphs.lean) | Literal fixed-source lift–cocycle fibres and the full marked graph moment in degree b+q(s+2c), allowing repeated maps and proper joint images. |
| [SharedC3](SymmetricSubgroupAsymptotics/SharedC3.lean), [SharedC3LinearCounts](SymmetricSubgroupAsymptotics/SharedC3LinearCounts.lean), [SharedC3Counts](SymmetricSubgroupAsymptotics/SharedC3Counts.lean) | Actual scalar semidirect-product map classification, exact onto linear-map counts, and shared-C3 single/double-mark audit formulae with all coboundaries retained. |
| [TerminalGaussian](SymmetricSubgroupAsymptotics/TerminalGaussian.lean), [TerminalEstimates](SymmetricSubgroupAsymptotics/TerminalEstimates.lean) | The complete terminal double sum, its endpoint-sensitive ratio, convergent relation series, and zero-inflation polynomial bound. |
| [TerminalIncidenceCohomology](SymmetricSubgroupAsymptotics/TerminalIncidenceCohomology.lean), [TerminalIncidence](SymmetricSubgroupAsymptotics/TerminalIncidence.lean), [TerminalIncidenceRecords](SymmetricSubgroupAsymptotics/TerminalIncidenceRecords.lean) | Actual H² diagonal invariants, vertical and mixed splitting tests, and ordered-record incidence with the actual retained inflation-kernel factor. |
| [TerminalIncidencePullback](SymmetricSubgroupAsymptotics/TerminalIncidencePullback.lean), [TerminalIncidenceCritical](SymmetricSubgroupAsymptotics/TerminalIncidenceCritical.lean) | The literal critical-product section and multiplication defect connect the original pullback-annihilator predicate to the proved incidence estimate with local constant 72. |
| [CocycleCardinality](SymmetricSubgroupAsymptotics/CocycleCardinality.lean), [InflationRestriction](SymmetricSubgroupAsymptotics/InflationRestriction.lean), [Non2LiftBound](SymmetricSubgroupAsymptotics/Non2LiftBound.lean) | Exact B1/H1 and restriction-image factors, and numerical bounds for arbitrary survival-restricted lifts in the original possibly nonsplit extension. |
| [Non2SylowReduction](SymmetricSubgroupAsymptotics/Non2SylowReduction.lean), [Non2SharedC3Audit](SymmetricSubgroupAsymptotics/Non2SharedC3Audit.lean) | The original Sylow normalizer maps onto the quotient; restriction preserves its actual equivariance, with exact shared-C3 cohomological single/double-mark audits. |
| [FusionNumerics](SymmetricSubgroupAsymptotics/FusionNumerics.lean), [FusionPointingRatio](SymmetricSubgroupAsymptotics/FusionPointingRatio.lean), [FusionCold](SymmetricSubgroupAsymptotics/FusionCold.lean) | Complete hot-moment inequality and rounded square, exact both-parity pointing ratio, original cold divisors, and exponential finite-menu cold sums. |
| [FusionHotBenchmark](SymmetricSubgroupAsymptotics/FusionHotBenchmark.lean), [FusionHot](SymmetricSubgroupAsymptotics/FusionHot.lean), [FusionZeroWidth](SymmetricSubgroupAsymptotics/FusionZeroWidth.lean) | Elementary all-pairs benchmark normalization, quadratic hot-kernel decay relative to an explicit coarse counting input, and the zero-width moment case. |
| [BinaryTransport](SymmetricSubgroupAsymptotics/BinaryTransport.lean), [BinaryTransportFibreProducts](SymmetricSubgroupAsymptotics/BinaryTransportFibreProducts.lean) | Reversible simultaneous transport of actual subgroups through arbitrary proper subdirect carriers, literal axes, full projections, and unchanged original fixed weights. |
| [BinaryMixtureCentralComparison](SymmetricSubgroupAsymptotics/BinaryMixtureCentralComparison.lean), [BinaryMixtureCyclicFour](SymmetricSubgroupAsymptotics/BinaryMixtureCyclicFour.lean) | Actual central-extension-to-split comparison preserving every exterior image and its weights, instantiated on C4 powers over arbitrary finite nonabelian exteriors. |

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

The shifted coefficient ratio is now also proved independently of T1:

    exists C > 0, exists N >= 1, forall r >= N,
      abs(c_(r-1)/(rho_r*c_r)-1) <= C/r.

Both coefficients use the same saddle `rho_r`. Exact coefficient extraction
identifies this ratio with the quotient of the normalized amplitude-one and
amplitude-zero integrals. The uniform integral estimate applies to both;
eventual denominator control justifies division. The module also proves the
corresponding absolute error and normalized limit.

For critical counting, `CriticalProfiles` proves the exact finite weighted
profile identity, including `1/24+1/8=1/6` for the two distinct rank-two
actions. `CanonicalLifts` separately counts actual subgroups containing the
kernel of a supplied surjective binary quotient: there are exactly `G_r`.
Its restricted correspondence retains every full-coordinate condition. A
canonical lift contains the entire kernel, so a commuting quotient square
with the stated kernel coverage proves fullness on an actual factor directly.
Faithful permutation transport preserves distinct subgroups.

`FullProjection` proves that at most `r` surjective coordinates of dimensions
at most four exclude at most `15r G_(r-1)` subspaces. Its relative-error
constant and threshold are chosen before all coordinate profiles; the rate is
`O(r 2^(-r/2))`. The same bounds count actual canonical subgroup projections.

`LabelledOrbitProfiles` constructs actual families of block charts. Their
cardinality is exactly `n! / product(a(U)^m(U) m(U)!)`, where `a(U)` is the
normalizer in the original permutation group. This is also proved as a
rational identity. Transitivity and pairwise distinction of permutation-action
types let a full subgroup recover its orbit blocks, projected actions, and
unique atlas within the specified profile. Equal-size actions remain separate.

For a finite central extension with binary kernel `K` and quotient `V`,
`AllLifts` proves, for every `U <= V`,

    #{H : image(H)=U} = sum_(B <= Q(U)^perp) 2^(dim(U)*dim(B))
                     = sum_(j=0)^dim(Q(U)^perp) [dim(Q(U)^perp) choose j]_2
                         * 2^(dim(U)*j).

Here `Q(U)` is the span of the actual squares above `U`, expressed in the
supplied kernel chart. Restriction preserves those original coordinates
pointwise. The proof partitions literal subgroups by `H intersect K`, proves
the square admissibility condition, identifies each fibre with actual linear
complements, and only then reindexes by annihilator duality. The square
condition cannot be replaced by the commutator condition alone.

The four local actions are constructed explicitly. The degree-four and
degree-eight nonabelian models act by `(x,z) ↦ (x+a,z+b·x+c)`, with quotient
`(a,b)` and central binary coordinate `c`. Actual squares prove Frattini
containment. Their original symmetric normalizers are computed as literal
permutation groups; no catalogue order is assumed.

`OrbitProfileAssembly` counts actual conjugate subgroups on `Fin n`.
An internal symmetry acts jointly on the labels and the model subgroup;
the proof does not assume that it fixes each lift. Full subgroups recover
their complete multiplicity profile, so distinct profiles contribute disjoint
families. The full-subgroup specialization proves its own naturality premise.

For every retained relation space `B`, `QuadraticSubspaceIncidence` proves

    #{U : dim U=k, U full, every relation in B annihilates q(U)}
      <= phi^(-1) [R choose k]_2 * 72^dim(B) / 2^(2k dim(B)).

Its hypotheses are a literal product chart, nonsingular coordinate polar
forms of dimension at least two, and the proved local isometry-cardinality
bound. Choosing a basis from the coordinate restrictions on `B` fixes all
pivot quadratic forms jointly. Counting actual realization fibres, then
actual ordered-basis fibres, preserves the original incidence throughout.
The numerical sum over all image and positive relation dimensions is uniform
in both the orbit profile and parity; its constant is explicit and unoptimized.

`PhysicalExceptionalBound` identifies the entire weighted incidence sum
with actual noncanonical subgroups. `CriticalProducts` verifies every premise
for arbitrary finite products of D8/E8 with a free binary factor. It counts
literal subgroups with full projections onto the actual nonabelian factors:

    N_exceptional <= (2^66 * Theta_half / phi^4) * G_R * 2^(-(R/2-t)),
    Theta_half = sum_(j in Z) 2^(-j^2/4).

Further full-projection requirements on the regular C2/V4 coordinates select
a subfamily, so the same bound applies. This includes the zero-gap case;
a constant relative bound on an all-D8 word is not claimed to decay.
`OrbitProfileProduct` supplies the exact independent-block action equivalence,
and `CriticalProfileAssembly` exposes that actual product-subgroup fibre in
the original-weight formula.

The indexed permutation-range products are transported to those coordinate
groups through the proved faithful action equivalences. The product kernel
is retained exactly; each original V4 projection remains a width-two condition.
This installs both the canonical deficit and exceptional lift estimate on the
actual model subgroup count. Summing the latter with the original weights
gives the perturbed coefficient. Its exponential decay follows by evaluating
at the already proved original saddle.

For the odd S3 marker, fourth powers force A3 on that coordinate alone.
The exact contraction preserves the complete exterior subgroup image and
adds one binary quotient coordinate. Thus an exterior profile of rank R-1
has total quotient rank R. Its physical weight is the exterior weight divided
by six; no artificial C2 normalizer is charged. The singleton and S3 sectors
are disjoint actual orbit profiles.

`CriticalFamilyAsymptotic.criticalSubgroups_relative_error` proves, with one
constant and threshold for both parities,

    abs(card(CriticalSubgroups n) / exactBenchmark n - 1) <= K * 2^(-n/96).

Every member is an actual subgroup on Fin n, and every full lift over a
permitted critical profile is included. Consequently
`subgroupCount_critical_lower` proves the matching exponential lower bound
for the total subgroup count. The rate is unoptimized. Profile weights are
never asserted to be subgroup cardinalities by definition.

The complete binary family is now defined intrinsically by the 2-group
condition and absence of singleton orbits. `binaryFamilyRatio_partition`
proves the exact F=Ccrit+E identity, with E the complement of all critical
profiles, including noncanonical lifts. This does not bound E.

For an actual central extension with elementary binary kernel, the terminal
counting theorem proves

    card {H <= X : image(H) = Y} = sum_(L <= Ann) 2^(d₂(Y) * dim L).

The annihilator is the literal image of scalar character restriction, and
`TerminalCohomology` identifies it with the kernel of the actual scalar H²
class map. The source Y may be nonabelian. Complete-exterior contraction,
all quotient graphs and the original |GL(u,2)| 2^(u d₂(T)) record divisor
are also proved, with arbitrary conditions and weights on the actual image.
The terminal numerical double sum is now bounded, including its large-d
endpoint. Actual H² diagonal and commuting-pair tests give an allowable
function space of dimension at most the retained inflation-kernel dimension
tau. The ordered-record incidence bound consequently retains the factor
`(72 * 2^tau)^ell`. Installing that bound on the complete physical attachment
count, including the global original-record divisor and weighted assembly,
remains a further obligation.

For a faithful degree-s cover of B, `JointSourceGraphs` proves

    sum_(J <= S_b) (card(Epi(J,B)) * 2^(c*d₂(J)))^q
      <= subgroupCount (b + q*(s+2*c)).

Every map in a tuple has the same actual source J. The lift correspondence
retains literal cocycles and arbitrary survival predicates. The shared-C3
fixture proves the actual counts 4^(m(r+1)) and
4^m product_(i<m)(4^r-4^i), including degenerate ranks, and a genuine
same-source double-mark count. The new cohomological audit independently
recovers `|H1|=1`, `|B1|=4^m`, and actual restriction-image size `4^(mr)`.
Inflation-restriction now proves the exact restriction-image factor and
the bound `|A| |H1(B,A)| |Hom(ker beta,A)^J|` for the original lift fibre,
including arbitrary survival predicates and empty fibres. Actual Sylow
restriction retains the normalizer action; the finite-length fractional
Schur inequality and permutation quotient-rank bound remain needed for
the advertised numerical exponent.

The numerical fusion kernels retain the original factorials and action
divisor. Fixed-width cold kernels are exponentially small in the complete
complement degree. Positive-width hot kernels are quadratically small,
relative only to the explicit coarse counting input `1/16 + o(1)`.
Zero-width moment bounds force every retained weight to be at most one.
These numerical results do not yet install physical orbit pointing,
capacity certificates, or the surviving c=1 owner application.

Simultaneous binary transport now reconstructs the literal original subgroup
from the full replacement relation, including nonabelian proper subdirect
carriers. The central binary extension comparison is proved for every exact
exterior image and its nonnegative weights, and is instantiated for C4
powers. Complete finite-menu coverage, the joint numerical transition
estimates, labelled decoration bounds and the binary-error recurrence
remain separate obligations.

The abstract recurrence results retain their kernel and counting hypotheses;
they do not establish a subgroup asymptotic without those estimates.
The [verification boundary](../ASSUMPTIONS.md#formal-theorem-boundary)
distinguishes conditional assembly, proofs relative to named published inputs,
and closed theorems. T1 remains unproved in Lean. The unconditional subgroup
asymptotics T2 and T3 therefore remain open, while both implications from T1
and both independent analytic benchmark estimates are proved.

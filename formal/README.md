# Lean formalization

The local project pins Lean **4.30.0** and mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Its complete dependency graph is
recorded in `lake-manifest.json`. With elan installed, obtain mathlib's
precompiled objects from this directory:

```sh
lake exe cache get
```

Check project modules individually, in dependency order, with
[check_lean.py](../scripts/check_lean.py). For example, from the repository root:

```sh
python3 -B scripts/check_lean.py SymmetricSubgroupAsymptotics/FiniteGroupCertificates.lean \
  --log-dir ../lean-check-logs
```

The runner requires existing import objects and validates available local
check receipts. It records legacy imports without receipts as unverified;
it does not recursively certify all installed dependency objects.
It permits one compiler at a time and one Lean thread, with defaults of
3 GiB allocator memory and a sampled 4 GiB process-group RSS watchdog.
Selected modules may use up to `--memory-mb 12288 --rss-limit-mb 16384`,
allowing 12 GiB allocator memory and a 16 GiB RSS threshold. Larger limits
are rejected; use lower limits whenever sufficient.
The RSS watchdog is sampled, not an operating-system hard allocation limit.
Every check also has a wall timeout. Split certificates that exceed these
ceilings. Logs and hash receipts stay outside this repository. A failed check
does not replace its previous object file. Avoid unrestricted parallel
`lake build` for generated finite certificates; use the capped runner.
Cached dependencies allow checking offline. There are no CI workflows.
The supervisor's small process and receipt regressions run locally with
`python3 -B scripts/test_check_lean.py` from the repository root; they do
not invoke Lean or allocate large amounts of memory.

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
| [BinaryCharacterProducts](SymmetricSubgroupAsymptotics/BinaryCharacterProducts.lean), [PrimeAbelianization](SymmetricSubgroupAsymptotics/PrimeAbelianization.lean), [PrimeFrattini](SymmetricSubgroupAsymptotics/PrimeFrattini.lean), [PrimeActionQuotient](SymmetricSubgroupAsymptotics/PrimeActionQuotient.lean) | Exact product character ranks; the actual elementary prime quotient and its Frattini identification; reversible descent of equivariant Hom spaces with the original Sylow-normalizer action. |
| [TerminalContraction](SymmetricSubgroupAsymptotics/TerminalContraction.lean) | Complete-exterior contraction through O²(T), preserving the entire critical-product image and every predicate on it. |
| [Non2NoSelectedResidual](SymmetricSubgroupAsymptotics/Non2NoSelectedResidual.lean) | Proves the intrinsic no-selected O02 contradiction: if every actual orbit image is binary or natural `S3` and there are no singleton or three-point marker orbits, simultaneous faithful restriction makes the complete exterior a `2`-group, so its literal `O²` residual is trivial. Proper subdirect products are included. Routing the final physical O02 atoms into this state remains explicit. |
| [TerminalCentralFibres](SymmetricSubgroupAsymptotics/TerminalCentralFibres.lean), [TerminalRetractions](SymmetricSubgroupAsymptotics/TerminalRetractions.lean), [TerminalFibreCount](SymmetricSubgroupAsymptotics/TerminalFibreCount.lean) | Actual scalar splitting annihilator, kernel-retraction equivalence, and complete central-fibre count for arbitrary finite nonabelian exterior images. |
| [TerminalCohomology](SymmetricSubgroupAsymptotics/TerminalCohomology.lean) | The retained annihilator equals the kernel of the actual scalar H² class map; actual inflation kernels and their pulled-coboundary membership criterion. |
| [BinaryInflationKernel](SymmetricSubgroupAsymptotics/BinaryInflationKernel.lean), [BinaryTransgressionExact](SymmetricSubgroupAsymptotics/BinaryTransgressionExact.lean) | Constructs normalized kernel characters from actual pulled-coboundary primitives. For an arbitrary surjection the inflation-kernel dimension is bounded by the full ambient invariant-character head. For the complete binary evaluation quotient, proves equality with the actual terminal H² defect, using a section cocycle and exact kernels of the two linear maps. The equality is not asserted for arbitrary surjections. |
| [TerminalGraphClassification](SymmetricSubgroupAsymptotics/TerminalGraphClassification.lean), [TerminalRecords](SymmetricSubgroupAsymptotics/TerminalRecords.lean), [TerminalRecordAssembly](SymmetricSubgroupAsymptotics/TerminalRecordAssembly.lean) | All exterior-full quotient images, reversible ordered records, faithful original group maps, and exact original divisor for any actual-image weight. |
| [TerminalPullbackFibres](SymmetricSubgroupAsymptotics/TerminalPullbackFibres.lean), [TerminalRankRecords](SymmetricSubgroupAsymptotics/TerminalRankRecords.lean), [TerminalDivisorArithmetic](SymmetricSubgroupAsymptotics/TerminalDivisorArithmetic.lean) | Exact original subgroup-image fibres, all ordered records at each vertical rank, and the original basis-and-lift divisor with its uniform Gaussian normalization. |
| [TerminalIncidenceSum](SymmetricSubgroupAsymptotics/TerminalIncidenceSum.lean), [TerminalRecordFibreWeights](SymmetricSubgroupAsymptotics/TerminalRecordFibreWeights.lean), [TerminalImageCounts](SymmetricSubgroupAsymptotics/TerminalImageCounts.lean), [TerminalAttachmentBound](SymmetricSubgroupAsymptotics/TerminalAttachmentBound.lean), [TerminalAttachmentEstimates](SymmetricSubgroupAsymptotics/TerminalAttachmentEstimates.lean) | Complete physical terminal counting and original-weight aggregation, with actual quotient images, central fibre weights, retained inflation kernel, original record divisor, and uniform and endpoint estimates. |
| [CocycleLifts](SymmetricSubgroupAsymptotics/CocycleLifts.lean), [JointSourceGraphs](SymmetricSubgroupAsymptotics/JointSourceGraphs.lean) | Literal fixed-source lift–cocycle fibres and the full marked graph moment in degree b+q(s+2c), allowing repeated maps and proper joint images. |
| [SharedC3](SymmetricSubgroupAsymptotics/SharedC3.lean), [SharedC3LinearCounts](SymmetricSubgroupAsymptotics/SharedC3LinearCounts.lean), [SharedC3Counts](SymmetricSubgroupAsymptotics/SharedC3Counts.lean) | Actual scalar semidirect-product map classification, exact onto linear-map counts, and shared-C3 single/double-mark audit formulae with all coboundaries retained. |
| [TerminalGaussian](SymmetricSubgroupAsymptotics/TerminalGaussian.lean), [TerminalEstimates](SymmetricSubgroupAsymptotics/TerminalEstimates.lean) | The complete terminal double sum, its endpoint-sensitive ratio, convergent relation series, and zero-inflation polynomial bound. |
| [TerminalIncidenceCohomology](SymmetricSubgroupAsymptotics/TerminalIncidenceCohomology.lean), [TerminalIncidence](SymmetricSubgroupAsymptotics/TerminalIncidence.lean), [TerminalIncidenceRecords](SymmetricSubgroupAsymptotics/TerminalIncidenceRecords.lean) | Actual H² diagonal invariants, vertical and mixed splitting tests, and ordered-record incidence with the actual retained inflation-kernel factor. |
| [TerminalIncidencePullback](SymmetricSubgroupAsymptotics/TerminalIncidencePullback.lean), [TerminalIncidenceCritical](SymmetricSubgroupAsymptotics/TerminalIncidenceCritical.lean) | The literal critical-product section and multiplication defect connect the original pullback-annihilator predicate to the proved incidence estimate with local constant 72. |
| [CocycleCardinality](SymmetricSubgroupAsymptotics/CocycleCardinality.lean), [InflationRestriction](SymmetricSubgroupAsymptotics/InflationRestriction.lean), [Non2LiftBound](SymmetricSubgroupAsymptotics/Non2LiftBound.lean) | Exact B1/H1 and restriction-image factors, and numerical bounds for arbitrary survival-restricted lifts in the original possibly nonsplit extension. |
| [Non2SylowReduction](SymmetricSubgroupAsymptotics/Non2SylowReduction.lean), [Non2SharedC3Audit](SymmetricSubgroupAsymptotics/Non2SharedC3Audit.lean) | The original Sylow normalizer maps onto the quotient; restriction preserves its actual equivariance, with exact shared-C3 cohomological single/double-mark audits. |
| [SchurFiniteLength](SymmetricSubgroupAsymptotics/SchurFiniteLength.lean), [SchurCapacity](SymmetricSubgroupAsymptotics/SchurCapacity.lean), [SchurMultiplicity](SymmetricSubgroupAsymptotics/SchurMultiplicity.lean), [SchurRestriction](SymmetricSubgroupAsymptotics/SchurRestriction.lean) | Finite-length Hom bounds for arbitrary sources, actual simple-socle capacity and Schur-division-ring multiplicities, and exact capacity preservation under a surjective acting-algebra map. |
| [SchurRepresentation](SymmetricSubgroupAsymptotics/SchurRepresentation.lean), [RepresentationSchurRows](SymmetricSubgroupAsymptotics/RepresentationSchurRows.lean), [Non2SchurBound](SymmetricSubgroupAsymptotics/Non2SchurBound.lean), [SchurSharedC3Audit](SymmetricSubgroupAsymptotics/SchurSharedC3Audit.lean) | Numerical fractional-Schur bounds on the actual Sylow/Frattini source, arbitrary original survival predicates, both shared-C3 marks and translations, and the full-capacity trivial-C3 counterexample. The row decomposition proves that every fixed simple row is bounded by the literal invariant dimension and defines the concrete supremum over all nonfixed simple rows, whose maximum bounds the full intrinsic capacity. |
| [Non2CentralCutNumerics](SymmetricSubgroupAsymptotics/Non2CentralCutNumerics.lean), [Non2CentralCutFusion](SymmetricSubgroupAsymptotics/Non2CentralCutFusion.lean) | The retained annihilator cut `min (t/2) (t-ell)` combines the fixed-space and unipotent budgets with the coupled nontrivial-socle estimate to give the complete `47/48` cost. The real-valued endpoint allows fractional Schur capacity, uses the same cut for the trivial and nontrivial rows, and absorbs the sole additive one exactly from physical degree at least 24. The fusion installation applies this bound to the actual quotient-module capacity and proves the explicit central-prefix reserve `s/768`. |
| [Non2RetainedAnnihilatorCut](SymmetricSubgroupAsymptotics/Non2RetainedAnnihilatorCut.lean) | Constructs the literal retained cut inside the original invariant space by an evaluation separator for the complete fixed-valued displacement image. The checked cut has dimension `min (t/2) (t-ell)`, has zero full displacement slice, and gives exact quotient fixed dimension `t-c`, with no coordinate basis or pivot choice. |
| [Non2SchurRowProfile](SymmetricSubgroupAsymptotics/Non2SchurRowProfile.lean), [Non2SchurRowDegrees](SymmetricSubgroupAsymptotics/Non2SchurRowDegrees.lean), [Non2SchurActionKernel](SymmetricSubgroupAsymptotics/Non2SchurActionKernel.lean), [Non2SchurMixedSocleDimension](SymmetricSubgroupAsymptotics/Non2SchurMixedSocleDimension.lean), [Non2SchurScalarOrbit](SymmetricSubgroupAsymptotics/Non2SchurScalarOrbit.lean), [Non2SchurFaithfulDegree](SymmetricSubgroupAsymptotics/Non2SchurFaithfulDegree.lean), [Non2SchurDegreeEightOrder](SymmetricSubgroupAsymptotics/Non2SchurDegreeEightOrder.lean), [Non2SchurBranchAssignment](SymmetricSubgroupAsymptotics/Non2SchurBranchAssignment.lean), [PermutationOrbitHeadSection](SymmetricSubgroupAsymptotics/PermutationOrbitHeadSection.lean), [Non2SchurPermutationSection](SymmetricSubgroupAsymptotics/Non2SchurPermutationSection.lean), [Non2SchurPermutationBranch](SymmetricSubgroupAsymptotics/Non2SchurPermutationBranch.lean), [TraceyBinaryOrbitInput](SymmetricSubgroupAsymptotics/TraceyBinaryOrbitInput.lean), [TraceyBinaryFormulaInput](SymmetricSubgroupAsymptotics/TraceyBinaryFormulaInput.lean), [TraceyBinaryFiveSixteenths](SymmetricSubgroupAsymptotics/TraceyBinaryFiveSixteenths.lean), [Non2SchurTraceyBranch](SymmetricSubgroupAsymptotics/Non2SchurTraceyBranch.lean), [Non2SchurRowCertificates](SymmetricSubgroupAsymptotics/Non2SchurRowCertificates.lean), [Non2CoupledSchurNumerics](SymmetricSubgroupAsymptotics/Non2CoupledSchurNumerics.lean), [Non2UnipotentSection](SymmetricSubgroupAsymptotics/Non2UnipotentSection.lean), [PermutationBinaryFourAugmentation](SymmetricSubgroupAsymptotics/PermutationBinaryFourAugmentation.lean), [PermutationBinaryFourNonbinary](SymmetricSubgroupAsymptotics/PermutationBinaryFourNonbinary.lean), [Non2ResidualOrbitCapacity](SymmetricSubgroupAsymptotics/Non2ResidualOrbitCapacity.lean), [Non2SectionCapacity](SymmetricSubgroupAsymptotics/Non2SectionCapacity.lean), [Non2OriginalFusion](SymmetricSubgroupAsymptotics/Non2OriginalFusion.lean) | Proves the exact actual-row identity `(h*d)*r=L-t`, proves every nonfixed binary row has `h*d≥2`, and identifies equality as `h=2`, `d=1` with a four-element Schur division ring. It retains the literal original action kernel and proves that kernel fixes both the full isotypic socle component and the mixed invariant/isotypic subspace pointwise. A nonzero fixed vector in a simple row is now proved to force the whole row fixed; consequently the literal invariant and nonfixed isotypic subspaces are disjoint and the actual mixed carrier has dimension exactly `t+h*m`. Thus its physical-size budget follows from the ambient section dimension and is no longer an independent input. The arbitrary-group orbit filtration pulls this literal carrier back through the actual surjective permutation section and adds local transitive head caps across the exact kernel orbits. The visible binary Tracey formula retains the separate soluble central-binomial/binary-part bounds and the nonsoluble largest-prime-power bound, proves the earlier half and three-eighths orbit interface, and pulls the fixed space of any quotient section back through its actual preimage. In the product-degree-two row, the original action is linear over its four-element Schur ring and has nontrivial image in its rank-one general linear group, hence image exactly `C3`; its kernel has one or three orbits, all of length at least eight at original degree at least 24. In the faithful row, parity excludes Schur rank one; below product degree nine the only surviving profile has product degree eight, where the original group embeds in `GL₂(4)` and its order divides `180`. The exact formula then proves both the global `11/32` fixed bound and the degree-eight `1/5` bound. Thus every structural and numerical premise of the four-way Schur branch follows from original even degree at least 24 and the single visible published Tracey input. The canonical equivariant map to every retained central quotient now composes with the original permutation-section epimorphism, so the closed Schur theorem automatically supplies every nonfixed-row certificate needed by the section-capacity theorem. The sharp `5/16` fixed budget is also proved from the exact formula in every degree outside odd part three; its sole remaining literature surface is separately named as the precise head consequence of Tracey's minimally-transitive `3*2^a` result. All subsequent real arithmetic, supremum passage, retained cut selection, `47/48` capacity cost, and `s/768` fusion reserve are proved. The exact preimage of the invariants after quotienting by all original invariants has the retained dimension `t+ell`; every original group element squares to the identity on it, so the literal terminal binary residual fixes it. In a faithful transitive nonbinary action, every residual orbit has size at least three and has nonbinary permutation image. The exact Tracey formula gives the `3/8` head bound away from degree four. At degree four, head at least two forces the literal augmentation hyperplane, while an order-three element in the nonbinary orbit image has fixed space of dimension at most one there. Thus the residual-orbit caps and the global `3/8` unipotent budget are proved internally. The complete section-capacity theorem now has only the two precisely named Tracey literature inputs at its boundary, together with the original faithful transitive nonbinary action and permutation-section quotient data. The resulting cut is packaged as a counting-ready original-weight fusion certificate: its shifted degree is twice an integer marker degree, its prefix is strictly smaller than the original physical width, its gap is at least `s/768`, and its common-source moments and arbitrary-predicate survival envelope retain the unchanged nonsplit extension. A complete physical first-moment theorem allows distinct quotient groups, sections, cuts, faithful top covers and extension charts on every literal normal axis, then sums them with the original action normalizer and their exact shifted subgroup-count rows. |
| [Non2OriginalFusionDirect](SymmetricSubgroupAsymptotics/Non2OriginalFusionDirect.lean), [Non2OriginalFusionAggregate](SymmetricSubgroupAsymptotics/Non2OriginalFusionAggregate.lean) | Installs the retained nonbinary certificate into one exact finite-menu physical recurrence. The complete row is forward, exponentially decaying and eventually contractive while every action, normal axis, quotient, extension chart and top cover remains literal. The retained cut also gives the stronger marker bound 32r≤21s; combined with gap e≥s/768, the exact varying-width kernel and the explicit original-weight hypothesis Σ D/a≤2^(s²/32+H) yield the aggregate bound O(2^(-3n/512)). The physical cover and this weighted menu-mass inequality remain explicit obligations. |
| [BinaryPairNon2OriginalFusion](SymmetricSubgroupAsymptotics/BinaryPairNon2OriginalFusion.lean), [Non2OriginalFusionFaithfulCover](SymmetricSubgroupAsymptotics/Non2OriginalFusionFaithfulCover.lean), [Non2OriginalFusionPayloadSelection](SymmetricSubgroupAsymptotics/Non2OriginalFusionPayloadSelection.lean), [Non2OriginalFusionOwnerBridge](SymmetricSubgroupAsymptotics/Non2OriginalFusionOwnerBridge.lean), [BinaryPairNon2OwnerOutcome](SymmetricSubgroupAsymptotics/BinaryPairNon2OwnerOutcome.lean) | For every literal normal axis `N`, the exact section `K/(K ∩ N)` is acted on by `U/(K ⋁ N)`. The unchanged non-2 pair top `U/K` is used as a faithful surjective cover: fixed spaces, the retained annihilator, quotient fixed-space dimension and Schur capacity descend to the actual quotient. This constructs the complete original-extension payload without assuming `N ≤ K`, retaining the certificate, quotient, extension chart and common-source moment cover together. An axis may instead carry a proof that all its Goursat reconstructions are physically earlier-owned; residual disjointness then gives an empty surviving-epimorphism fibre and the exact contractive recurrence. The final adapter converts this structural pair-axis-or-earlier-owner alternative directly into the counting outcome using only the two named Tracey inputs. |
| [BinaryPairFrameTransport](SymmetricSubgroupAsymptotics/BinaryPairFrameTransport.lean), [Non2UnipotentPrefixFiniteMenu](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixFiniteMenu.lean), [Non2UnipotentPrefixOwnerRecognition](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixOwnerRecognition.lean), [Non2UnipotentPrefixPhysicalCover](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixPhysicalCover.lean), [Non2UnipotentPrefixPhysicalOwner](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixPhysicalOwner.lean), [Non2UnipotentPrefixPhysicalEstimate](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixPhysicalEstimate.lean), [Non2UnipotentPrefixPhysicalForwardEstimate](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixPhysicalForwardEstimate.lean), [Non2UnipotentPrefixResidualClosure](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixResidualClosure.lean), [Non2UnipotentPrefixOutsidePartition](SymmetricSubgroupAsymptotics/Non2UnipotentPrefixOutsidePartition.lean), [Non2PreE7PhysicalFrontier](SymmetricSubgroupAsymptotics/Non2PreE7PhysicalFrontier.lean), [Non2PreE7NumericalClosure](SymmetricSubgroupAsymptotics/Non2PreE7NumericalClosure.lean), [Non2PreE7MenuMassAggregation](SymmetricSubgroupAsymptotics/Non2PreE7MenuMassAggregation.lean), [Non2PreE7PairPayload](SymmetricSubgroupAsymptotics/Non2PreE7PairPayload.lean), [Non2PreE7PairFiniteMenu](SymmetricSubgroupAsymptotics/Non2PreE7PairFiniteMenu.lean), [Non2PreE7ResidualPairMenu](SymmetricSubgroupAsymptotics/Non2PreE7ResidualPairMenu.lean), [Non2PreE7ResidualPairPartition](SymmetricSubgroupAsymptotics/Non2PreE7ResidualPairPartition.lean), [Non2PreE7NonPairPhysicalFrontier](SymmetricSubgroupAsymptotics/Non2PreE7NonPairPhysicalFrontier.lean), [Non2PreE7NonPairNumericalClosure](SymmetricSubgroupAsymptotics/Non2PreE7NonPairNumericalClosure.lean), [Non2PreE7NonPairConcreteInterface](SymmetricSubgroupAsymptotics/Non2PreE7NonPairConcreteInterface.lean), [Non2PreE7NonPairMenuMassAggregation](SymmetricSubgroupAsymptotics/Non2PreE7NonPairMenuMassAggregation.lean) | Proves that every literal pair kernel is a 2-group, hence the original source is binary exactly when its faithful pair top is binary. Pair frames transport through actual source-point relabellings; the transported partner involution is the conjugate physical pairing and the top range is unchanged. The selected UP pair counts `24,32,48,64,96,128,192,256` form a finite conjugacy-class action menu, with frame existence retained propositionally so auxiliary frame choices add no multiplicity. A literal selected orbit enters the exact last first-owner physical cell. The recognition interface is specialized to the canonical payload built from that frame. The complete E7-UP-H/C predicate implements the archived ANY-hot-before-cold priority, is degree-natural, recognizes every checked `47s/48` cut, makes every local residual Goursat family empty, and proves that no noncritical subgroup with a selected UP pair orbit can be first-owned by the appended residual branch. Its hot/cold union is exactly the certified physical family; every displayed reconstruction enters the fixed canonical family without an added pointing factor. Summing the arbitrary-axis payloads over the complete finite action/normal menu gives the exact original-weight shifted recurrence, an exponentially small row, and a complete `ExponentialForwardEstimate` with zero scalar. The orbitwise post-E7 alphabet records binary, natural-`S3`, or selected-UP alternatives on every actual orbit. Removing the selected alternative yields the complete `Fits` predicate, so an outside-`Fits` residual is impossible, every marked O03 residual embeds unchanged in the existing repeated-marker owner, and the marker-free O02 residual is empty by the literal `O^2` theorem, including proper subdirect products. The outside frontier splits exactly into the post-alphabet sector, which injects unchanged into E7 and has a complete forward estimate, and the complementary pre-E7 unresolved sector. Every pre-E7 subgroup is now covered by a selected violating orbit whose conjugacy-class index retains the proof that no selected UP pair frame exists. Its exact subtype cardinality and restricted complete-source constructor remove all post-E7 action cells. A residual pre-E7 action which still has a pair system now carries the universal arbitrary-normal-axis payload on its literal representative; the selected eight widths are proved empty in that restricted index. Any finite family of the remaining widths has an exact physical union, original-weight recurrence, exponentially decaying row and complete forward estimate. Instantiating this consumer at `384,768,1536,3072` supplies the closed consumer for the four residual pair-width sectors identified by the action exhaustion; formal coverage by the complete exhaustion is still part of the remaining integration. The exact pre-E7 family is partitioned again at this physical union, which is injected unchanged into the paid pair row, so the exported T1 and `AllTargets` boundary now asks only for the non-pair complement. On each other retained normal axis, the numerical closure uses the exact earlier-owner envelope or an annihilator-aware reversible cell, charges the retained flag and Yoneda fibre jointly, and preserves coefficient one on the owned branch; a quotient comparator is one sufficient way to construct that envelope. The menu aggregation derives the complete polynomial/subquadratic mass from the published labelled transitive-action count and one uniform bound for each literal axis-envelope entry divided by its original normalizer; the fixed first-owner labels cost only a constant factor. Its constructor supplies the exact numerical certificate with no second action-counting premise. The resulting pre-E7 estimate combines with the paid E7 and residual-pair rows once the remaining action consumers provide their owner-envelope, retained-cell, entry-bound and parameter data. The O03 embedding is converted into the complete checked even and odd normalized inequalities: positive marker defect uses the strict ordinary row, while zero defect uses the current and predecessor binary-error coefficients. Residual recognition introduces no second scalar or forward row. |
| [Non2PreE7C3Partition](SymmetricSubgroupAsymptotics/Non2PreE7C3Partition.lean), [Non2PreE7NoPairNoC3PhysicalFrontier](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3PhysicalFrontier.lean), [Non2PreE7NoPairNoC3NumericalClosure](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3NumericalClosure.lean), [Non2PreE7NoPairNoC3ConcreteInterface](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3ConcreteInterface.lean), [Non2PreE7NoPairNoC3MenuMassAggregation](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3MenuMassAggregation.lean), [Non2PreE7NoPairNoC3EarlierOwnerCatalogue](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3EarlierOwnerCatalogue.lean), [T1RelativeClosure](SymmetricSubgroupAsymptotics/T1RelativeClosure.lean) | Transports the complete regular-`C3` physical family to every ambient `Fin n`, proves exact cardinal preservation, and partitions it out of the non-pair pre-`E7` residual. The complement is retained through the selected-orbit chart as a relabelling-invariant complete-source predicate; the resulting first-owner cells literally cover the no-pair/no-`C3` subgroup set and feed the local-to-global physical bound. The numerical closure and concrete interface turn the structural owner envelope, rejected-axis retained cells and uniform menu certificate directly into the narrowed forward estimate, while requiring their exact joint flag-times-Yoneda capacity. `T1RelativeClosure` threads both that multiplicative package and the certificate-retaining additive-tail package through `T1 → T2`, `T1 → T3` and `AllTargets`. The catalogue fixes the exact 53-family overlay precedence from `IT` through `JCHAR`, leaving `DEG9all` in its separate degree-nine partition; labels alone are explicitly not subgroup predicates. This is the strongest current T1 boundary. |
| [Non2PreE7NoPairNoC3EarlierComparators](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3EarlierComparators.lean), [Non2PreE7NoPairNoC3AdditiveTailInterface](SymmetricSubgroupAsymptotics/Non2PreE7NoPairNoC3AdditiveTailInterface.lean), [Non2PreE7ComparatorAbelianTowerTemplate](SymmetricSubgroupAsymptotics/Non2PreE7ComparatorAbelianTowerTemplate.lean) | Defines each earlier owner as existence of a family-specific comparator certificate on a literal retained orbit and proves degree naturality by transporting that same orbit. The certified physical cover displays a family-bearing orbit whenever one exists; mismatched owner/action cells are proved empty, and only the terminal residual branch may use an arbitrary violating orbit. Thus no precedence theorem enters a family bound, while the residual lane may soundly use absence of every family orbit. The audited 53 families are partitioned into the five reusable certificate templates of sizes `9,16,8,5,15`, with marked-`C4` and binary-rank-tail obligations recorded separately. The common certificate retains its actual comparator group, faithful action and per-axis additive envelope. A selector installs the real certificate on matching cells, zero on mismatches, and an independently supplied retained-cell envelope on the terminal cells. The cover-parametric additive interface accepts `(C_N 2^(eta*b)) Z_J(R) + T_N 2^(theta*b)`: only the first term enters the quotient moment, while the source-independent term becomes a pure cold row under its own menu-mass and exponent-gap hypotheses. The comparator/abelian-layer template works directly on the literal quotient `U/N`; its retained restriction flags and Yoneda fibres are charged jointly by one tower-capacity inequality and it produces the common action certificate without a carrier change or an owner-order premise. Its additive form injects an exhaustive main/tail split into the disjoint sum of the two counted families, applies the tower only to the main branch, and preserves the second branch as a pure cold row. |
| [Non2PreE7SmallAdditiveBasicNumerics](SymmetricSubgroupAsymptotics/Non2PreE7SmallAdditiveBasicNumerics.lean), [Non2PreE7SmallAdditiveRecoveredNumerics](SymmetricSubgroupAsymptotics/Non2PreE7SmallAdditiveRecoveredNumerics.lean), [Non2PreE7SaprimDegreeFive](SymmetricSubgroupAsymptotics/Non2PreE7SaprimDegreeFive.lean), [Non2PreE7SaprimBinaryAffine](SymmetricSubgroupAsymptotics/Non2PreE7SaprimBinaryAffine.lean), [Non2PreE7SaprimOddCyclicAffine](SymmetricSubgroupAsymptotics/Non2PreE7SaprimOddCyclicAffine.lean), [Non2PreE7SaprimOddLargeAffine](SymmetricSubgroupAsymptotics/Non2PreE7SaprimOddLargeAffine.lean), [Non2PreE7SaprimExceptionalOdd](SymmetricSubgroupAsymptotics/Non2PreE7SaprimExceptionalOdd.lean), [Non2PreE7S3LocalAdditive](SymmetricSubgroupAsymptotics/Non2PreE7S3LocalAdditive.lean), [Non2PreE7SmallAdditiveNumericalInstances](SymmetricSubgroupAsymptotics/Non2PreE7SmallAdditiveNumericalInstances.lean) | Completes literal-axis coefficient totals for DIH, natural S4, A4W2, both LIN modes, all finite soluble primitive-affine SAPRIM rows except the separately owned natural F20 action, S3TWO, S3CYCL, S3SYL, and all three TF modes. SAPRIM includes the degree-nine `P × C₂` comparison and every degree-twenty-five central-`C₄` stratum, while retaining the exact degree-27 complement ceiling `q = 78`. The three local-S3 owners share one theorem transporting their audited complete all-normal additive bounds to every literal axis; Lean verifies their `(w,v)` pairs `(12,10)`, `(9,6)`, `(9,6)` and the tail slopes `log₂(3)/3`, `log₂(3)/3`, `log₂(3)/2`. One typed dispatcher sends every completed predicate through the ordinary numerical package and into the concrete rank-tail owner sum consumed by T1. |
| [Non2PreE7S3ExceptionalEnvelope](SymmetricSubgroupAsymptotics/Non2PreE7S3ExceptionalEnvelope.lean), [FiniteComparatorListMoment](SymmetricSubgroupAsymptotics/FiniteComparatorListMoment.lean), [FusionFiniteComparatorListTransfer](SymmetricSubgroupAsymptotics/FusionFiniteComparatorListTransfer.lean), [Non2PreE7FiveExceptional](SymmetricSubgroupAsymptotics/Non2PreE7FiveExceptional.lean), [Non2PreE7ExceptionalSmallRankTailBridge](SymmetricSubgroupAsymptotics/Non2PreE7ExceptionalSmallRankTailBridge.lean) | Completes S3EXC and fiveExc as source-facing numerical owners. S3EXC retains its correlated complete all-normal inequality and covers every historical pure-tail, additive and multiplicative branch through one padded comparator envelope. fiveExc keeps the literal list consisting of the top and every invariant line quotient, including repeated abstract isomorphism types. Jensen proves that the arithmetic mean of any finite degree-`v` comparator list has moment at most `subgroupCount (b+q*v)`. The physical transfer applies this statistic directly, while the affine error remains a separate cold row. Lean verifies the three historical parameter rows `(w,v,cutoff)=(10,8,9/8),(15,12,13/8),(20,16,9/4)` and their tail windows. Both packages enter the concrete rank-tail owner sum used by the final T1 source exhaustion. |
| [Non2PreE7Inv12AllJointSource](SymmetricSubgroupAsymptotics/Non2PreE7Inv12AllJointSource.lean) | Completes the numerical INV12all source without maximizing its binary and ternary ranks separately. Every literal normal quotient retains an onto projection to its actual transitive degree-nine `3`-group and the full fibre of that projection. One support integer `c` for the original source simultaneously satisfies `4 d₃(J) ≤ b+c` and `2 d₂(ker θ)+3c ≤ b` for every retained top map. Combining the degree-nine character recurrence and all binary fibres before discarding `c` gives the uniform slope `43/30`; the finite all-normal coefficient is paid once through the complete-source comparator. The resulting `.inv12All` package enters the final rank-tail owner sum directly. |
| [Non2PreE7B6Y1Menu](SymmetricSubgroupAsymptotics/Non2PreE7B6Y1Menu.lean), [Non2PreE7B6Y1Secondary](SymmetricSubgroupAsymptotics/Non2PreE7B6Y1Secondary.lean), [Non2PreE7RankTailNumericalCatalogue](SymmetricSubgroupAsymptotics/Non2PreE7RankTailNumericalCatalogue.lean), [Non2PreE7RankTailNumericalRows](SymmetricSubgroupAsymptotics/Non2PreE7RankTailNumericalRows.lean), [Non2PreE7RankTailMainNumerics](SymmetricSubgroupAsymptotics/Non2PreE7RankTailMainNumerics.lean), [Non2PreE7RankTailSecondaryNumerics](SymmetricSubgroupAsymptotics/Non2PreE7RankTailSecondaryNumerics.lean), [Non2PreE7RankTailNumericalClosure](SymmetricSubgroupAsymptotics/Non2PreE7RankTailNumericalClosure.lean), [Non2PreE7RankTailOwnerOrJointTopClosure](SymmetricSubgroupAsymptotics/Non2PreE7RankTailOwnerOrJointTopClosure.lean), [Non2PreE7RankTailSourceDichotomyClosure](SymmetricSubgroupAsymptotics/Non2PreE7RankTailSourceDichotomyClosure.lean) | Integrates all three correlated binary rank-tail families into the exact first-owner recurrence. B6 and Y1 use their literal fixed-width menus, so arbitrary action-dependent constants are summed directly at widths twelve and eight; their cold and hot contributions combine with the already-closed ordinary/SNS2 secondary row. The disjoint physical catalogue now contains ordinary, B6, Y1, SNS2 and terminal cells, with a proved subquadratic main menu and a complete forward estimate. The publication-facing T1 boundary asks for an actual ordinary/B6/Y1/SNS2 source certificate or annihilator-aware joint/Yoneda top data only after all four owner sectors have been tested; existing joint cells apply unchanged because the new terminal predicate only removes sources. Historical owner labels alone cannot inhabit this boundary. |
| [Non2PreE7CompleteSourceComparator](SymmetricSubgroupAsymptotics/Non2PreE7CompleteSourceComparator.lean), [Non2PreE7SemisimpleCompleteSourceInstances](SymmetricSubgroupAsymptotics/Non2PreE7SemisimpleCompleteSourceInstances.lean), [Non2PreE7CompleteSourceRankTailBridge](SymmetricSubgroupAsymptotics/Non2PreE7CompleteSourceRankTailBridge.lean) | Installs a comparator bound proved directly for the complete sum over all literal normal axes, preserving its correlation through the physical hot/cold transfer. The semisimple outer-fibre constructor pays its one simple-factor product once; it does not assign the complete quotient sum to every axis and sum it again. Existing `SS` and `SNS` sources are routed through this exact complete-source path in the ordinary T1 dispatcher, and the same constructor is available for compressed-quotient families such as `COMP`. Complete-source witnesses enter the final rank-tail T1 exhaustion boundary directly, without conversion to pointwise normal-axis estimates. |
| [Non2PreE7SemisimpleCompression](SymmetricSubgroupAsymptotics/Non2PreE7SemisimpleCompression.lean), [Non2PreE7SemisimpleCompressionClosure](SymmetricSubgroupAsymptotics/Non2PreE7SemisimpleCompressionClosure.lean) | Proves the numerical half of complete semisimple compression on a literal action. A semisimple normal chart and a faithful quotient action of degree at most half the even width produce a concrete `.comp` owner source at the final T1 boundary. The published uniform outer-factor input supplies the log-squared coefficient bound, and the normal-axis correlation is retained. The post-compression T1 theorem now asks on every retained action for that structural compression witness, an already integrated owner source, or an annihilator-aware Yoneda-top family. |
| [PermutationalWreathProduct](SymmetricSubgroupAsymptotics/PermutationalWreathProduct.lean), [SemisimpleSubdirectChart](SymmetricSubgroupAsymptotics/SemisimpleSubdirectChart.lean), [PermutationalWreathQuotient](SymmetricSubgroupAsymptotics/PermutationalWreathQuotient.lean), [Non2PreE7ExactBlockCompression](SymmetricSubgroupAsymptotics/Non2PreE7ExactBlockCompression.lean), [ActualBlockWreathEmbedding](SymmetricSubgroupAsymptotics/ActualBlockWreathEmbedding.lean), [Non2PreE7ActualBlockCompression](SymmetricSubgroupAsymptotics/Non2PreE7ActualBlockCompression.lean), [Non2PreE7LocalSemisimpleCompression](SymmetricSubgroupAsymptotics/Non2PreE7LocalSemisimpleCompression.lean), [Non2PreE7ActualBlockCompressionClosure](SymmetricSubgroupAsymptotics/Non2PreE7ActualBlockCompressionClosure.lean), [Non2PreE7PrimitiveBlockExhaustion](SymmetricSubgroupAsymptotics/Non2PreE7PrimitiveBlockExhaustion.lean) | Retains an arbitrary faithful block-top action and constructs its quotient after applying a local compression map. Exact-component fullness makes every block-coordinate image normal. A Scott-style induction constructs the literal product-of-simple-groups chart for the intersection, including nonabelian proper subdirect kernels, diagonal strips, omitted factors and the empty product. The standard faithful wreath embedding and its fullness witness are proved from every actual equivariant block system. A local primitive theorem now supplies only a literal normal semisimple `E`, a faithful action of `L/E`, and `2u ≤ evenWidth r`; Lean constructs the onto local permutation image and proves its kernel is exactly `E`. On an original minimal block this automatically gives the global compressed action on exactly `u * s` points, with `2 * u * s ≤ evenWidth (r * s)`. Lean now also performs the primitive/imprimitive split and chooses an actual minimal block in the imprimitive case. The remaining T1 exhaustion is therefore local on a primitive original action or the primitive component of that chosen block, versus the already integrated affine/soluble/exceptional source and Yoneda alternatives. |
| [PrimitiveSemisimpleCompressionProfile](SymmetricSubgroupAsymptotics/PrimitiveSemisimpleCompressionProfile.lean), [PrimitiveSemisimpleOuterLogExhaustion](SymmetricSubgroupAsymptotics/PrimitiveSemisimpleOuterLogExhaustion.lean), [PrimitiveSemisimpleBoundedIndexExhaustion](SymmetricSubgroupAsymptotics/PrimitiveSemisimpleBoundedIndexExhaustion.lean), [PrimitiveBoundedIndexReceipt](SymmetricSubgroupAsymptotics/PrimitiveBoundedIndexReceipt.lean), [PrimitiveBoundedIndexCatalogueBridge](SymmetricSubgroupAsymptotics/PrimitiveBoundedIndexCatalogueBridge.lean) | Formalizes the uniform numerical half of nonaffine primitive compression. For socle profile `(a, ell, q)`, `4q ≤ ell²` propagates to `2aq ≤ ell^a` for every `a ≥ 2`; the `a=1`, `ell≥30` branch uses `2q≤ell`. Together with the literal semisimple chart, faithful quotient action and core-free index lower bound, these produce the local compression certificate. Lean performs the exhaustive split: every multiple-factor profile and every one-factor profile with `ell ≥ 30` closes uniformly. In the remaining one-factor range `ell < 30`, the profile already contains the chart and faithful quotient action, so the finite primitive package supplies only the integer inequality `2q ≤ r`; Lean turns it into the exact local compression datum. The generated, kernel-checked receipt records this inequality for all 116 simple-nonabelian-socle primitive catalogue rows in degrees 5 through 29. The catalogue bridge asks only for a locator and equality of its degree and quotient order with the literal profile; it then transports the checked inequality and exports the T1 endpoint. |
| [PrimitiveOuterOrderNumerics](SymmetricSubgroupAsymptotics/PrimitiveOuterOrderNumerics.lean) | Converts the natural published input `q ≤ 3 log₂ ell` into both exact primitive-compression inequalities: `4q ≤ ell²` for `ell ≥ 5` and `2q ≤ ell` for `ell ≥ 30`. The small intervals are kernel checked and the tails use exact dyadic induction. `PrimitiveSemisimpleOuterLogProfile` retains the single literature bound and constructs the compression profile and uniform certificates. |
| [FusionNumerics](SymmetricSubgroupAsymptotics/FusionNumerics.lean), [FusionPointingRatio](SymmetricSubgroupAsymptotics/FusionPointingRatio.lean), [FusionCold](SymmetricSubgroupAsymptotics/FusionCold.lean) | Complete hot-moment inequality and rounded square, exact both-parity pointing ratio, original cold divisors, and exponential finite-menu cold sums. |
| [FusionHotBenchmark](SymmetricSubgroupAsymptotics/FusionHotBenchmark.lean), [FusionHot](SymmetricSubgroupAsymptotics/FusionHot.lean), [FusionZeroWidth](SymmetricSubgroupAsymptotics/FusionZeroWidth.lean) | Elementary all-pairs benchmark normalization, quadratic hot-kernel decay relative to an explicit coarse counting input, and the zero-width moment case. |
| [BinaryTransport](SymmetricSubgroupAsymptotics/BinaryTransport.lean), [BinaryTransportFibreProducts](SymmetricSubgroupAsymptotics/BinaryTransportFibreProducts.lean) | Reversible simultaneous transport of actual subgroups through arbitrary proper subdirect carriers, literal axes, full projections, and unchanged original fixed weights. |
| [BinaryCoverage](SymmetricSubgroupAsymptotics/BinaryCoverage.lean), [FiniteGroupCertificates](SymmetricSubgroupAsymptotics/FiniteGroupCertificates.lean) | Universal p-group action/normal coverage from local closure, and soundness of finite Cayley and homomorphism-graph certificates. The actual finite closure checks are separate obligations. |
| [BinaryCheckedTransport](SymmetricSubgroupAsymptotics/BinaryCheckedTransport.lean), [BinaryPermutationBlocks](SymmetricSubgroupAsymptotics/BinaryPermutationBlocks.lean), [BinaryExceptionalCarriers](SymmetricSubgroupAsymptotics/BinaryExceptionalCarriers.lean) | Four literal exceptional charts, exact original kernels and quotient maps, reversible transport with any exterior, and actual block projections with positive noncritical support. The degree-sixteen carrier remains the proper joint image. |
| [BinaryNormalTransport16](SymmetricSubgroupAsymptotics/BinaryNormalTransport16.lean) | Every normal subgroup of the original 16T1086 action either has a local pair certificate or is the exact chart axis. Transport reconstructs the original subgroup with its full exterior and carries the action and normal subgroup through the same ambient conjugacy. |
| [BinarySylowCoverage](SymmetricSubgroupAsymptotics/BinarySylowCoverage.lean), [BinaryWreathRoots](SymmetricSubgroupAsymptotics/BinaryWreathRoots.lean), [BinaryMenuRoots](SymmetricSubgroupAsymptotics/BinaryMenuRoots.lean), [BinaryConjugacyTransport](SymmetricSubgroupAsymptotics/BinaryConjugacyTransport.lean) | Global coverage from local representative edges; structurally proved Sylow roots bound to all four literal menu roots; simultaneous original action/normal/quotient conjugacy and unchanged normalizer weights. |
| [FusionGoursat](SymmetricSubgroupAsymptotics/FusionGoursat.lean), [FusionGoursatCount](SymmetricSubgroupAsymptotics/FusionGoursatCount.lean), [FusionLabelCounting](SymmetricSubgroupAsymptotics/FusionLabelCounting.lean), [FusionOrbitPointing](SymmetricSubgroupAsymptotics/FusionOrbitPointing.lean), [FusionOrbitDeletion](SymmetricSubgroupAsymptotics/FusionOrbitDeletion.lean), [FusionPhysicalCount](SymmetricSubgroupAsymptotics/FusionPhysicalCount.lean) | Reversible actual Goursat encoding, complete surviving literal-axis/source sum, intrinsic orbit extraction, and the original factorial/normalizer divisor proved by labelled-frame fibres. |
| [CompleteQuotientMoment](SymmetricSubgroupAsymptotics/CompleteQuotientMoment.lean) | A faithful permutation action of any finite quotient target turns every simultaneous tuple of quotient maps from one complete source into one subgroup on the source points plus one target block per map. Exact coordinate marginals recover every map, so the coding is injective while retaining distinct normal axes. Consequently the full $q$th moment of the complete quotient-map count is at most the subgroup count in degree $b+qs$. |
| [FusionCompleteSourceEnvelope](SymmetricSubgroupAsymptotics/FusionCompleteSourceEnvelope.lean) | Sums branch-specific incidence or capacity bounds over every literal normal axis while keeping one unchanged complete source and comparator weight. The total coefficient is the actual sum of the axis coefficients, and a common exponential lift factor is charged only once. |
| [FusionQuotientComparator](SymmetricSubgroupAsymptotics/FusionQuotientComparator.lean) | Turns an exact equivalence from an original quotient axis to one literal quotient of a finite comparator into a coefficient-one bound by that comparator's complete quotient weight. A family of such witnesses bounds the complete-source sum by the literal number of original normal axes, with no automorphism or quotient-type multiplicity. |
| [FusionOwnerCapacityEnvelope](SymmetricSubgroupAsymptotics/FusionOwnerCapacityEnvelope.lean) | Combines a direct earlier-owner bound by the common complete-quotient weight with the retained-annihilator alternative axis by axis. Earlier-owned axes contribute exactly one before extracting the common exponential lift; only rejected axes pay their supplied capacity coefficient. A literal quotient comparator remains a sufficient adapter, but is no longer required from owner theorems proved by a direct envelope. The resulting mixed coefficient feeds the full non-2 first-owner forward theorem directly. |
| [FusionCarrierOwnerCapacity](SymmetricSubgroupAsymptotics/FusionCarrierOwnerCapacity.lean) | Sends every unowned literal normal axis through a checked reversible permutation carrier while retaining the same complete exterior subgroup, inverse-original survival predicate and quotient-map multiplicity. An intrinsic carrier envelope then discharges the exact owner-or-capacity premise and sums over all original axes without weakening earlier owners. |
| [FusionCarrierIncidence](SymmetricSubgroupAsymptotics/FusionCarrierIncidence.lean) | Converts a direct map from accepted carrier epimorphisms to complete quotient comparators into the required intrinsic envelope by a uniform fibre bound. Its retained-cell form keeps an arbitrary finite radical or transgression-annihilator flag in every cell and charges the exact flag count before the quotient moment; reversible transport returns the bound to the same original literal axis. Supplying these cells on every rejected axis now feeds the full general non-2 forward estimate without a raw cardinal-envelope premise. |
| [FusionCarrierSubdirectCapacity](SymmetricSubgroupAsymptotics/FusionCarrierSubdirectCapacity.lean) | Realizes every carrier epimorphism as a literal full subdirect pullback of the carrier and the unchanged complete source. Its first axis is exactly the checked carrier kernel, and the full joint character, derived-normal, invariant-radical and restricted-`H²` transition applies to that same core, including nonabelian proper subdirect cores and negative first marks. The intrinsic core embeds onto the exact ambient quotient graph and uniquely recovers its epimorphism. Adjoining that core to any comparator gives an injective exact cell with one-point fibres, so later signature cells can be coarsened only through an explicit fibre bound. |
| [FusionCarrierAnnihilatorYonedaIncidence](SymmetricSubgroupAsymptotics/FusionCarrierAnnihilatorYonedaIncidence.lean) | Proves annihilator-aware Yoneda incidence for reversible carrier cells. A cell is the complete quotient map `J ↠ Q ↠ R/M` through a top `τ` fixed by the axis carrier, never by the epimorphism, together with a retained flag read off the literal pullback core `fusionCarrierSubdirectGraph`. At one abelian layer, fixing the bottom map and the literal restriction value leaves only inflated cocycles, `|Z¹(B,A)| = |B¹||H¹|`; the flags range over the literal restriction image, where the transgression annihilator is encoded, and are never enlarged to all equivariant kernel maps. `AbelianYonedaTower` multiplies these along a tower of abelian layers, giving `|Flag| · Z_Yoneda ≤ ∏ |im res_ℓ| |A_ℓ| |H¹_ℓ|`; empty obstruction fibres contribute zero. `PreE7NoPairNoC3RetainedCellData.ofAbelianYonedaTowers` installs this on the frozen pre-E7 interface from an explicit dichotomy: each axis is owned, or its carrier quotient has an abelian-layer tower to a fixed comparator top. Nonabelian chief factors must therefore be owned. |
| [FusionCarrierAnnihilatorYonedaFixture](SymmetricSubgroupAsymptotics/FusionCarrierAnnihilatorYonedaFixture.lean) | Regression fixture on the sign carrier of `S₃`. The literal pullback core is nonabelian, has both projections full, is not the direct product of its projections, and has the literal sign kernel as its first axis. One abelian layer reaches the trivial top; the retained flag is read off the literal core and the incidence bound holds with the tower capacity. |
| [Non2PreE7ResidualAbelianTowerChoice](SymmetricSubgroupAsymptotics/Non2PreE7ResidualAbelianTowerChoice.lean) | Bridges the retained-cell theorem to the certified final owner. A reversible carrier and an abelian Yoneda tower on every literal terminal normal axis, together with one joint-capacity inequality, produce the exact terminal `PreE7NoPairNoC3AxisComparatorChoice`; assembling these choices yields the cover-parametric additive axis datum. The original source, terminal predicate, normal axis, restriction flags and complete comparator moment are preserved. |
| [FusionCarrierWeightedIncidence](SymmetricSubgroupAsymptotics/FusionCarrierWeightedIncidence.lean) | Replaces the product of a flag count and one worst-case fibre bound by a finite sum of flag-dependent fibre costs. The resulting reversible-carrier theorem preserves the correlation between a selected top and the Yoneda capacity below that top while retaining the same literal complete quotient map. |
| [FusionCarrierYonedaTopFamily](SymmetricSubgroupAsymptotics/FusionCarrierYonedaTopFamily.lean) | Lets every accepted carrier epimorphism select a member of a finite family of actual abelian Yoneda towers. Its dependent retained flag remembers that top and its literal restriction data, and the resulting incidence pays the sum of the individual tower capacities rather than the number of tops times a worst-case tower. |
| [Non2PreE7JointTopYonedaIncidence](SymmetricSubgroupAsymptotics/Non2PreE7JointTopYonedaIncidence.lean) | Freezes the terminal original-weight obligation in its correlation-preserving form. A cell may retain its top, radical and character flags, derived-normal coordinate and restricted transgression datum; one bound on the sum of its fibre costs produces the terminal comparator choice. Both the fixed-top tower and an epimorphism-selected finite family of tops have checked constructors. Supplying the actual family and proving its numerical joint-capacity sum for every residual action remain the terminal mathematical obligations. |
| [T1JointTopCellClosure](SymmetricSubgroupAsymptotics/T1JointTopCellClosure.lean) | Threads joint terminal cells and the additive numerical certificate through the certified earlier-owner cover to `T1` and `AllTargets`. This is a conditional closure boundary: it exposes the concrete joint-cell construction and menu numerics rather than replacing them by an unverified global premise. |
| [C3PhysicalStructuralOwner](SymmetricSubgroupAsymptotics/C3PhysicalStructuralOwner.lean) | Promotes the c=1 high-state structural witness on an untouched complement orbit to a relabelling-invariant predicate of the complete physical subgroup, retaining its C3 chart with full projection onto the displayed regular $C_3$, complete complement, normal axis, strict `3/20` failure and owner witness. Fullness makes the displayed triple an actual orbit, so the owned orbit is never that triple. Under the four explicit ternary inputs, every high trivial-axis C3 state enters this owner and cannot be first-owned by the appended residual branch. |
| [C3PhysicalOwnerBranches](SymmetricSubgroupAsymptotics/C3PhysicalOwnerBranches.lean) | Splits the complete high-C3 physical owner into four degree-natural branches: ternary p-group, natural A4, degree six and degree twelve. The strict high witness proves exhaustive coverage, while first ownership permits a different checked counting theorem on each branch without duplication. |
| [C3PhysicalOwnerFusionCover](SymmetricSubgroupAsymptotics/C3PhysicalOwnerFusionCover.lean) | Proves directly from the retained strict ternary relative-head inequality that the stored owned orbit image cannot be a 2-group. It deletes that same orbit and places every classified complete high-C3 owner in the canonical general non-2 fusion family, preserving the complete complement and its outer regular-C3 block. |
| [C3PhysicalOwnerFirstFusion](SymmetricSubgroupAsymptotics/C3PhysicalOwnerFirstFusion.lean) | Strengthens that cover to the exact first-owner cells used by the general non-2 recurrence. Literal reconstruction of the deleted model transports noncriticality and first ownership of the complete physical subgroup. The action-chart-specific form keeps the selected chart visible so later consumers can transport the high normal pair to that exact retained action, without pointing multiplicity. |
| [C3PhysicalOwnerFiniteFusion](SymmetricSubgroupAsymptotics/C3PhysicalOwnerFiniteFusion.lean) | Applies the six-degree high-ternary theorem to the same retained orbit used by the first-owner chart. The c=1 audit therefore uses only widths `3,4,6,9,12,27`, packaged as a finite action index, rather than inheriting the arbitrary growing-width menu. |
| [C3PhysicalOwnerFiniteContinuation](SymmetricSubgroupAsymptotics/C3PhysicalOwnerFiniteContinuation.lean) | Forms the finite index of the six retained widths, four first owners and exact non-2 action classes. Pointwise bounds for those canonical physical cells assemble into one literal-complement recurrence; exponential decay of the finitely many local rows returns a complete forward-estimate object. This broad interface does not by itself certify that the indexed action is the orbit carrying the high pair. |
| [C3PhysicalOwnerAlignedContinuation](SymmetricSubgroupAsymptotics/C3PhysicalOwnerAlignedContinuation.lean) | Repairs the c=1 audit interface by transporting the selected normal subgroup, its strict high relative-character inequality, the full intrinsic earlier-owner witness, and the precise first-owner branch property to the exact retained action class. The complete high-C3 family is covered by this certified finite index, and local estimates on only these aligned cells assemble into the same literal-complement recurrence and exponential forward estimate. Branch-specific numerical work should use this interface. |
| [C3AlignedOwnerRefinement](SymmetricSubgroupAsymptotics/C3AlignedOwnerRefinement.lean) | Refines every aligned coarse branch intrinsically on that same literal transitive action. Degree six splits into the odd-index-two or cyclic-binary owner, and degree twelve splits into the prime-base or binary-nine owner, while the ternary p-group and natural-$A_4$ branches retain their exact structural certificates. Thus the continuation exposes precisely the six numerical consumers without finite-catalogue recognition or a detached owner disjunction. |
| [FusionAcceptedOrbitChartAt](SymmetricSubgroupAsymptotics/FusionAcceptedOrbitChartAt.lean), [FusionComplementOrbits](SymmetricSubgroupAsymptotics/FusionComplementOrbits.lean) | Fixes the quotient-orbit witness at a specified point of a full transitive fusion block, and identifies every orbit of a deleted complement image with its literal undeleted ambient orbit. The induced permutation images agree through the displayed point charts, and the second projection of the exact deleted model is exactly the complement image. |
| [FusionSourceRestriction](SymmetricSubgroupAsymptotics/FusionSourceRestriction.lean), [C1DegreeNineRankBudget](SymmetricSubgroupAsymptotics/C1DegreeNineRankBudget.lean), [C1DegreeNinePatternDeletion](SymmetricSubgroupAsymptotics/C1DegreeNinePatternDeletion.lean) | Separates the structural producer from the numerical consumer. The unique-regular-$C_3$, no-natural-$A_4$ pattern survives deletion of every nonmarker orbit and proves the invariant budget $9d_3(J)\leq2|J\text{-points}|+3$. The source-restricted fusion predicate attaches that budget to the same literal second projection consumed by the original-weight row. |
| [C3C1PatternAlignedCoverage](SymmetricSubgroupAsymptotics/C3C1PatternAlignedCoverage.lean), [C3TernaryPGroupAlignedLocal](SymmetricSubgroupAsymptotics/C3TernaryPGroupAlignedLocal.lean) | Closes the two ternary-p-group endpoints of the exact c=1 finite audit. A width-nine aligned chart enters the existing first-owner cell with its automatically produced rank budget on the same deleted model, and the sharp degree-nine row consumes only that budget. At width three, full outer $C_3$ projection would make the selected inner action a second literal regular-$C_3$ orbit, contradicting the exact source pattern. Width twenty seven retains its unrestricted row. |
| [C1TernaryPrimeBaseCanonicalBound](SymmetricSubgroupAsymptotics/C1TernaryPrimeBaseCanonicalBound.lean), [C3PrimeBaseAlignedLocal](SymmetricSubgroupAsymptotics/C3PrimeBaseAlignedLocal.lean) | Installs the internally proved A4 quotient-map estimate on the complete canonical width-twelve prime-base family. On an aligned degree-twelve high-C3 cell, an intrinsic prime-base witness now supplies the full local row unconditionally, retaining every literal normal axis and the original action normalizer; no top-map or action-recognition premise remains on this subbranch. |
| [C1DegreeNineSourcePatternRelabel](SymmetricSubgroupAsymptotics/C1DegreeNineSourcePatternRelabel.lean), [C1DegreeNineSourcePatternFusion](SymmetricSubgroupAsymptotics/C1DegreeNineSourcePatternFusion.lean) | Transports the exact one-regular-$C_3$, no-natural-A4 source pattern along every relabelling, and from a complete fusion subgroup with full outer projection to its literal source. The complete high-C3 owner set, its first-owner menu and every aligned cell predicate now retain this pattern, so no later consumer re-derives it. |
| [C3NaturalA4AlignedLocal](SymmetricSubgroupAsymptotics/C3NaturalA4AlignedLocal.lean) | Proves that the aligned natural-A4 canonical family is empty at every ambient degree: full projection would make the selected natural-A4 action a literal orbit of the complete subgroup, contradicting the retained source pattern. Its local coefficient is zero. |
| [KovacsPraegerAbelianization](SymmetricSubgroupAsymptotics/KovacsPraegerAbelianization.lean), [CoprimeSplitCharacterLabel](SymmetricSubgroupAsymptotics/CoprimeSplitCharacterLabel.lean), [CoprimeOrbitLabels](SymmetricSubgroupAsymptotics/CoprimeOrbitLabels.lean) | Records the Kovács--Praeger abelianization bound $|J/J'|\le 3^{b/3}$ (LIT-KP, Corollary p.284) as the explicit named hypothesis `KovacsPraegerAbelianizationBound`, never as an axiom. Proves the coprime labelling lemmas: onto maps to a quotient with an abelian normal $p$-subgroup of prime index $q$ are counted by the $p$-characters of the source commutator-power subgroup times target automorphisms, once one character detects the subgroup with its conjugates. |
| [DegreeSixOddIndexStructure](SymmetricSubgroupAsymptotics/DegreeSixOddIndexStructure.lean), [DegreeSixOddIndexEpiBound](SymmetricSubgroupAsymptotics/DegreeSixOddIndexEpiBound.lean) | For the transitive degree-six odd-index-two owner, bounds the onto maps from every degree-$b$ source to every literal quotient by a fixed constant times $2^{8b/15}$. The trivial axis over a base of order nine uses the literal point-stabilizer character; otherwise the base image has order at most three and either one injective ternary label applies or the quotient is abelian and the Kovács--Praeger hypothesis applies. |
| [DegreeSixBinaryBlockCoordinates](SymmetricSubgroupAsymptotics/DegreeSixBinaryBlockCoordinates.lean), [DegreeSixBinaryBlockEpiBound](SymmetricSubgroupAsymptotics/DegreeSixBinaryBlockEpiBound.lean) | Gives the same uniform $2^{8b/15}$ quotient bound for the two-by-three binary block owner, from its literal block kernel in $F_2^3$ and an element over a three-cycle of the blocks. A nontrivial shift on the kernel image admits one triple-detecting binary coordinate label; a trivial shift forces kernel image of order at most two by the coordinate sum, and the abelian quotient enters Kovács--Praeger. The closed coordinate facts are decided by evaluation. |
| [C3DegreeSixAlignedLocal](SymmetricSubgroupAsymptotics/C3DegreeSixAlignedLocal.lean) | Reruns the degree-six dichotomy on the retained high pair of an aligned cell. Both the odd-index-two and the cyclic binary-module owners feed the complete degree-six row through the full original normal menu, with constants independent of the source degree. |
| [OriginalKernelLabelRegularEmbedding](SymmetricSubgroupAsymptotics/OriginalKernelLabelRegularEmbedding.lean), [DegreeTwelveKleinCoordinates](SymmetricSubgroupAsymptotics/DegreeTwelveKleinCoordinates.lean), [C1BinaryNineRegularTop](SymmetricSubgroupAsymptotics/C1BinaryNineRegularTop.lean) | Supplies the two structural inputs of the binary-nine row without a catalogue: the regular section embedding on every original normal axis from the literal Klein block coordinates, and a top bound uniform in the source degree through the faithful nine-label image and the degree-nine rank budget. |
| [C3DegreeTwelveAlignedLocal](SymmetricSubgroupAsymptotics/C3DegreeTwelveAlignedLocal.lean) | Reruns the degree-twelve top geometry on an aligned cell. The three-by-four orientation feeds the prime-base row; the four-by-three orientation feeds the mixed binary-nine row, whose source pattern is read from the cell predicate itself. |
| [C3HighAlignedRemainingConsumers](SymmetricSubgroupAsymptotics/C3HighAlignedRemainingConsumers.lean) | Defines the four remaining intrinsic aligned consumers (natural A4, odd-index-two, cyclic binary module, binary nine), proves every aligned refinement is a closed ternary-p-group or prime-base alternative or one of them, and exports `c3HighAligned_remainingConsumers_local`: one nonnegative, exponentially decaying local row per consumer in the exact form of `c3PhysicalStructuralOwner_alignedExponentialForwardEstimate`. The companion theorem closes that continuation once ternary-p-group rows are supplied. |
| [C3HighAlignedRefinedContinuation](SymmetricSubgroupAsymptotics/C3HighAlignedRefinedContinuation.lean) | Removes the width-three ternary-p-group cells from the aligned index as an indexing artefact. The physical cover derives the exclusion on the actual selected nested carrier, before it is forgotten into an enlarged canonical cell: full projection makes the displayed triple a regular $C_3$ orbit, and the retained one-$C_3$ pattern forbids a second width-three ternary orbit. The enlarged width-three cell is not claimed empty. The cover, forward row and exponential forward-estimate assembly are rebuilt on the refined index. |
| [C3HighAlignedRefinedExhaustion](SymmetricSubgroupAsymptotics/C3HighAlignedRefinedExhaustion.lean) | Shows every refined aligned cell reaches a local row. A transitive ternary p-group has odd degree, so the surviving ternary cells have width nine or twenty seven and receive the positive-width rows of `C3TernaryPGroupAlignedPositiveLocal`. With the natural-A4, degree-six, prime-base and binary-nine rows this closes the high-C3 owner continuation and the complete regular-C3 ordinary audit, relative to the four named ternary inputs and `KovacsPraegerAbelianizationBound`. |
| [C3CompletePhysicalContinuation](SymmetricSubgroupAsymptotics/C3CompletePhysicalContinuation.lean) | Splits the complete noncritical regular-C3 physical family between its invariant finite high-owner sector and the appended final residual owner, then adds their forward estimates. This leaves only the finite local owner/action bounds as the numerical input to the complete c=1 audit. |
| [C3CompleteOutsideAudit](SymmetricSubgroupAsymptotics/C3CompleteOutsideAudit.lean) | Proves that full regular-C3 projection supplies an actual cyclic order-three orbit after every complete physical relabelling. The complete c=1 family is therefore a literal subfamily of the general outside-`Fits` frontier, so any reusable general non-2 forward estimate closes c=1 directly; the finite six-width continuation remains an independent audit. |
| [C3ResidualClosure](SymmetricSubgroupAsymptotics/C3ResidualClosure.lean) | Applies those four physical branches first and the canonical catch-all last. The high trivial-axis family on the final residual predicate is literally empty, leaving exactly the previously checked direct and low original-weight rows. |
| [C3ResidualForwardEstimate](SymmetricSubgroupAsymptotics/C3ResidualForwardEstimate.lean) | Places the two surviving c=1 residual rows at their literal complement degree, combines their checked exponential kernels, and returns a complete `ExponentialForwardEstimate` with zero high scalar term. |
| [GrowingQuotientTransferNumerics](SymmetricSubgroupAsymptotics/GrowingQuotientTransferNumerics.lean), [FusionCompleteQuotientTransfer](SymmetricSubgroupAsymptotics/FusionCompleteQuotientTransfer.lean), [GrowingQuotientHotKernel](SymmetricSubgroupAsymptotics/GrowingQuotientHotKernel.lean) | Casts the complete quotient moment into the nonnegative real fusion interface, proves the exact hot-tail inequality, and completes the square for the rounded growing moment with uniform reserve $-\rho^2(b+w)^2/4$. The physical theorem first sums all literal normal axes over one unchanged source, then applies that moment while retaining the original factorial and normalizer divisor. Exact identities install this physical bound as one pointwise growing hot scalar plus one cold forward coefficient; the hot scalar keeps the full quadratic reserve before lower-order aggregation. Growing action-class aggregation remains separate. |
| [GrowingQuotientAdditiveTail](SymmetricSubgroupAsymptotics/GrowingQuotientAdditiveTail.lean) | Extends the growing-comparator transfer to a source-independent additive tail. After literal-axis summation, the comparator-weighted term alone passes through the hot/cold quotient moment. The additive term contributes a second cold row, with its own subquadratic weighted menu mass and the direct gap `theta ≤ halfDegree(w)/4 - rho*w/4`. The two complete forward estimates are then added, so no hot/cold threshold is charged to the tail. |
| [TrivialQuotientComparator](SymmetricSubgroupAsymptotics/TrivialQuotientComparator.lean) | A subsingleton comparator has exactly one literal normal axis and one quotient map from every complete source, so its complete quotient weight is exactly one. Every nonnegative exponential threshold therefore has an empty hot set; this branch enters the cold row without dividing by a comparator degree. |
| [GrowingQuotientDegreeBounds](SymmetricSubgroupAsymptotics/GrowingQuotientDegreeBounds.lean) | For every nontrivial padded comparator, the rounded simultaneous-graph degree lies between $\rho(b+w)$ and $(1+1/(2\rho))b+w$. The lower bound makes the coarse subgroup estimate uniform in ambient degree, and the upper bound converts its quadratic error into an explicitly prescribed fraction of the retained hot reserve. |
| [GrowingComparatorPadding](SymmetricSubgroupAsymptotics/GrowingComparatorPadding.lean) | Implements the manuscript's fixed-point padding at the parity-safe even width. The original margin proves that the padded degree is at most $(1-4\rho)w$ and the residual margin is at least $\rho w/2$; a nontrivial faithful comparator, whose original degree is at least two, also gives the required lower bound $v\geq\rho w$. |
| [GrowingQuotientColdAggregate](SymmetricSubgroupAsymptotics/GrowingQuotientColdAggregate.lean) | Sums a width-dependent finite certificate menu with every original divisor retained. A direct bound on the weighted certificate mass, together with the padded capacity gap, gives the sharp pointwise cold coefficient $2^{-\rho wn/8}$ for every removed width $w\geq3$. |
| [GrowingQuotientColdRow](SymmetricSubgroupAsymptotics/GrowingQuotientColdRow.lean) | Assigns every growing-width cold menu to its literal complement degree and proves exact forward support. The pointwise width bounds sum as a genuine geometric tail, preserving the rate and giving the aggregate $2\cdot2^{-\rho w_0n/8}$. |
| [GrowingQuotientHotAggregate](SymmetricSubgroupAsymptotics/GrowingQuotientHotAggregate.lean) | Aggregates the complete growing hot menu. The graph-degree bounds allocate one sixteenth of the quadratic exponent to the coarse subgroup estimate and a direct original-weight overhead allocates one more, leaving the uniform scalar bound $2^{-\rho^2n^2/8}$. |
| [GrowingMenuMassAbsorption](SymmetricSubgroupAsymptotics/GrowingMenuMassAbsorption.lean), [GrowingMenuMassCertificate](SymmetricSubgroupAsymptotics/GrowingMenuMassCertificate.lean), [GrowingMenuMassEntryCertificate](SymmetricSubgroupAsymptotics/GrowingMenuMassEntryCertificate.lean) | Replaces separate certificate-size and action-class entropy inputs by one direct, width-uniform subexponential bound on the original weighted menu mass. A concrete certificate of the form $B_\epsilon(n+1)^{p_\epsilon}2^{\epsilon w^2}$, for every positive $\epsilon$, implies that uniform menu bound on the whole triangle $w_0\leq w\leq n$. The entry certificate proves this concrete bound from a subquadratic index count and a uniform per-entry bound, splitting the quadratic exponent between them and multiplying their constants. These results absorb every polynomial, Euler-product and finite-width summation overhead required by both the cold $wn$ estimate and the fully aggregated hot $n^2$ estimate. |
| [GrowingQuotientForwardEstimate](SymmetricSubgroupAsymptotics/GrowingQuotientForwardEstimate.lean) | Packages the full growing-comparator numerical transfer as an `ExponentialForwardEstimate`, uniformly from width three. Controlled padding proves every hot/cold parameter inequality, moving graph degrees enter the published coarse estimate uniformly, and one direct menu-mass condition yields rate $\rho^2/8$. A separate cold-only constructor handles trivial comparators, whose hot set is empty, at rate $\rho w_0/8$. |
| [GrowingQuotientPhysicalAssembly](SymmetricSubgroupAsymptotics/GrowingQuotientPhysicalAssembly.lean) | Turns a literal sigma-indexed cover and complete-source comparator envelopes into the exact growing physical bound. The weighted cold-row identity retains every complement degree, original normalizer, and action label without a reindexing loss. |
| [Non2TransitiveActionClasses](SymmetricSubgroupAsymptotics/Non2TransitiveActionClasses.lean) | Constructs the complete finite index of actual non-2 transitive permutation actions modulo conjugacy on their original point set. It classifies both point-selected orbits and literal quotient-orbit profiles by an exact relabelling to one chosen representative. |
| [Non2OutsideOrbitPhysical](SymmetricSubgroupAsymptotics/Non2OutsideOrbitPhysical.lean) | Installs an exact literal non-2 orbit chart in its canonical arbitrary-width family while retaining the complete complementary action, every correlation with it, and the original ordinary-remainder predicate. |
| [Non2OutsideOrbitMenu](SymmetricSubgroupAsymptotics/Non2OutsideOrbitMenu.lean) | Builds the finite exact-width/action-class menu and proves a literal physical cover of the entire outside remainder. One bad orbit chooses the label, while the covered object remains the complete original subgroup, so no orbit-pointing multiplicity is charged. |
| [Non2OutsideFrontierAdapter](SymmetricSubgroupAsymptotics/Non2OutsideFrontierAdapter.lean) | Identifies the literal outside-subgroup count with the ambient-degree frontier ratio and partitions its source disjointly by the single selected bad orbit. The small side has width exactly three or four; the growing side has width at least five, with no duplicated owner. |
| [Non2GrowingPhysicalFrontier](SymmetricSubgroupAsymptotics/Non2GrowingPhysicalFrontier.lean) | Splits the ambient outside ratio exactly into widths three/four and the width-at-least-five diagnostic sector, and also sends the entire outside frontier into the sigma-indexed quotient assembly at cutoff three. The same selected orbit determines the sector and action label. The uniform local predicate reconstructs the complete ordinary subgroup in degree $w+b$, so one complete-source local envelope now supplies the full physical premise directly, with the degree-three $C_3$ case as its first required audit. |
| [Non2FirstOwnerPhysicalFrontier](SymmetricSubgroupAsymptotics/Non2FirstOwnerPhysicalFrontier.lean) | Refines the complete cutoff-three non-2 frontier by the first eligible physical owner and the selected action class. Cross-degree relabelling preserves ownership, every subgroup enters exactly one owner-action branch, and owner-specific local bounds plus their joint original-weight menu mass yield the same forward estimate. This is the formal interface for earlier-owner acceptance versus the terminal annihilator-aware capacity branch. |
| [Non2OwnerCapacityFrontier](SymmetricSubgroupAsymptotics/Non2OwnerCapacityFrontier.lean) | Appends a canonical catch-all residual branch to any finite relabelling-natural earlier-owner menu. Earlier first owners are unchanged, while first ownership by the final branch is exactly rejection by every earlier owner. Branch-specific complete-source envelopes then feed the cutoff-three forward theorem directly; the terminal premise is imposed only on the actual unowned residual family. |
| [Non2OwnerAxisFrontier](SymmetricSubgroupAsymptotics/Non2OwnerAxisFrontier.lean) | States the remaining local input at literal normal-axis resolution. One surviving-epimorphism envelope for each owner, selected non-2 action, normal axis and unchanged complete source is summed exactly and passed through the complete quotient moment to the full outside-frontier forward estimate. |
| [FusionEpimorphismTransport](SymmetricSubgroupAsymptotics/FusionEpimorphismTransport.lean), [FusionEpimorphismLifts](SymmetricSubgroupAsymptotics/FusionEpimorphismLifts.lean), [FusionFiniteMenu](SymmetricSubgroupAsymptotics/FusionFiniteMenu.lean) | Literal epi transport and survival-restricted extension fibres; fractional-Schur epi envelopes on the actual source; actual physical hot/cold fusion from local envelopes and same-source moments. |
| [FusionCentralLifts](SymmetricSubgroupAsymptotics/FusionCentralLifts.lean), [FusionCentralPrefix](SymmetricSubgroupAsymptotics/FusionCentralPrefix.lean) | Actual central-cut lift fibres, exact binary character factor, original Schur envelope, and its literal same-source graph moment without a split-extension assumption. |
| [FusionPhysicalUnion](SymmetricSubgroupAsymptotics/FusionPhysicalUnion.lean), [FusionKernelAssembly](SymmetricSubgroupAsymptotics/FusionKernelAssembly.lean), [FusionShiftedMenu](SymmetricSubgroupAsymptotics/FusionShiftedMenu.lean), [FusionContinuationRow](SymmetricSubgroupAsymptotics/FusionContinuationRow.lean) | Actual normalized physical fusion from local envelopes and graph moments, including zero graph width; complete finite sums at each actual complement degree n−2h, exact weighted row assembly, forward support and a proved contractive row aggregate. |
| [C1SplitCharacters](SymmetricSubgroupAsymptotics/C1SplitCharacters.lean), [C1BinaryInflation](SymmetricSubgroupAsymptotics/C1BinaryInflation.lean), [C1CharacterWitness](SymmetricSubgroupAsymptotics/C1CharacterWitness.lean), [C1ComplementChart](SymmetricSubgroupAsymptotics/C1ComplementChart.lean), [C1InverseComplement](SymmetricSubgroupAsymptotics/C1InverseComplement.lean), [C1InverseComplementCount](SymmetricSubgroupAsymptotics/C1InverseComplementCount.lean), [C1CosetReciprocal](SymmetricSubgroupAsymptotics/C1CosetReciprocal.lean), [C1ActualGraphs](SymmetricSubgroupAsymptotics/C1ActualGraphs.lean), [C1RetainedAnnihilator](SymmetricSubgroupAsymptotics/C1RetainedAnnihilator.lean), [C1PhysicalWeight](SymmetricSubgroupAsymptotics/C1PhysicalWeight.lean) | Exact surviving split-character weights, reversible inverse-complement charts with the original reciprocal denominator, binary-kernel invariance, retained annihilator count, and the physical c=1 row with original normalizer six. |
| [FiniteCayleyReflection](SymmetricSubgroupAsymptotics/FiniteCayleyReflection.lean), [FinitePermutationEncoding](SymmetricSubgroupAsymptotics/FinitePermutationEncoding.lean), [FiniteCayleyGroup](SymmetricSubgroupAsymptotics/FiniteCayleyGroup.lean), [FiniteCayleyMaps](SymmetricSubgroupAsymptotics/FiniteCayleyMaps.lean) | Faithful numeric permutation rows, well-founded original-generator paths, actual executable finite groups, and homomorphisms certified by generator transitions. |
| [FinitePermutationRegistry](SymmetricSubgroupAsymptotics/FinitePermutationRegistry.lean), [BinaryMenuSmallCoverage](SymmetricSubgroupAsymptotics/BinaryMenuSmallCoverage.lean), [BinaryRowCharacters](SymmetricSubgroupAsymptotics/BinaryRowCharacters.lean), [BinaryCharacterRegistry](SymmetricSubgroupAsymptotics/BinaryCharacterRegistry.lean), [BinaryActionCoverage8](SymmetricSubgroupAsymptotics/BinaryActionCoverage8.lean) | Universal original-generator bit coverage, literal ambient conjugacy edges, and complete transitive binary action coverage in degrees 2, 4 and 8. |
| [BinaryGeneratorConjugacy](SymmetricSubgroupAsymptotics/BinaryGeneratorConjugacy.lean), [BinaryGeneratorRegistry](SymmetricSubgroupAsymptotics/BinaryGeneratorRegistry.lean), [BinaryNormalGeneratorSteps](SymmetricSubgroupAsymptotics/BinaryNormalGeneratorSteps.lean) | Generator membership plus exact orders identify actual conjugate children and quotient-cyclic normal steps; full row correspondence tables are unnecessary. |
| [FusionArbitraryWidth](SymmetricSubgroupAsymptotics/FusionArbitraryWidth.lean), [FusionWidthContinuation](SymmetricSubgroupAsymptotics/FusionWidthContinuation.lean), [FusionWidthPhysical](SymmetricSubgroupAsymptotics/FusionWidthPhysical.lean) | Exact normalization and contractive forward rows at arbitrary odd/even deletion widths; the physical implication retains the original action divisor and complete complement. Any complete physical orbit/complement chart now enters the same canonical family at arbitrary width, rather than only at even binary width. |
| [FusionWidthUniformNormalization](SymmetricSubgroupAsymptotics/FusionWidthUniformNormalization.lean) | Retains the full removed-width quadratic reserve in the arbitrary-width pointing ratio and cold kernel, with the original multiplicity, divisor and local capacity exponent. An independent hot-pointing denominator bound works for every complement degree and width, without the former large-complement restriction. |
| [C1LowCone](SymmetricSubgroupAsymptotics/C1LowCone.lean), [C1LowNormalized](SymmetricSubgroupAsymptotics/C1LowNormalized.lean), [C1LowNaturality](SymmetricSubgroupAsymptotics/C1LowNaturality.lean), [C1Continuation](SymmetricSubgroupAsymptotics/C1Continuation.lean) | The actual surviving low-cone physical mass and its uniform exponential bound, plus a contractive numerical row for earlier-owner types. Actual high-cone owner coverage is a separate obligation. |
| [C1FiniteOwnerWitness](SymmetricSubgroupAsymptotics/C1FiniteOwnerWitness.lean), [TernaryOwnerWitness6T1](SymmetricSubgroupAsymptotics/TernaryOwnerWitness6T1.lean), [TernaryOwnerWitness6T4](SymmetricSubgroupAsymptotics/TernaryOwnerWitness6T4.lean), [TernaryOwnerWitness6T5](SymmetricSubgroupAsymptotics/TernaryOwnerWitness6T5.lean), [TernaryOwnerWitness6T6](SymmetricSubgroupAsymptotics/TernaryOwnerWitness6T6.lean) | Intrinsic degree-six earlier-owner witnesses on the original actions: the index-two normal ternary cases and the cyclic elementary-binary semidirect cases. Their literal Cayley/action tables are checked separately. |
| [C1FiniteOwnerTransport](SymmetricSubgroupAsymptotics/C1FiniteOwnerTransport.lean), [C1FiniteOwnerMenu](SymmetricSubgroupAsymptotics/C1FiniteOwnerMenu.lean) | The index-two, cyclic-binary, nonsplit ternary prime-base and correlated binary nine-translation owner structures transport through actual group equivalences. The transports retain the normal bases, complements, exact factorization, distinguished vector and conjugate words, literal $A_4$ top kernel with its equivariant coordinates, and the whole nine-point quotient action with its conjugation law. The eleven checked bounded actions form one exact original-action recognition target rather than a list of order tests. |
| [DegreeSixTernaryBlockOwner](SymmetricSubgroupAsymptotics/DegreeSixTernaryBlockOwner.lean) | Structural degree-six split for every high normal pair: a minimal $3\times2$ block system gives a normal ternary kernel of index two, and the complementary $2\times3$ geometry is isolated for the binary-frame theorem. |
| [BinaryC3CyclicModule](SymmetricSubgroupAsymptotics/BinaryC3CyclicModule.lean) | Every invariant submodule of the natural three-coordinate binary permutation module for an order-three top is generated by one actual orbit. The proof classifies only the four submodules of this fixed local module, supplying literal list words for the later owner witness. |
| [DegreeSixBinaryBlockOwner](SymmetricSubgroupAsymptotics/DegreeSixBinaryBlockOwner.lean) | Completes the structural degree-six ownership theorem. Highness forces the actual three-block top to be $C_3$; the literal binary block kernel is elementary, Schur--Zassenhaus supplies an actual complement, and the local orbit words become products of actual conjugates through the faithful kernel chart. Transport back to the original group gives the intrinsic cyclic binary-module witness, so no degree-six action catalogue remains in the high-pair ownership implication. |
| [DegreeTwelveBlockReduction](SymmetricSubgroupAsymptotics/DegreeTwelveBlockReduction.lean), [DegreeTwelveTopGeometry](SymmetricSubgroupAsymptotics/DegreeTwelveTopGeometry.lean) | Reduces every high degree-twelve normal pair to an internally selected minimal block system of type $3\times4$ or $4\times3$. The excluded $2\times6$ and $6\times2$ orientations have relative ternary rank at most one. In both surviving orientations the original rank is exactly two, the primitive-fibre chief weight is exactly one, and the original normal top image has rank exactly one. The four-block top is then the literal natural $A_4$ action, while the three-block top has order three. The two resulting structural owner geometries are completed below. |
| [DegreeTwelvePrimeBaseReduction](SymmetricSubgroupAsymptotics/DegreeTwelvePrimeBaseReduction.lean) | In the saturated $3\times4$ branch, eliminates every ternary-fibre inversion from the strict rank gain $2>1$, proves the literal block kernel is a $3$-group, and uses the exact restriction sequence to retain a one-dimensional character image on $N\cap\ker(\mathrm{top})$, including an actual nonzero character in that range. |
| [TernaryA4InvariantSubmodules](SymmetricSubgroupAsymptotics/TernaryA4InvariantSubmodules.lean) | Classifies the natural $A_4$-invariant submodules of $\mathbb F_3^4$ as zero, diagonal, augmentation or full. The augmentation has full coordinate projections but no nonzero invariant functional; consequently a retained invariant head forces diagonal or full after the coherent physical-coordinate identification below. |
| [TernaryA4SectionRegularEmbedding](SymmetricSubgroupAsymptotics/TernaryA4SectionRegularEmbedding.lean) | Avoids a separate classification of the quotients of $A_4$. Every invariant section $B/(B\cap C)$ of the natural four-coordinate ternary module embeds equivariantly in the same coordinate module. If its action factors through an onto map $A_4\twoheadrightarrow Q$, a matrix coefficient embeds it in the actual regular $\mathbb F_3[Q]$-module. |
| [DegreeTwelveCoherentTernaryCoordinates](SymmetricSubgroupAsymptotics/DegreeTwelveCoherentTernaryCoordinates.lean), [C1TernaryPrimeBaseOwner](SymmetricSubgroupAsymptotics/C1TernaryPrimeBaseOwner.lean) | Constructs coherent physical triple-fibre charts from actual ambient transporters, proves every transition even, and injects the original kernel equivariantly into the natural $\mathbb F_3^4$ module. The saturated $3\times4$ branch therefore installs a nonsplit prime-base owner with its literal $A_4$ top. For every arbitrary original normal axis, its exact coordinate denominator is invariant and its section kernel is the physical intersection; no assumption $N\leq\ker(\mathrm{top})$ is used. |
| [OriginalKernelArbitraryNormalQuotient](SymmetricSubgroupAsymptotics/OriginalKernelArbitraryNormalQuotient.lean) | Descends any original prime-kernel module chart through every arbitrary original normal subgroup. It constructs the literal map $Q/N\to Q/(\ker\pi\vee N)$, the exact kernel section $\ker\pi/(\ker\pi\cap N)$, its quotient representation and its original conjugation chart, without splitting or replacing either quotient by an abstract group. |
| [C1TernaryPrimeBaseQuotient](SymmetricSubgroupAsymptotics/C1TernaryPrimeBaseQuotient.lean) | Installs the generic arbitrary-normal adapter on the intrinsic prime-base owner. For every original normal $N$, it identifies the adapter denominator with the physical coordinate axis, constructs the onto map $A_4\to G/(\ker(\mathrm{top})\vee N)$, proves the action factorization, and embeds the actual kernel module of $G/N$ into that quotient's regular ternary module. No factorization, splitting, diagonal/full classification, or containment $N\leq\ker(\mathrm{top})$ remains as an input. |
| [DegreeTwelveFourBlockCore](SymmetricSubgroupAsymptotics/DegreeTwelveFourBlockCore.lean) | Proves that the saturated $4\times3$ intersection head is one. Under the explicit all-even fibre condition, constructs the actual normal elementary binary core $W\leq V_4^3$, proves $|W|\leq64$, proves the original quotient is a $3$-group, and obtains an actual ternary complement by Schur--Zassenhaus. It does not assume $W=V_4^3$. |
| [DegreeTwelveFourBlockSigns](SymmetricSubgroupAsymptotics/DegreeTwelveFourBlockSigns.lean), [DegreeTwelveFourBlockFullness](SymmetricSubgroupAsymptotics/DegreeTwelveFourBlockFullness.lean) | Removes the all-even hypothesis from the saturated $4\times3$ branch. An odd local image would make every coordinate normal head vanish, contradicting the retained intersection head. Each actual block-kernel image is then all of $A_4$, and cubing local lifts proves that the intrinsic correlated core maps onto every literal $V_4$ coordinate. The proof still does not replace the core by the full product. |
| [DegreeTwelveNineTranslations](SymmetricSubgroupAsymptotics/DegreeTwelveNineTranslations.lean) | Packages the whole quotient by the intrinsic correlated binary core as an action on the nine ambient nonidentity local translations. Its kernel is exactly the core, and full local $A_4$ images make the quotient action transitive. The resulting faithful transitive $3$-group action is proved for the complete saturated $4\times3$ branch, without requiring the supported ambient translations themselves to lie in the core. |
| [C1BinaryNineTopOwner](SymmetricSubgroupAsymptotics/C1BinaryNineTopOwner.lean) | Installs the intrinsic mixed owner with its actual correlated elementary binary core, whole faithful transitive nine-translation quotient, and original conjugation. The core constructs its own binary module chart; for every arbitrary original normal $N$, the descended extension is the literal $G/N\to G/(W\vee N)$ with kernel $W/(W\cap N)$, and its top remains a $3$-group. It assumes neither $N\leq W$, a complement, a full $V_4^3$ base, nor cyclicity of the correlated module. |
| [TernaryHighOwnerCapacity](SymmetricSubgroupAsymptotics/TernaryHighOwnerCapacity.lean) | Combines the high-action degree menu with the structural degree-six owners and both intrinsic degree-twelve owners. Under the four explicitly named global ternary stability inputs, every original normal pair is accepted by an existing 3-group, natural-$A_4$, index-two, cyclic-binary, prime-base or nine-translation owner, or satisfies the exact capacity inequality $20d_3(N)\leq3|\Omega|$. All six owner branches transport through arbitrary physical relabellings, retaining their complete structural witnesses. Whole-subgroup first ownership and the remaining numerical owner consumers are separate. |
| [C3HighNestedCarrier](SymmetricSubgroupAsymptotics/C3HighNestedCarrier.lean) | Starts from the selected high trivial-axis $C_3$ orbit itself, retaining its normal axis and strict high inequality. It lifts the orbit action into the complete outer physical subgroup, identifies the exact complementary action, splits that complement as the literal outer $C_3$ block plus the undeleted points, and installs the result in the arbitrary-width canonical fusion family. Thus the structural owner output is attached to the same physical carrier used by continuation, without dropping the selected high pair. |
| [RegularKernelHomBound](SymmetricSubgroupAsymptotics/RegularKernelHomBound.lean) | Evaluation at the identity coefficient injects equivariant homomorphisms into scalar characters of the same original source kernel whenever the target module embeds in its actual top's regular module. The surviving-lift bound retains the complete module and $H^1$ factors and applies to empty or nonsplit fibres. |
| [C1OriginalNormalEpiSum](SymmetricSubgroupAsymptotics/C1OriginalNormalEpiSum.lean) | Sums the regular-kernel bound first over the actual top epimorphisms and then over every literal original normal axis, retaining one complete source subgroup throughout. Its physical consumers feed `C1OwnerAggregate` directly and allow source-pattern restrictions by proving all surviving fibres outside the source class empty. The remaining inputs are the row-specific top-map character-mass estimates. |
| [C1OwnerAggregate](SymmetricSubgroupAsymptotics/C1OwnerAggregate.lean) | Converts a fixed-source estimate already summed over every literal original normal axis into the exact physical c=1 row. The polynomial is charged once, the complete-source sum remains `subgroupCount`, and the original action normalizer is retained. |
| [TernaryOneExceptionalOrbitRank](SymmetricSubgroupAsymptotics/TernaryOneExceptionalOrbitRank.lean), [C1DegreeNineSourceRank](SymmetricSubgroupAsymptotics/C1DegreeNineSourceRank.lean) | The actual orbit filtration sums one exceptional local ternary allowance without changing the complete source: local bounds $9\delta_o\leq2|o|+3\mathbf1_{o=o_0}$ give $9d_3(J)\leq2b+3$. For the unique regular-$C_3$, no-natural-$A_4$ source pattern this uses the existing primitive chief/head and degree-eighteen inputs explicitly. |
| [PrimeElementaryEpimorphismBound](SymmetricSubgroupAsymptotics/PrimeElementaryEpimorphismBound.lean), [C1DegreeNineTopMass](SymmetricSubgroupAsymptotics/C1DegreeNineTopMass.lean) | Computes the exact number of homomorphisms to an elementary prime target and bounds rank-two epimorphisms. For a degree-nine target certified as elementary rank at most two or a possibly nonsplit $C_3$-by-regular-module extension, the one-exception source budget and literal binary-kernel rank give the fixed-target mass $2187\,2^{25b/18}$. The physical installer retains as explicit inputs the target alternative and regular embedding for every descended original-normal section, together with the named global ternary stability premises. |
| [C1TernaryPrimeBaseMass](SymmetricSubgroupAsymptotics/C1TernaryPrimeBaseMass.lean) | For every actual quotient of the literal $A_4$ top, the internal permutation theorem supplies the one-third bound on each literal top-map kernel. A top-epimorphism estimate with exponent $8/15$ then gives the complete same-source character mass with exponent $16/15$ and installs it through every original normal axis. Its generic interface retains the top estimate; `C1A4QuotientTopEpi` discharges it internally. |
| [C1A4QuotientTopEpi](SymmetricSubgroupAsymptotics/C1A4QuotientTopEpi.lean) | Closes the uniform quotient-target input. A single explicit binary character on the literal derived subgroup labels epimorphisms to $A_4$ and determines their kernels, giving $|\operatorname{Epi}(J,A_4)|\leq|\operatorname{Aut}(A_4)|2^{\lfloor b/2\rfloor}$ from the internal permutation half-rank theorem. An axiom-free order/commutator argument proves every literal quotient target is $A_4$, $C_3$ or trivial; the latter two are handled internally. The stronger full-target exponent embeds directly into $8b/15$, with no polynomial-absorption loss. |
| [C1SparseSemidirectCertificate](SymmetricSubgroupAsymptotics/C1SparseSemidirectCertificate.lean), [C1V4BlockGeometryCertificate](SymmetricSubgroupAsymptotics/C1V4BlockGeometryCertificate.lean), [TernaryV4Semidirect12T228](SymmetricSubgroupAsymptotics/TernaryV4Semidirect12T228.lean), [TernaryV4Semidirect12T229](SymmetricSubgroupAsymptotics/TernaryV4Semidirect12T229.lean), [TernaryV4Semidirect12T265](SymmetricSubgroupAsymptotics/TernaryV4Semidirect12T265.lean) | Sparse original-action semidirect witnesses and the three V4-block geometries: three literal four-point blocks, all nine nonidentity local translations, exact generation of the elementary binary base, complement conjugation, and transitivity on those translations. These witnesses do not prove exhaustive high-cone coverage. |
| [C1PrimeBaseGeometryCertificate](SymmetricSubgroupAsymptotics/C1PrimeBaseGeometryCertificate.lean), [TernaryPrimeBase12T194](SymmetricSubgroupAsymptotics/TernaryPrimeBase12T194.lean) | The full prime-base degree-twelve owner on the original points: four literal triples, all eight local ternary translations generating the order-81 base, a disjoint order-12 complement, and its exact transitive order-12 action on the four blocks. This completes the eleven individual c=1 finite-owner witnesses; exhaustive high-pair coverage remains separate. |
| [PrimeEquivariantCharacters](SymmetricSubgroupAsymptotics/PrimeEquivariantCharacters.lean), [PrimeRelativeHeadChain](SymmetricSubgroupAsymptotics/PrimeRelativeHeadChain.lean), [PrimeRelativeFiltration](SymmetricSubgroupAsymptotics/PrimeRelativeFiltration.lean), [PrimeCoordinateRanks](SymmetricSubgroupAsymptotics/PrimeCoordinateRanks.lean) | Exact restriction-image heads for nonsplit extensions and proper nonabelian subdirect cores, normal filtrations, and a high relative-head witness in an original coordinate. |
| [C1PrimitiveTail](SymmetricSubgroupAsymptotics/C1PrimitiveTail.lean), [C1ImprimitiveNumerics](SymmetricSubgroupAsymptotics/C1ImprimitiveNumerics.lean), [TraceyTernaryEnvelope](SymmetricSubgroupAsymptotics/TraceyTernaryEnvelope.lean) | The primitive tail with its precisely named HRD hypothesis, and proved imprimitive scalar bounds with the structural recurrence still explicit. |
| [TraceyPrimePowerInput](SymmetricSubgroupAsymptotics/TraceyPrimePowerInput.lean), [TraceySylowIndices](SymmetricSubgroupAsymptotics/TraceySylowIndices.lean), [TraceyTernaryPrimePower](SymmetricSubgroupAsymptotics/TraceyTernaryPrimePower.lean) | A literal published prime-power input, actual Sylow orbit degrees, and floor-preserving numerical aggregation. The input remains a theorem hypothesis. |
| [BinaryFiniteEntryCoverage8](SymmetricSubgroupAsymptotics/BinaryFiniteEntryCoverage8.lean) | Exhaustive original degree-8 normal-state coverage: 190 physical certificates, 10 exact character criteria and three transport charts, with the original conjugation and normalizer. |
| [BinaryOriginalWeightedDirectEntry](SymmetricSubgroupAsymptotics/BinaryOriginalWeightedDirectEntry.lean), [BinaryOriginalWeightedPartialSelection](SymmetricSubgroupAsymptotics/BinaryOriginalWeightedPartialSelection.lean), [BinaryDegreeEightDirectEntryCoverage](SymmetricSubgroupAsymptotics/BinaryDegreeEightDirectEntryCoverage.lean), [BinaryDegreeEightNormalizerSaturatedDirect](SymmetricSubgroupAsymptotics/BinaryDegreeEightNormalizerSaturatedDirect.lean), [BinaryDegree16DirectOwnerRouting](SymmetricSubgroupAsymptotics/BinaryDegree16DirectOwnerRouting.lean), [BinaryDegree16NormalizerSaturatedDirect](SymmetricSubgroupAsymptotics/BinaryDegree16NormalizerSaturatedDirect.lean) | Gives every accepted direct axis one width-uniform original-weight interface: an even strictly shorter prefix, all same-source moments, the arbitrary-survival envelope, its exact forward row, exponential row decay and eventual contraction. A reusable partial-selection theorem assigns literal zero coefficients to inactive axes by proving their retained Goursat fibres empty. In degree eight all 190 generated pair rows retain their checked even cover degree, the ten character rows enter the same interface, and the three exceptional rows enter their carrier owners. The resulting theorem constructs the intrinsic unmarked direct/carrier split on actual eight-point orbits; its direct family has an exact ordinary-count forward recurrence, exponential row decay, contraction and arbitrary first-owner filtering, while every residual orbit witness retains an exact classified carrier slot. Every degree-sixteen direct owner, including the order/seven-character branch and both catalogue-conjugate branches, likewise pulls back to the literal original action and normal. Entry existence transports through arbitrary action equivalences and is therefore stable under the full original normalizer. The unmarked degree-sixteen direct family has the same recurrence and filtering properties, with no catalogue or marked-orbit multiplicity. |
| [BinaryDegreeEightBaseRoutes](SymmetricSubgroupAsymptotics/BinaryDegreeEightBaseRoutes.lean), [BinaryDegreeEightPhysicalAnalyticClosure](SymmetricSubgroupAsymptotics/BinaryDegreeEightPhysicalAnalyticClosure.lean), [BinaryDegree16CarrierRouting](SymmetricSubgroupAsymptotics/BinaryDegree16CarrierRouting.lean) | Identifies the base actions with their exact carrier-alphabet colours, including the explicit `E8`/`8T22` point conjugacy. Every transitive binary degree-eight axis is direct or an exact slot. The proper 16T1086 chart and the unchanged 16T1332 colour give the same direct-or-slot theorem in degree sixteen; every degree-sixteen carrier slot retains an explicit noncritical cell. |
| [BinaryCarrierAlphabetWordClosure](SymmetricSubgroupAsymptotics/BinaryCarrierAlphabetWordClosure.lean), [BinaryCarrierProfileAxisClosure](SymmetricSubgroupAsymptotics/BinaryCarrierProfileAxisClosure.lean), [BinaryCarrierRoutedWordClosure](SymmetricSubgroupAsymptotics/BinaryCarrierRoutedWordClosure.lean), [BinaryCarrierRoutedProfileAssembly](SymmetricSubgroupAsymptotics/BinaryCarrierRoutedProfileAssembly.lean), [BinaryCarrierRoutedProfileAxisClosure](SymmetricSubgroupAsymptotics/BinaryCarrierRoutedProfileAxisClosure.lean) | Packages unchanged and exceptional carrier occurrences into one finite source alphabet. Routed source equivalences preserve coordinate fullness and every literal normal axis. The canonical axis profile injectively partitions the no-direct residual, and each fixed profile with noncritical support enters the completed mixture. Arbitrary curried physical action profiles flatten to this exact word interface. The aggregate theorem retains the finite profile sum and assumes no cross-profile injectivity. |
| [BinaryCarrierActualDecoratedTransport](SymmetricSubgroupAsymptotics/BinaryCarrierActualDecoratedTransport.lean), [BinaryCarrierActualDecoratedProducer](SymmetricSubgroupAsymptotics/BinaryCarrierActualDecoratedProducer.lean) | States the corrected aggregate target as a joint injection into a bounded decoration and one actual subgroup in one retained physical `(a,T)` bin. Its sigma target has cardinality exactly the sum of the literal bin families, so profile witnesses inside propositions and untouched identity-slot axes do not create a raw multiplicity. The generic producer composes any heterogeneous reversible slot word with per-slot quarter retention and an actual-source reconstruction code, preserving proper nonabelian subdirect carriers and quotient-identity slots, and proves the exact retained-bin cardinal bound. |
| [BinaryS16CanonicalCarrierProfile](SymmetricSubgroupAsymptotics/BinaryS16CanonicalCarrierProfile.lean), [BinaryS16ResidualPartition](SymmetricSubgroupAsymptotics/BinaryS16ResidualPartition.lean), [BinaryS16SupportAccounting](SymmetricSubgroupAsymptotics/BinaryS16SupportAccounting.lean), [BinaryS16FinalFibreReflection](SymmetricSubgroupAsymptotics/BinaryS16FinalFibreReflection.lean), [BinaryS16FinalFibreAssembly](SymmetricSubgroupAsymptotics/BinaryS16FinalFibreAssembly.lean), [BinaryS16FinalFibreClosure](SymmetricSubgroupAsymptotics/BinaryS16FinalFibreClosure.lean) | Exhausts fixed-point-free binary orbit sizes below sixteen, routes every residual degree-eight/sixteen orbit, and partitions the unmarked residual family into positive support plus the existing critical owner. Literal orbit accounting assigns support `2,4,8` to the positive colours and disintegrates the positive family over its unique `C_old`. Equality of the mixed table aligns changed routes; the route-output naturality square returns both targets to fixed original labels; indexed full-preimage reflection recovers the complete correlated word, including identity slots; and the slot-preserving binary source reindex recovers the canonical flat source. Thus every fixed table/target fibre has size one, also for the proper nonabelian `16T1086` carrier, with no point-chart or axis multiplicity. |
| [BinaryS16DecorationNumerics](SymmetricSubgroupAsymptotics/BinaryS16DecorationNumerics.lean), [BinaryS16PositiveResidualEstimate](SymmetricSubgroupAsymptotics/BinaryS16PositiveResidualEstimate.lean), [BinaryNativeOwnerPartition](SymmetricSubgroupAsymptotics/BinaryNativeOwnerPartition.lean), [BinaryNativeRecurrence](SymmetricSubgroupAsymptotics/BinaryNativeRecurrence.lean) | Pays the exact `(2N+2)^(20*C_old)` decoration inside the strong small-support, Hall, and carrier-reserve envelopes, then absorbs the cubic support/bin index. The positive residual has eventual normalized bound `2^(-(29/2980864)N)`. A deterministic four-owner injection covers every noncritical binary subgroup by the wide-orbit, direct degree-eight, direct degree-sixteen, or positive residual family. The three original-weight rows plus this scalar define the complete native `RankForwardEstimate`, with strictly forward ordinary targets and exponentially decaying aggregate row. |
| [BinaryPairCertificateCapacity](SymmetricSubgroupAsymptotics/BinaryPairCertificateCapacity.lean), [BinaryPairPrefixChart](SymmetricSubgroupAsymptotics/BinaryPairPrefixChart.lean) | Actual cut dimension and quotient capacity, followed by the literal central-prefix tower, surviving-epi bound and joint moment. |
| [InducedMackeyDecomposition](SymmetricSubgroupAsymptotics/InducedMackeyDecomposition.lean), [InducedTernaryEnvelope](SymmetricSubgroupAsymptotics/InducedTernaryEnvelope.lean) | Actual twisted Mackey coordinates and the older Gaussian envelope, whose prime-power branch retains the named Tracey hypothesis. The coprime branch is proved from Maschke and Frobenius. |
| [PGroupOrderedTransversal](SymmetricSubgroupAsymptotics/PGroupOrderedTransversal.lean), [RepresentationLeadingAntichain](SymmetricSubgroupAsymptotics/RepresentationLeadingAntichain.lean), [PGroupInducedHead](SymmetricSubgroupAsymptotics/PGroupInducedHead.lean) | Actual prime-index chains and ordered coset transversals bound the intrinsic head of every induced subrepresentation over a finite three-group, with arbitrary original subgroups and fibres. |
| [InducedTernaryWidthEnvelope](SymmetricSubgroupAsymptotics/InducedTernaryWidthEnvelope.lean), [TernaryIndexWidthValues](SymmetricSubgroupAsymptotics/TernaryIndexWidthValues.lean) | The proved integer B(s) envelope on actual Sylow/Mackey pieces, natural division before the fibre factor, and exact small-index values; no prime-power literature hypothesis. |
| [ChiefOrbitEvaluation](SymmetricSubgroupAsymptotics/ChiefOrbitEvaluation.lean), [ChiefNormalStep](SymmetricSubgroupAsymptotics/ChiefNormalStep.lean), [ChiefTernaryFiltration](SymmetricSubgroupAsymptotics/ChiefTernaryFiltration.lean) | Constructed elementary images, exact retained-character kernels and aggregation of actual elementary, perfect and coprime layers. |
| [ImprimitiveBlockEvaluation](SymmetricSubgroupAsymptotics/ImprimitiveBlockEvaluation.lean), [ChiefConjugateIntersections](SymmetricSubgroupAsymptotics/ChiefConjugateIntersections.lean) | Original block-fibre action and separation, yielding the actual normal intersection chain with proved endpoints. |
| [TransitiveBlockQuotient](SymmetricSubgroupAsymptotics/TransitiveBlockQuotient.lean), [PrimitiveBlockFibre](SymmetricSubgroupAsymptotics/PrimitiveBlockFibre.lean), [OriginalMinimalBlock](SymmetricSubgroupAsymptotics/OriginalMinimalBlock.lean) | Constructed minimal block quotient, primitive literal fibre image, exact degree product, smaller faithful top action, and the original-normal natural-number chief recurrence. |
| [PermutationTwoGroupRank](SymmetricSubgroupAsymptotics/PermutationTwoGroupRank.lean) | Every faithful finite 2-group action has binary character and Frattini rank at most half its degree. Degree induction uses the actual intransitive restriction image and complementary kernel, and an actual pair frame in the transitive case. The correlated kernel's entire-group head is bounded through an element's fixed space. No published generator bound or finite catalogue is assumed. The actual Sylow subgroups of each original epimorphism kernel inherit the same bound on the unchanged exterior points. |
| [PermutationThreeGroupRank](SymmetricSubgroupAsymptotics/PermutationThreeGroupRank.lean) | Every faithful finite $3$-group action has ternary character rank at most one third of its degree. The transitive induction uses an actual prime-index block cover and the intransitive step uses the literal restriction image. Injective restriction to actual Sylow subgroups upgrades this to every finite permutation group and every literal epimorphism kernel. The same module exports the corresponding binary kernel bound from `PermutationTwoGroupRank`; no published permutation-generator premise is used. |
| [TransitiveTernaryHeadBound](SymmetricSubgroupAsymptotics/TransitiveTernaryHeadBound.lean) | Sharpens the transitive $3$-group head estimate by iterating the literal three-block cover.  The actual faithful top action is retained at every step and the literal block kernel contributes `ternaryIndexWidth`; hence degrees $3$, $9$, and $27$ have elementary ternary quotient ranks at most $1$, $2$, and $5$.  This is the simultaneous-head half of the classification-free ternary owner recurrence. |
| [PermutationPGroupSection](SymmetricSubgroupAsymptotics/PermutationPGroupSection.lean) | A reusable prime-uniform theorem for quotients of permutation subrepresentations.  A trivial quotient factors through the exact coinvariants, and the full invariant space of any equivariant quotient is pulled back to its literal preimage.  A central semiregular element then gives the uniform dimension bound `degree / p`. |
| [TernaryThreeBlockKernelChart](SymmetricSubgroupAsymptotics/TernaryThreeBlockKernelChart.lean), [TernaryThreeGroupQuotientEpi](SymmetricSubgroupAsymptotics/TernaryThreeGroupQuotientEpi.lean) | Constructs coherent three-point fibre charts for every transitive ternary group, proves all binary transitions vanish, and embeds the complete correlated block kernel as a literal subrepresentation of the ternary function-permutation module on the actual block set.  The reversible chart descends along every original normal subgroup.  For every non-base block set, the descended section retains its exact quotient action and has invariant dimension at most one third of the number of blocks.  Proper diagonal and subdirect kernel images are retained rather than enlarged to the full coordinate product.  The resulting one-layer epimorphism theorem keeps the exact quotient top, section module, first cohomology, and same complete source. |
| [TernaryThreeGroupEpiRecurrence](SymmetricSubgroupAsymptotics/TernaryThreeGroupEpiRecurrence.lean) | Iterates the arbitrary-normal one-layer theorem while retaining the complete source character rank.  The checked exponents are `d`, `d+b/3`, and `d+4b/3` in degrees 3, 9, and 27.  It derives generic binary slopes `16/15` and `8/3` in degrees 9 and 27 and the separate marked degree-nine slope `8/9`; the marked improvement is not used inside degree 27. |
| [TernaryThreeGroupPhysicalOwner](SymmetricSubgroupAsymptotics/TernaryThreeGroupPhysicalOwner.lean) | Installs the unrestricted degree-27 quotient theorem through the literal original-normal sum and original action normalizer.  It also provides a source-restricted degree-nine physical owner whose explicit premise requires every surviving Goursat map to retain the one-regular-`C3`, no-natural-`A4` source pattern. |
| [PermutationChiefWeight](SymmetricSubgroupAsymptotics/PermutationChiefWeight.lean) | Every genuine chosen-chief ternary weight is bounded by the three-adic valuation of the point-degree factorial; small-degree density bounds need no classification assumption. |
| [OriginalNormalChiefHead](SymmetricSubgroupAsymptotics/OriginalNormalChiefHead.lean) | Every original normal subgroup's relative ternary head is bounded by any chosen chief weight of its finite ambient group, using B(1)=1. At original permutation degrees ≤2, ≤5 and ≤8, the respective head bounds are 0, 1 and 2. |
| [FaithfulFiniteActionImage](SymmetricSubgroupAsymptotics/FaithfulFiniteActionImage.lean), [FaithfulNaturalChiefFamilies](SymmetricSubgroupAsymptotics/FaithfulNaturalChiefFamilies.lean) | An explicit point labelling preserves the faithful original action, normal character head and chosen chief weight. If its permutation image contains the natural alternating group at degree at least five, the original ambient has an actual chief series of ternary weight zero and every original normal subgroup has relative ternary head zero. |
| [TransitiveHeadDegreeInduction](SymmetricSubgroupAsymptotics/TransitiveHeadDegreeInduction.lean) | Strong degree induction on original finite faithful transitive actions, conditional on primitive head and chosen-chief-weight bounds and a scalar recurrence. Selected degrees can instead use a bound on every original transitive normal pair; recursion retains the actual top range and normal image. |
| [SubgroupIndexJordanHolder](SymmetricSubgroupAsymptotics/SubgroupIndexJordanHolder.lean), [SubnormalCompositionIndices](SymmetricSubgroupAsymptotics/SubnormalCompositionIndices.lean), [ChiefCompositionTernaryCount](SymmetricSubgroupAsymptotics/ChiefCompositionTernaryCount.lean) | Proved matching of actual composition-factor orders; every chosen chief weight is bounded by the order-three factor count in any supplied actual composition series. An existence corollary supplies a chief series with that bound. |
| [FiniteGeneratorNormality](SymmetricSubgroupAsymptotics/FiniteGeneratorNormality.lean), [FiniteCompositionWitness](SymmetricSubgroupAsymptotics/FiniteCompositionWitness.lean), [FiniteActionCompositionWitness](SymmetricSubgroupAsymptotics/FiniteActionCompositionWitness.lean) | Generator-conjugation words prove actual relative normality. Actual composition chains and verified quotient orders then bound every chosen chief weight in the original faithfully labelled action. Literal row certificates and complete action recognition remain required. |
| [FiniteGeneratorCompositionWitness](SymmetricSubgroupAsymptotics/FiniteGeneratorCompositionWitness.lean) | Sparse Cayley certificates and injective rows prove actual orders along a literal generator chain. Inclusion and conjugation words, prime adjacent order ratios, and exact endpoints produce a composition certificate and bound every chosen chief weight. This adapter covers soluble chains; individual row certificates and complete action recognition remain required. |
| [PrimitiveCompositionPilot3P2](SymmetricSubgroupAsymptotics/PrimitiveCompositionPilot3P2.lean) | Instantiates the sparse adapter on the recorded primitive degree-three, index-two source generators and literal chain. Kernel-checked rows of sizes 1, 3 and 6 prove prime quotient orders 3 and 2, original primitivity, and every chosen chief weight at most 1. This is one original action, with no catalogue completeness premise or conclusion. |
| [TernaryStabilityArithmetic](SymmetricSubgroupAsymptotics/TernaryStabilityArithmetic.lean), [TransitiveTernaryStability](SymmetricSubgroupAsymptotics/TransitiveTernaryStability.lean) | Concrete numerical stability and its degree-eighteen bypass, with the scalar recurrence proved. Primitive head/weight bounds and complete degree-eighteen normal-pair bounds remain explicit inputs. |
| [CharacterEpimorphismBound](SymmetricSubgroupAsymptotics/CharacterEpimorphismBound.lean), [BinaryIrreducibleTuple](SymmetricSubgroupAsymptotics/BinaryIrreducibleTuple.lean) | The original target-automorphism/class-character bound and construction of its faithful irreducible tuple from actual central involutions. |
| [BinaryCharacterEnvelope](SymmetricSubgroupAsymptotics/BinaryCharacterEnvelope.lean), [BinaryCharacterFusion](SymmetricSubgroupAsymptotics/BinaryCharacterFusion.lean) | The original arbitrary-source bound `Epi(J,Q) ≤ Aut(Q) 2^(z log₂(38/25)b)` for finite binary targets; exact criterion gaps and survival-restricted fusion input. Only the stated nilpotent class-count theorem remains external. |
| [BinaryPairCertificateCapacity](SymmetricSubgroupAsymptotics/BinaryPairCertificateCapacity.lean) | Checked original subgroup orders determine the literal central-cut dimension and original quotient capacity; a physical gap additionally requires equality of certificate width and actual degree. |
| [BinaryPhysicalPairCertificate](SymmetricSubgroupAsymptotics/BinaryPhysicalPairCertificate.lean), [BinaryNormalFiniteEntry](SymmetricSubgroupAsymptotics/BinaryNormalFiniteEntry.lean), [BinaryPairSharedFiniteEntry](SymmetricSubgroupAsymptotics/BinaryPairSharedFiniteEntry.lean) | Exact pair, character or literal carrier alternatives for the same original normal subgroup. Pair gaps use the actual physical degree and retained cut. Shared registries require explicit resolution of every exceptional axis. |
| [BinaryNormalFiniteEntry16](SymmetricSubgroupAsymptotics/BinaryNormalFiniteEntry16.lean), [BinaryNormalCharacterFiniteEntry16](SymmetricSubgroupAsymptotics/BinaryNormalCharacterFiniteEntry16.lean) | All-normal typed entries for the selected original actions 16T1086, 16T1184 and 16T1391. These are selected action results; full degree-sixteen action coverage and counting envelopes remain separate. |
| [BinaryCarrierOriginal](SymmetricSubgroupAsymptotics/BinaryCarrierOriginal.lean) | The checked chart acts directly on the original source and normal quotient, with exact kernel, reversible reconstruction, arbitrary exterior, full carrier projection and injectivity. Earlier-owner acceptance and its weighted estimate are not consequences of reconstruction alone. |
| [BinaryCarrierSurvival](SymmetricSubgroupAsymptotics/BinaryCarrierSurvival.lean) | Exact bijection of full fixed-axis families through the same literal Goursat data, agreeing with checked carrier transport. Arbitrary survival conditions and weights are retained on the reconstructed original subgroup, without a 2-group hypothesis. Earlier-owner membership and its estimates remain separate. |
| [BinaryCarrierEpiSurvival](SymmetricSubgroupAsymptotics/BinaryCarrierEpiSurvival.lean) | The same carrier transport gives exact surviving-epimorphism counts and arbitrary original weights for each fixed literal complement group. The actual original quotient is retained through its checked equivalence. An intrinsic carrier envelope transfers only after its acceptance implication is proved; no owner acceptance or decay is assumed away. |
| [BinaryFiniteEntryFusion](SymmetricSubgroupAsymptotics/BinaryFiniteEntryFusion.lean) | Exact finite entries feed the physical finite-menu sum with the original action normalizer. Pair gaps and the character epimorphism bound are derived from their checked interfaces; pair/carrier envelopes, character majorants, the stated class-count input and same-source moments remain explicit hypotheses. |
| [BinaryPhysicalPairMoments](SymmetricSubgroupAsymptotics/BinaryPhysicalPairMoments.lean) | The recorded pair cover descends faithfully to the exact quotient by the pair kernel and original normal subgroup. Its quotient-epimorphism and binary-character weight has a proved moment in degree `b + q*(s + 2*c)`, retaining one complete source subgroup in every factor. The envelope below uses this same certificate and weight. |
| [BinaryPhysicalPairEnvelope](SymmetricSubgroupAsymptotics/BinaryPhysicalPairEnvelope.lean) | Proves the matching local envelope for every physical pair certificate and every complete original source, with arbitrary survival predicates. The actual post-cut translation and first-cohomology factors remain explicit, and the Sylow-kernel rank bound is derived. It uses exactly the canonical moment weight. Coherent certificate selection, other entry branches, complete family coverage and the final weighted recurrence remain separate. |
| [BinaryPhysicalPairParameters](SymmetricSubgroupAsymptotics/BinaryPhysicalPairParameters.lean), [BinaryPhysicalPairFusion](SymmetricSubgroupAsymptotics/BinaryPhysicalPairFusion.lean) | A fixed certificate selection for each original normal axis supplies the graph degree, lift constant and a gap of at least `1/16`. The matching envelope and all moments give the original-normalizer physical bound and a finite-family forward recurrence with a proved contractive row. Absent certificates require actual zero survival; the selection is independent of the exterior subgroup and ambient degree. Complete physical family coverage remains an input, as does the coarse subgroup estimate for hot decay. Other branches and the complete T1 recurrence remain separate. |
| [PrimeSubdirectNormalHead](SymmetricSubgroupAsymptotics/PrimeSubdirectNormalHead.lean) | For any original normal subgroup of a full subdirect product, bounds its invariant-character dimension by those of its exact image and literal first-axis kernel. The two terms retain conjugation by the entire original factors, which may be nonabelian. The axis and derived-subgroup inclusions are proved. |
| [PrimeCharacterSubgroupCapacity](SymmetricSubgroupAsymptotics/PrimeCharacterSubgroupCapacity.lean), [PrimeSubdirectNormalRank](SymmetricSubgroupAsymptotics/PrimeSubdirectNormalRank.lean), [PrimeSubdirectJointCapacity](SymmetricSubgroupAsymptotics/PrimeSubdirectJointCapacity.lean) | Exact finite maxima over original derived normal subgroups and a shared cardinal budget give the coupled character/normal-head transition for every finite full subdirect core and every prime. With the actual retained character increment `δ` and positive derived-normal increment `ε`, proves `δ ≤ k`, `ε ≤ m`, and `δ+ε ≤ log_p(card(axis))`. The original axis and extendibility cut remain explicit; the cohomology increment is a separate step. |
| [PrimeFrattiniSurjection](SymmetricSubgroupAsymptotics/PrimeFrattiniSurjection.lean), [BinarySubdirectInflation](SymmetricSubgroupAsymptotics/BinarySubdirectInflation.lean) | Surjections map actual prime evaluation kernels onto one another, including Frattini subgroups of finite p-groups. Applied to the full subdirect projection, the exact terminal transgression identity bounds the H²-defect increment by the whole-factor invariant head of the literal evaluation-kernel axis. |
| [PrimeRelativeRadical](SymmetricSubgroupAsymptotics/PrimeRelativeRadical.lean), [PrimeRelativeHeadChainCapacity](SymmetricSubgroupAsymptotics/PrimeRelativeHeadChainCapacity.lean), [PrimeSubdirectRadicalCapacity](SymmetricSubgroupAsymptotics/PrimeSubdirectRadicalCapacity.lean), [BinarySubdirectJointTransition](SymmetricSubgroupAsymptotics/BinarySubdirectJointTransition.lean) | Evaluation on all whole-factor invariant characters defines the actual radical `R`, with exact index `p^k`. It lies in the literal evaluation-kernel axis `P`; the retained dimension and the rank of `P/R` share the bound `δ + rank(P/R) ≤ k`. This proves the sharp H² transition `τ(K) ≤ τ(B)+k−δ+a₂` together with the coupled `δ, ε` constraints for the same finite full subdirect core, including nonabelian cores. Here `a₂` is the actual relative head of `R`. Actual finite rank-row bindings and the complete mixture remain separate. |
| [PrimeRelativeRadicalPresentation](SymmetricSubgroupAsymptotics/PrimeRelativeRadicalPresentation.lean), [PrimeRelativeRadicalGenerators](SymmetricSubgroupAsymptotics/PrimeRelativeRadicalGenerators.lean) | For every prime and actual normal subgroup, the invariant-character radical is exactly the subgroup generated by pth powers together with ambient commutators. Powers of any actual generating family suffice; an additional family generating the ambient commutator subgroup gives the exact combined-tuple presentation. No finiteness or p-group premise is needed. Proving that the selected finite records supply those generating families and numerical ranks remains separate. |
| [JointCapacitySupport](SymmetricSubgroupAsymptotics/JointCapacitySupport.lean), [BinaryMarkedSubdirect](SymmetricSubgroupAsymptotics/BinaryMarkedSubdirect.lean) | The joint finite capacity polygon has a subadditive support function. The actual subdirect transition controls the mark `x*d+y*rho+z*tau` for arbitrary real `x` and nonnegative `y,z`, including the terminal case `x=j−ell<0`. Both inequalities concern the same original full subdirect subgroup and retain its radical head. |
| [JointCapacityHistory](SymmetricSubgroupAsymptotics/JointCapacityHistory.lean) | Iterating support subadditivity bounds a finite row history by its initial marks and one directed interaction for each earlier/later pair. The symmetric pair bound and terminal specialization retain the full `j<ell` region. These numerical rows still require their actual group certificates. |
| [FullSubdirectGoursat](SymmetricSubgroupAsymptotics/FullSubdirectGoursat.lean), [BinaryMarkedGoursatPeel](SymmetricSubgroupAsymptotics/BinaryMarkedGoursatPeel.lean) | A full subdirect subgroup is recovered from its literal normal axis and one actual epimorphism from the same tail. This injective coding derives the weighted one-step recurrence for finite 2-groups, combining the proved joint capacity and structured epimorphism bounds. Arbitrary nonnegative axis weights and original survival predicates are retained, with a negative first mark allowed. No automorphism divisor, numerical row premise or supplied recurrence is used. Whole-word induction, actual finite row bindings and complete owner coverage remain separate. |
| [SubdirectTailImage](SymmetricSubgroupAsymptotics/SubdirectTailImage.lean) | Restricting the second coordinate to the original subgroup's literal tail image gives a concrete multiplicative equivalence to a full subdirect core. Its original axis and all full tail coordinates are retained, and mapping back recovers the entire subgroup. Recording the tail and this core is injective, providing the family map needed for word induction. |
| [BinaryMarkedInvariantsCongr](SymmetricSubgroupAsymptotics/BinaryMarkedInvariantsCongr.lean), [BinaryMarkedTailImage](SymmetricSubgroupAsymptotics/BinaryMarkedTailImage.lean) | Actual finite-group equivalences preserve the character rank, the maximum over original derived normals, and the actual terminal H²-kernel dimension. Applying this to the literal tail image preserves all three marks together and proves the marked transition for the original product subgroup. No p-group hypothesis is needed for this transport. |
| [BinaryMarkedTailFamily](SymmetricSubgroupAsymptotics/BinaryMarkedTailFamily.lean) | The exact tail-image injection lifts the marked peel to an arbitrary family of literal tail subgroups. Original survival is transported through exact reconstruction, and nonnegative weights can depend on that tail and the original normal axis. Every summand uses the same tail for its epimorphism count and all marks. Selected tails must actually be 2-groups; a binary ambient product supplies this. Full word induction and terminal attachment remain separate. |
| [BinaryCarrierConeData](SymmetricSubgroupAsymptotics/BinaryCarrierConeData.lean), [BinaryCarrierConeA](SymmetricSubgroupAsymptotics/BinaryCarrierConeA.lean), [BinaryCarrierConeB](SymmetricSubgroupAsymptotics/BinaryCarrierConeB.lean), [BinaryCarrierConeBounds](SymmetricSubgroupAsymptotics/BinaryCarrierConeBounds.lean) | Exact rational square decompositions and nonnegative matrix remainders prove both carrier-cone inequalities on the full original rectangle, including `j<ell`. The resulting energy bound has coefficients `139/328` and `627/2624`; substituting mass `4*T` gives the exact reserves `(25/82)*R*T` and `(29/164)*T^2`. This is a universal real inequality. Actual group-to-row certification, word counting and terminal attachment remain separate. |
| [BinaryCarrierHistoryEnergy](SymmetricSubgroupAsymptotics/BinaryCarrierHistoryEnergy.lean) | Individual row and distinct-pair support certificates imply the six-colour history energy bound. Exact mass aggregation counts each unordered pair once and adds only nonnegative diagonal terms, giving the quadratic divisor `128` and the full-rectangle reserve. The input inequalities are explicit per-row certificates; this theorem does not identify concrete group rows. |
| [BinaryRelativeIndexTwoRadical](SymmetricSubgroupAsymptotics/BinaryRelativeIndexTwoRadical.lean), [BinaryCarrierRank8T26Normal3](SymmetricSubgroupAsymptotics/BinaryCarrierRank8T26Normal3.lean) | An original ambient-normal index-two section kills squares and mixed commutators; a reverse square witness identifies the actual radical. A selected literal order-four axis in the original `8T26` action has certified `(k,n,m,a₂)=(1,2,1,1)`, with its maximum taken over all original ambient normals. This is one selected row's rank binding; quotient centre/derived fields and the other rows remain separate. |
| [PGroupNormalIndexP](SymmetricSubgroupAsymptotics/PGroupNormalIndexP.lean), [PGroupNormalSubgroupCount](SymmetricSubgroupAsymptotics/PGroupNormalSubgroupCount.lean), [PGroupDerivedNormalSubgroupCount](SymmetricSubgroupAsymptotics/PGroupDerivedNormalSubgroupCount.lean) | Actual ambient-normal subgroups of bounded p-power index are counted through central prime steps and whole-ambient invariant characters. Inside the derived subgroup, the canonical maximum `rho` gives the bound `p^(a*rho)` with no subgroup-rank monotonicity assumption. |
| [PrimeFrattiniGenerators](SymmetricSubgroupAsymptotics/PrimeFrattiniGenerators.lean), [CentralizingHomCount](SymmetricSubgroupAsymptotics/CentralizingHomCount.lean), [CentralizerCosetCode](SymmetricSubgroupAsymptotics/CentralizerCosetCode.lean), [BinaryStructuredEpiFibre](SymmetricSubgroupAsymptotics/BinaryStructuredEpiFibre.lean), [BinaryStructuredTupleEpi](SymmetricSubgroupAsymptotics/BinaryStructuredTupleEpi.lean), [BinaryStructuredEpimorphisms](SymmetricSubgroupAsymptotics/BinaryStructuredEpimorphisms.lean), [BinaryStructuredEpiPolynomial](SymmetricSubgroupAsymptotics/BinaryStructuredEpiPolynomial.lean) | For every finite 2-group source and target, proves `#Epi(G,Q) ≤ C_Q*(d₂(G)+2)^C_Q*2^(log₂|Z(Q)|*d₂(G)+log₂|Q′|*rho₂(G))`, with an explicit positive target-only constant. Actual Frattini generators, their padded subtuples, the original normal `D ∩ ker f`, left centralizer cosets, and central map differences give a self-contained proof. No class-count hypothesis, bounded source alphabet, or automorphism divisor is used. Applying this source-specific theorem to arbitrary exterior groups and completing the weighted carrier recurrence remain separate. |
| [BinaryTargetOrderEnvelope](SymmetricSubgroupAsymptotics/BinaryTargetOrderEnvelope.lean), [BinaryTargetOrderMoments](SymmetricSubgroupAsymptotics/BinaryTargetOrderMoments.lean) | For every finite binary target of order `2^a` and arbitrary finite original source `J`, a central-series fibre argument proves `#Hom(J,Q) ≤ 2^(a*d₂(J))`. Its binary-character majorant has all same-source moments in degree `b+2*a*q`, without a class-count or permutation-generator theorem. This gives a fusion alternative when `2*a` is less than the original physical width; it does not cover every character-entry criterion or assert a faithful target action of degree `2*a`. |
| [BinaryStructuredPolynomialBound](SymmetricSubgroupAsymptotics/BinaryStructuredPolynomialBound.lean) | The original source-order bound `|G|≤2^s` and a common bound on the explicit target constants control the structured polynomial by `C*(s+2)^C`. A product of `t` such factors is at most `(C*(s+2)^C)^t`. Both actual center/derived exponential slopes remain unchanged; source-order and target-alphabet bounds still need their actual applications. |
| [BinaryCarrierSourceOrder](SymmetricSubgroupAsymptotics/BinaryCarrierSourceOrder.lean) | An injective original coordinate map with factor orders at most `2^(a_i)` bounds the source order by `2^(sum a_i)` and its binary character rank by `sum a_i`. This applies to every literal tail subgroup, including proper correlated tails, and supplies its uniform polynomial bound. A common target constant remains explicit. |
| [BinaryTargetOrderFusion](SymmetricSubgroupAsymptotics/BinaryTargetOrderFusion.lean) | A fixed choice of an actual pair certificate or the strict target-order gap, for each original normal axis, installs the matching envelope and all moments in the original-normalizer recurrence. Proves the contractive cold row; hot decay retains the coarse subgroup estimate. An unselected axis requires zero survival. Complete physical coverage and character cases outside this order criterion remain separate. |
| [OrdinaryRemainderAssembly](SymmetricSubgroupAsymptotics/OrdinaryRemainderAssembly.lean) | Exact partition of all actual subgroups into the complete critical family and its complement, in both parities. An exponential complement bound implies T1. A forward counting recurrence with exponential scalar and row bounds first proves contraction and total boundedness, then T1; the actual recurrence and decay bounds remain to be installed. |
| [OddMarkerCoefficientBounds](SymmetricSubgroupAsymptotics/OddMarkerCoefficientBounds.lean) | The exact odd current coefficient is at most `4*(N+1)` and the adjacent-rank predecessor coefficient is at most `2*eulerProduct⁻¹^2*(N+1)^3`. Both are nonnegative, and either polynomial factor is absorbed by half of any positive exponential rate. Thus the odd transfer introduces no independent analytic hypothesis. |
| [OrdinaryFrontierClosure](SymmetricSubgroupAsymptotics/OrdinaryFrontierClosure.lean) | Combines the even and odd repeated-marker inequalities into one ambient-degree frontier. Two explicit exponential forward certificates, one for the outside-`Fits` term and one for the parity-adjusted binary term, combine with the proved marker row to imply `T1` and then `AllTargets`. Total boundedness is derived by the recurrence; it is not assumed. The two physical producer certificates remain the final inputs. |
| [ForwardEstimateAlgebra](SymmetricSubgroupAsymptotics/ForwardEstimateAlgebra.lean) | Pointwise domination transports an exponential forward estimate to any smaller scalar/kernel pair, and two estimates add with the minimum decay rate while preserving nonnegative kernels. This is the reusable assembly rule for independent physical owner producers before they enter the single frontier closure. |
| [BinaryFrontierTransport](SymmetricSubgroupAsymptotics/BinaryFrontierTransport.lean) | Converts a native rank-indexed recurrence for `binaryErrorRatio N`, with targets below degree `2*N`, into the exact ambient-degree `binaryFrontierRatio` certificate. It pads both forward kernels, retains the current and predecessor odd coefficients, and proves exponential scalar and row decay at rate `rate/8`. Its native producer is `BinaryNativeRecurrence.rankForwardEstimate`. |
| [FiniteFirstOwnership](SymmetricSubgroupAsymptotics/FiniteFirstOwnership.lean) | Literal coverage by a finite ordered family gives a unique first eligible owner and an exact partition of retained original objects. Cardinalities and arbitrary additive weights are preserved. Two-way predicate transport preserves every earlier exclusion; actual eligibility and coverage remain application obligations. |
| [OrdinaryRemainderNaturality](SymmetricSubgroupAsymptotics/OrdinaryRemainderNaturality.lean) | The complete critical family and its complement are invariant under physical relabelling in both parities. Physical first-owner predicates retain every earlier exclusion and pull back to original-normalizer naturality. Literal coverage and physical eligibility invariance remain explicit. |
| [FusionPhysicalFilters](SymmetricSubgroupAsymptotics/FusionPhysicalFilters.lean) | Forming all physical relabellings commutes with every globally invariant filter on the entire original subgroup. This gives exact filtered-family identities, preserving the full local action and complete complement; it does not assert that an eligible orbit exists. |
| [OrdinaryFirstOwnerFiniteMenu](SymmetricSubgroupAsymptotics/OrdinaryFirstOwnerFiniteMenu.lean) | Applies the original-normalizer finite-menu bound to literal noncritical first-owner families. Exact filtering derives their coverage from unfiltered full-action coverage. Finite entries, actual eligible-orbit coverage, class-count bounds, branch envelopes and moments remain explicit. |
| [ModuleCoordinateHeads](SymmetricSubgroupAsymptotics/ModuleCoordinateHeads.lean), [InducedOrbitDecomposition](SymmetricSubgroupAsymptotics/InducedOrbitDecomposition.lean) | Actual finite-coordinate submodule head bounds and the original induced representation's equivariant double-coset support decomposition. |
| [BinaryMixtureCentralComparison](SymmetricSubgroupAsymptotics/BinaryMixtureCentralComparison.lean), [BinaryMixtureCyclicFour](SymmetricSubgroupAsymptotics/BinaryMixtureCyclicFour.lean) | Actual central-extension-to-split comparison preserving every exterior image and its weights, instantiated on C4 powers over arbitrary finite nonabelian exteriors. |

| [BinaryPairFrameGenerators](SymmetricSubgroupAsymptotics/BinaryPairFrameGenerators.lean), [BinaryPairSharedCutInstall](SymmetricSubgroupAsymptotics/BinaryPairSharedCutInstall.lean) | Original generator images construct the exact physical pair frame and top range; shared coordinate cuts yield original central-cut and full fixed-preimage certificates. |
| [NormalChiefSeries](SymmetricSubgroupAsymptotics/NormalChiefSeries.lean), [AbelianMinimalNormal](SymmetricSubgroupAsymptotics/AbelianMinimalNormal.lean), [ActualLocalChiefSteps](SymmetricSubgroupAsymptotics/ActualLocalChiefSteps.lean) | Existence of literal normal chief chains and installation of every actual elementary, coprime-order and nonabelian layer. Ternary weights count only abelian factors. |
| [MinimalNormalSimpleQuotients](SymmetricSubgroupAsymptotics/MinimalNormalSimpleQuotients.lean), [MinimalNormalSubdirect](SymmetricSubgroupAsymptotics/MinimalNormalSubdirect.lean), [PerfectSubdirect](SymmetricSubgroupAsymptotics/PerfectSubdirect.lean) | Actual jointly faithful simple quotient coordinates prove perfectness for proper subdirect nonabelian chief layers. |
| [RelativeSecondIsomorphism](SymmetricSubgroupAsymptotics/RelativeSecondIsomorphism.lean) | The exact character-space equivalence between the original sections N/(N∩K) and NK/K, with their literal ambient conjugation actions. |

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

The [general binary-exterior contraction](SymmetricSubgroupAsymptotics/OddMarkerBinaryContraction.lean)
removes the exponent-four restriction: an elementwise power `4^k` kills
the binary exterior lift and preserves the original A3 coordinate.
It proves exact subgroup, survival-predicate and original-weight transport
for every 2-group exterior, retaining its entire subgroup image.
The general S3 physical-profile reindexing and weight sum remain separate.
For repeated markers, the [original joint kernel](SymmetricSubgroupAsymptotics/RepeatedOddMarkerKernel.lean)
records all signs and the complete exterior together. Each full S3 coordinate
has a full A3 projection of this kernel; the kernel need not be a product.
The [diagonal projection theorem](SymmetricSubgroupAsymptotics/DiagonalIsotypeProjection.lean)
decomposes invariant subspaces by distinct scalar functions using explicit
separating operators, over any field and with no finite-source assumption.
The [actual ternary chart](SymmetricSubgroupAsymptotics/OddMarkerTernaryChart.lean)
identifies the original alternating subgroup with F3 and proves the literal
S3 conjugation formula. The [repeated-marker module](SymmetricSubgroupAsymptotics/RepeatedOddMarkerModule.lean)
then reconstructs the original joint kernel exactly from its F3 submodule,
proves its decomposition by the same original sign characters and retains
full coordinate projection under the actual binary-exterior hypothesis.
Complete cocycle fibres and the physical marker sum remain additional steps.

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
The terminal numerical double sum is bounded, including its large-d
endpoint. Actual H² diagonal and commuting-pair tests give an allowable
function space of dimension at most the retained inflation-kernel dimension
tau. The ordered-record incidence bound consequently retains the factor
`(72 * 2^tau)^ell`. `TerminalAttachmentBound` installs it on the actual
subgroups of the original critical product times the complete exterior T,
full on T and every nonabelian critical factor. The count is at most
`terminalGaussianDoubleSum r c d tau`, with the actual character rank
`d = d₂(T)` and retained inflation dimension tau. The proof includes all
quotient images, their full central fibres, the original record divisor,
and every relation dimension, including zero. Arbitrary extra conditions
define subfamilies with the same upper bound. `TerminalAttachmentEstimates`
gives uniform, endpoint, convergent-series and zero-inflation estimates,
and sums arbitrary nonnegative original profile weights. These physical
estimates have no additional counting or capacity hypothesis.

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
including arbitrary survival predicates and empty fibres. The finite-length
fractional-Schur bound is now proved over the original field, without
semisimplicity or algebraic-closure assumptions. Its intrinsic capacity
equals the actual socle multiplicity divided by the simple-module dimension
over its Schur division ring. The resulting original-lift bound is

    |surviving lifts| <= |A| |H1(B,A)| p^(r_B(A) dim_Fp(P/Phi(P))).

Here P is an actual Sylow subgroup of the original kernel, with its actual
normalizer action. Only the target action is inflated from B. The character
quotient is proved isomorphic to the actual Frattini quotient. The separate
permutation quotient-rank estimate `dim(P/Phi(P)) <= b/p` remains an explicit
input when substituting b/p. Shared-C3 checks compute the capacity over F2,
retain both translation factors on one shared source, and verify that a
trivial C3 action still attains the full binary exponent t².

The numerical fusion kernels retain the original factorials and action
divisor. Fixed-width cold kernels are exponentially small in the complete
complement degree. Positive-width hot kernels are quadratically small,
relative only to the explicit coarse counting input `1/16 + o(1)`.
Zero-width moment bounds force every retained weight to be at most one.
`FusionPhysicalCount` now proves physical orbit pointing with the original
normalizer divisor on the complete stable literal-axis sum. `FusionFiniteMenu`
then splits this numerical sum into hot and cold terms using only local epi
envelopes and same-source moments. `FusionPhysicalUnion` installs the resulting
recurrence on actual covering families of subgroups of S_n. No invariance of individual axes or source
envelopes is silently assumed. `FusionContinuationRow` retains different
removed widths at the same ambient degree and proves eventual row contraction.
The central-cut epi envelope and its full graph moment are now connected to
the actual original extension tower. Actual module charts and the named
permutation quotient-rank bound remain explicit inputs. The arbitrary-width extension normalizes every positive deletion width at its
actual complement degree, including odd widths. Its required strict slope
is floor(w/2)/4. Complete finite acceptance and family coverage remain
separate from this numerical implication.

The original imprimitive ternary recurrence is also proved in
[ImprimitiveChiefHead](SymmetricSubgroupAsymptotics/ImprimitiveChiefHead.lean).
It constructs all actual chief layers, including proper nonabelian subdirect
layers, and retains the original top section. Its proved coefficient is the
integer `ternaryIndexWidth s`, formed from actual Sylow/Mackey pieces; this
route requires no published prime-power module hypothesis. Its multiplier
is the sum of ternary abelian weights on an actual chief series of the
original local component. Chosen chief weight is bounded by the number of
order-three factors in any supplied actual composition series, using a
proved Jordan–Hölder matching of quotient indices. Finite records still
require actual series/count certificates and original-group bindings.
The earlier composition-length bound also remains available.
`PrimitiveCompositionTail` derives the strict bound
`10 W < 3 r` for every primitive degree `r >= 45`, conditional on the
precisely stated published `PrimitiveCompositionLengthInput`. That input,
the remaining small-degree cases and the high-cone installation remain
separate obligations. The minimal block quotient is itself constructed from
a cover of the original point stabilizer. Its local component is primitive
on the unchanged fibre, and its top is the faithful original permutation
range. The exact degree product makes both degrees smaller.
[TransitiveHeadDegreeInduction](SymmetricSubgroupAsymptotics/TransitiveHeadDegreeInduction.lean)
proves the resulting strong degree induction with explicit primitive head
bounds, chosen chief series with bounded weight, and the scalar inequality
`g(r) * B(s) + f(s) <= f(r*s)`. A finite set of degrees may instead use
bounds for every original transitive normal pair at those degrees; the
primitive head and scalar premises then apply outside that set. Concrete
primitive inputs, finite coverage and high-action ownership remain to be installed.

The concrete stability installation uses `g(r) = r/3` with natural division
and a head bound equal to one in degrees three and four, two in degrees
nine and eighteen, and `5w/27` otherwise. Its scalar inequality is proved
outside total degree eighteen. That degree uses an explicit bound for all
original transitive normal pairs. Primitive chosen weights at most `r/3`
and strict primitive heads `20d < 3r` outside degrees three, four and eighteen
remain inputs. The installation does not classify the exceptional actions
within degrees three, four or nine.

[OriginalNormalChiefHead](SymmetricSubgroupAsymptotics/OriginalNormalChiefHead.lean)
also proves that the relative ternary head of any `N` normal in a finite
group `A` is at most the weight of any chosen actual chief series of `A`.
It uses the original inclusion and ambient conjugation at index one,
with `B(1)=1`. No permutation, transitivity or primitivity assumption is
needed for this helper. Its permutation corollaries use the factorial
valuation bound without identifying chief weight with composition length.

[FaithfulFiniteActionImage](SymmetricSubgroupAsymptotics/FaithfulFiniteActionImage.lean)
uses an explicit labelling `Ω ≃ Fin n` to identify a faithful action with
its literal permutation image. It preserves transitivity and primitivity,
the original normal subgroup with its ambient conjugation, the relative
character head, and the weight of a chosen actual chief series.
[FaithfulNaturalChiefFamilies](SymmetricSubgroupAsymptotics/FaithfulNaturalChiefFamilies.lean)
then installs the existing zero-weight alternating and symmetric families
when that image contains `A_n` and `n >= 5`. The alternating inclusion
remains an explicit recognition hypothesis; primitive classification and
the remaining global primitive bounds are separate obligations.

The first c=1 application proves the physical factor `n!/(6 m!)` times the
exact surviving split-character sum on the complete complement. Its unrestricted
weight is `3^d₃(K)−3^h₃(K)`; a survival predicate remains inside that count.
The inverse-complement formula is an exact reversible reindexing with weight
`1/|{y in Nx : orderOf y=3}|`. Binary-kernel inflation preserves characters,
splitting and all these surviving weights. These identities do not yet prove
the required high-cone exhaustion by earlier owners or the final c=1 bound.

Simultaneous binary transport now reconstructs the literal original subgroup
from the full replacement relation, including nonabelian proper subdirect
carriers. Four exceptional charts have literal kernel-checked quotient maps,
both exact kernels, and physical block projections. Their exporter reads
the committed finite menu; Lean checks each generated witness. The
degree-sixteen carrier is its actual proper joint image, and the auxiliary
quotient degree is never charged as physical support. The generic registry
coverage implications are proved, with all four original Sylow roots now
installed by structural wreath-product proofs and short generator words.
All transitive binary actions of degrees 2, 4 and 8 are covered by checked
original-point conjugacies. The complete degree-16 action registry remains to be installed. The degree-8
nonbase normal registries cover all 203 states, and every state is installed
in its physical-pair, exact character-criterion or original transport branch.
The 190 physical pairs have actual capacity and central-prefix bounds.
The shared coordinate route also has generic proofs identifying the whole
original flip kernel from Schreier words, certifying an exact fixed preimage
by a sparse linear factor, and excluding central quotient classes by either
faithful kernel action or a nonsplit affine obstruction. These generic
lemmas do not replace the remaining concrete finite certificate checks.
The [order-pruned coverage theorem](SymmetricSubgroupAsymptotics/BinaryOrderPrunedCoverage.lean)
installs the numeric target-order selection on every original normal quotient
when `card U ≤ 2^a` and `2*a < w`. For binary actions this accepts all actions
of order at most 128 in degree 16, including their descendants on the same
points. Its registry theorem needs only high-order transitive children;
the dual normal registry stops at small quotient index. The binary-group
hypothesis remains explicit at every fusion use: small order alone does
not prove the binary epimorphism bound. Concrete high-order coverage is
still required.
The [combined order-or-character consumer](SymmetricSubgroupAsymptotics/BinaryOrderCharacterFusion.lean)
accepts a fixed certificate for every literal original normal. It retains
the original action normalizer, target automorphism factor, surviving maps
and all marker moments, and proves the finite-family continuation row
eventually contracts. Its character counting branch takes the named
nilpotent conjugacy-class input; hot decay separately takes the global
coarse subgroup-growth input.
The [direct first-moment consumer](SymmetricSubgroupAsymptotics/BinaryOrderCharacterDirectFusion.lean)
also proves a forward recurrence for the same complete finite menu, with
no hot term or coarse subgroup-growth premise. It continues at the actual
graph degree `m = n - w + v < n`, retaining every literal original normal
and the original action normalizer. The [exact physical assembly](SymmetricSubgroupAsymptotics/FusionDirectPhysicalUnion.lean)
and [direct coefficient decay](SymmetricSubgroupAsymptotics/FusionDirectDecay.lean)
prove exponential decay of the complete finite row before bounding any
unknown subgroup count. The character class-count input remains explicit.
The [uniform coefficient estimate](SymmetricSubgroupAsymptotics/FusionDirectUniform.lean)
retains the quadratic width loss for every complement degree: its exponent
is `-2*e*b - (h^2-r^2)/4 + (h-r+1)/4`, its polynomial degree is `h+r+1`,
and its factor remains the original `D/a(U)`. A growing-menu argument must
still bound the sum of those original factors; the coefficient estimate
does not supply that group-theoretic input.
The [growing-width numerical sum](SymmetricSubgroupAsymptotics/FusionDirectAggregate.lean)
proves an eventual `C * 2^(-n/16)` bound when every original entry has
`v ≤ 13*w/16`, gap `16*e ≥ w/32`, and the full original weighted menu at
width `w ≥ 64` satisfies `sum (D/a) ≤ 2^(w^2/128+H)` for one fixed `H`.
Its threshold is uniform across widths. The menu-mass bound and actual
physical coverage remain explicit requirements, not consequences of
the numerical aggregation.
The [wide direct row](SymmetricSubgroupAsymptotics/FusionWideDirectRow.lean)
assigns every one of those entries to `m=n-w+v<n`, proves that its row sum
is exactly the checked aggregate, and derives decay and eventual
contraction. Entries sharing a target degree are all retained.
The [degree-sixteen application](SymmetricSubgroupAsymptotics/BinaryTransitiveBoundary16Fusion.lean)
accepts all transitive binary actions of order at most 256, including every
original normal, without enumerating groups or normals. A nontrivial normal
leaves a quotient of order at most 128. For the remaining trivial normal,
the [faithful central-action argument](SymmetricSubgroupAsymptotics/FaithfulTransitiveCentralCard.lean)
bounds the central involution dimension by three in the nonregular case,
and the [exact character criterion](SymmetricSubgroupAsymptotics/BinaryTransitiveCentralCriterion.lean)
then applies. The complete finite subtype of all these original actions
has its own recurrence and contractive aggregate; physical family coverage,
naturality, the class input and hot coarse-growth input remain explicit.
The [actual degree-sixteen sector](SymmetricSubgroupAsymptotics/BinarySmallOrbit16Physical.lean)
supplies this coverage for the unmarked set of original subgroups admitting
a genuine sixteen-point orbit chart with binary restriction image of order
at most 256. Its [direct recurrence](SymmetricSubgroupAsymptotics/BinarySmallOrbit16Direct.lean)
proves both coverage and naturality and has an exponentially decaying row,
with only the named class-count input retained. Arbitrary earlier-owner
restrictions decrease the left-hand cardinality without adding chart
multiplicity. This is a sector bound, not coverage of every subgroup.
The [power-degree extension](SymmetricSubgroupAsymptotics/BinaryTransitivePowerBoundaryFusion.lean)
proves the same complete selection for every original transitive action of
degree `w = 2^k ≥ 16` and order at most `2^(w/2)`. Nontrivial normals save
one order bit, and a large source's bottom axis satisfies the
[uniform character criterion](SymmetricSubgroupAsymptotics/BinaryTransitivePowerCharacterCriterion.lean).
Any fixed finite family, including different such widths, has the original
weighted recurrence and contractive row. This does not bound the aggregate
over an unbounded family of widths.
The [actual power-degree sector](SymmetricSubgroupAsymptotics/BinarySmallOrbitPowerDirect.lean)
also constructs the complete physical cover for every fixed `k ≥ 4`.
It counts the unmarked original subgroups with such an orbit chart and
proves the direct recurrence and aggregate decay at that fixed degree.
The character class-count premise remains; no constants or thresholds
are asserted uniformly as `k` grows.
The [intrinsic orbit formulation](SymmetricSubgroupAsymptotics/BinarySmallOrbitPowerIntrinsic.lean)
states membership directly through an actual orbit and its faithful image.
The [orbit chart construction](SymmetricSubgroupAsymptotics/FusionActualOrbitCharts.lean)
proves the required labelling, exact two-restriction reconstruction and
image equivalence internally. Its unmarked injection adds no point or
chart multiplicity and requires no binary assumption on the full original
subgroup or its complement.
The [binary induced-module head theorem](SymmetricSubgroupAsymptotics/BinaryInducedHead.lean)
proves the intrinsic coinvariant bound `dim(V) * choose(t,t/2)` for an
actual representation injected into a coinduced module from index `2^t`
in a finite 2-group. It constructs the subgroup-chain coordinates and
uses the Boolean antichain bound, with no supplied module-capacity input.
The corresponding original induced-subrepresentation and invariant-character
bounds hold over the stated fields.
The [all-normal binary induction](SymmetricSubgroupAsymptotics/TransitiveBinaryNormalHead.lean)
now bounds the relative character head of every original normal subgroup
by `A_k = sum_{j<k} choose(j,j/2)` in degree `2^k`. Its
[permutation adapter](SymmetricSubgroupAsymptotics/PermutationBinaryHead.lean)
and [pair-kernel adapter](SymmetricSubgroupAsymptotics/BinaryPairNormalHead.lean)
retain the exact normal intersection, the original conjugation action and
the actual top image. The
[normal-count consequence](SymmetricSubgroupAsymptotics/TransitiveBinaryNormalCount.lean)
gives at most `2^(a*A_k)` original normals when `card U ≤ 2^a`,
and at most `2^((2^k-1)*A_k)` directly from the permutation degree;
the [generator theorem](SymmetricSubgroupAsymptotics/TransitiveBinaryGenerators.lean)
constructs an actual generating tuple of length `A_k`. These discharge
their rank inputs internally.
The [action-count adapter](SymmetricSubgroupAsymptotics/TransitiveBinaryActionCount.lean)
bounds every family separated by actual permutation conjugacy by the
same `2^((2^k-1)*A_k)`. It injects chosen original generating tuples
into one chosen Sylow subgroup, whose exact order is proved in
[BinaryPermutationOrder](SymmetricSubgroupAsymptotics/BinaryPermutationOrder.lean).
The [trivial-section adapter](SymmetricSubgroupAsymptotics/PermutationBinaryTrivialSection.lean)
bounds an actual trivial quotient through its original preimage's
coinvariants. No embedding of the section is assumed.
The [whole-subspace count](SymmetricSubgroupAsymptotics/BinarySubspaceTupleCount.lean)
bounds all actual subspaces of a binary space of dimension `d` by
`2^(d*d)`, using padded spanning tuples.
The [elementary width asymptotics](SymmetricSubgroupAsymptotics/BinaryWidthAsymptotics.lean)
prove `choose(k,k/2)/2^k → 0` and the same limit for the cumulative
widths `sum_{j<k} choose(j,j/2)`. An exact central-binomial recurrence
gives a square bound in both parities; no Stirling or group-theoretic
estimate is assumed.
The [actual pair-section bound](SymmetricSubgroupAsymptotics/BinaryPairSectionInvariantBound.lean)
controls its invariant dimension and counts all literal central cuts. The
[section cohomology bound](SymmetricSubgroupAsymptotics/BinaryPairSectionCocycleBound.lean)
retains the actual top quotient and the actual translation and H¹ factors.
The [frame sum](SymmetricSubgroupAsymptotics/BinaryPairFrameMenuMass.lean)
sums these costs over every original normal subgroup and central cut.
The [pair-system count](SymmetricSubgroupAsymptotics/TransitivePairingCount.lean)
bounds distinct equivariant partner functions by `w-1`. The
[frame construction](SymmetricSubgroupAsymptotics/BinaryPairFramePairing.lean)
chooses exactly one auxiliary chart for each realized pair system, and the
[original-action transport](SymmetricSubgroupAsymptotics/BinaryPairFrameTransport.lean)
constructs such a system for every positive power-degree transitive binary action.
The [complete weighted sum](SymmetricSubgroupAsymptotics/BinaryWideMenuMass.lean)
then bounds every conjugacy-separated original action family, including all
its realized pair systems, original normals and central cuts, with its original
normalizer divisor. The
[numerical menu exponent](SymmetricSubgroupAsymptotics/BinaryMenuExponentAsymptotics.lean)
and [uniform constant](SymmetricSubgroupAsymptotics/BinaryMenuExponentUniform.lean)
give a single `H ≥ 0`, independent of degree and action family, for the bound
`sum (D/a) ≤ 2^(w^2/128+H)`. The
[complete action classes](SymmetricSubgroupAsymptotics/BinaryTransitiveActionClasses.lean)
select one original subgroup per actual ambient-conjugacy class and prove
complete coverage and separation. The
[original orbit charts](SymmetricSubgroupAsymptotics/FusionOrbitRepresentativeCharts.lean)
transport every eligible original orbit into those representatives using the
same original subgroup on both coordinate projections.
The [complete entry index](SymmetricSubgroupAsymptotics/BinaryOriginalMenuEntries.lean)
now assembles the literal action-class, pair-system, original-normal and
central-cut indices. Its weighted sum equals the proved menu mass exactly,
and every literal accepted subtype inherits the same bound.
The [actual accepted row](SymmetricSubgroupAsymptotics/BinaryOriginalWideRow.lean)
installs that mass internally, proves forward support, exponential decay
and eventual contraction. Its numerical acceptance predicate alone does
not assert local envelopes for arbitrary nonzero cuts.
The [zero-cut parameters](SymmetricSubgroupAsymptotics/BinaryZeroCutWideParameters.lean)
prove that `w=2^(k+1)`, `v=2^k` and `r≤choose(k,k/2)` satisfy the required
wide-row inequalities for every `k≥11`. This numerical statement requires
an actual section-capacity and local-envelope application before it counts
any physical family.
The [zero-cut extension](SymmetricSubgroupAsymptotics/BinaryPairZeroCutExtension.lean)
identifies the exact kernel of `U/N → U/(K∨N)` and its original conjugation
action without assuming splitting. The
[actual zero-cut fusion theorem](SymmetricSubgroupAsymptotics/BinaryPairZeroCutFusion.lean)
derives its Schur capacity, original translation/H¹ coefficient, arbitrary
survival envelope and all same-source moments. Its faithful prefix is the
actual top group covering the quotient. Every original normal has the
required uniform gap at physical width at least 4096.
The [strict-gap refinement](SymmetricSubgroupAsymptotics/BinaryPairZeroCutPositiveFusion.lean)
proves `e≥w/2048>0` from physical width 1024, including `e≥1/2` and `e≥1`
at 1024 and 2048.
The [zero-entry installation](SymmetricSubgroupAsymptotics/BinaryOriginalZeroCutEntry.lean)
and [wide physical recurrence](SymmetricSubgroupAsymptotics/BinaryOriginalWidePhysical.lean)
now bound the unmarked family with a binary orbit of power degree at least
4096 by the proved forward, exponentially decaying original row. A single
pairing is chosen for each original action before the exterior is specified;
every original normal is retained. The complementary action is arbitrary.
The [finite-prefix recurrence](SymmetricSubgroupAsymptotics/BinaryOriginalFinitePrefixPhysical.lean)
proves the corresponding original-weight bound and contracting aggregate for
orbit degrees 1024 and 2048. Neither installation assumes class-count bounds,
coarse subgroup growth, or a supplied coverage/capacity estimate. Both allow
arbitrary additional ownership exclusions by literal subtype inclusion.
The [combined intrinsic sector](SymmetricSubgroupAsymptotics/BinaryOriginalLargePhysical.lean)
derives the binary power degree from the actual orbit image and combines
these rows. Thus every subgroup with any binary orbit of size at least 1024
is covered by one original-weight forward recurrence, with exponentially
decaying aggregate and no supplied power-degree hypothesis.
The [finite small-pair recurrence](SymmetricSubgroupAsymptotics/BinaryOriginalSmallPairPhysical.lean)
now covers degrees 32, 64, 128, 256 and 512. For each original normal,
a small actual section supplies a proved central cut; a large actual
section forces a faithful top action and satisfies the proved character
criterion. The choice precedes the exterior group. The
[combined degree-at-least-32 sector](SymmetricSubgroupAsymptotics/BinaryOriginalNoncriticalPhysical.lean)
therefore counts every original subgroup with an actual binary orbit
image of degree at least 32. Its complete original-weight row is forward,
decays exponentially and is eventually contractive. It allows arbitrary
complementary actions and ownership exclusions. Global subgroup coverage,
the remaining smaller binary families, and nonbinary sectors remain separate.
The [general central-cut chart](SymmetricSubgroupAsymptotics/OriginalCentralCutExtension.lean)
constructs the original tower `Q → Q/C → B` from any supplied subspace
`C ≤ A^B`, with exact central and quotient kernel charts. Its
[fusion envelope](SymmetricSubgroupAsymptotics/OriginalCentralCutFusion.lean)
retains `|A/C|*|H¹(B,A/C)|` and the entire common-source weight
`#Epi(J,B)*2^(dim(C)*d₂(J))`; a faithful original cover of B supplies all
moments. Neither theorem assumes that B itself acts faithfully on those
cover points, or that the extension splits.
The independent [evaluation separator](SymmetricSubgroupAsymptotics/LinearMapEvaluationSeparator.lean)
constructs linearly independent detecting inputs from bounds on actual
image-line slices. The [central-cut arithmetic](SymmetricSubgroupAsymptotics/BinaryCentralCutNumerics.lean)
then gives the small-section cost bound for all pair exponents at least four.
The [actual small-section cut](SymmetricSubgroupAsymptotics/BinaryPairSmallSectionCut.lean)
and [large-section character alternative](SymmetricSubgroupAsymptotics/BinaryPairLargeSectionCharacter.lean)
install this dichotomy for every original pair section of pair degree
at least 16. The large branch identifies the entire central involution
subgroup of the original nonsplit quotient; it does not assert that the
small-cut inequality holds in that branch.
At pair degree eight, the [general small-dimension cut](SymmetricSubgroupAsymptotics/BinaryPairEightSmallSectionCuts.lean)
has cost at most twice the original section dimension. Together with the
[eight-pair character alternative](SymmetricSubgroupAsymptotics/BinaryPairEightLargeSectionCharacter.lean),
every original normal axis admits a strict cut, admits a character entry,
or has section dimension exactly four. This is a residual dimension
statement, not complete acceptance of degree-sixteen actions.
The [cocycle generator bound](SymmetricSubgroupAsymptotics/CocycleGeneratorBound.lean)
injects actual one-cocycles into their values on a supplied original
generating tuple, giving `card Z¹ ≤ (card A)^d` and the same upper bound
for the actual quotient `H¹`. It does not evaluate cohomology classes
on generators. The independent
[class-count extension theorem](SymmetricSubgroupAsymptotics/ConjugacyClassExtension.lean)
proves `k(G) ≤ k(N)*k(G/N)` for every finite group and original normal
subgroup, including nonabelian kernels. This extension inequality does
not itself establish the required permutation class-count envelope.
The [correlated-product bound](SymmetricSubgroupAsymptotics/SubgroupProductClassBound.lean)
filters the original group by coordinate kernels and bounds its class count
by the product of bounds for all actual coordinate subgroups. Its
[p-group specialization](SymmetricSubgroupAsymptotics/PGroupProductClassBound.lean)
requires these coordinate bounds only for p-subgroups. Neither theorem
assumes independent coordinates or monotonicity of class count under inclusion.
The [actual block kernel](SymmetricSubgroupAsymptotics/BlockKernelClassBound.lean)
uses jointly injective actions on the original fibres. The
[eight-point block construction](SymmetricSubgroupAsymptotics/BinaryEightPointBlocks.lean)
selects the needed stabilizer-chain prefix and proves the exact degree product.
The [class induction](SymmetricSubgroupAsymptotics/BinaryEightBlockClassInduction.lean)
then derives `k(G)^7≤5^(2*card X)` for every finite faithful binary action
from its degree-at-most-eight class base.
The [complete class theorem](SymmetricSubgroupAsymptotics/BinaryPermutationClassBound.lean)
now installs this base and proves the bound without a class-count hypothesis.
It does not assert the separate 38/25 bound for arbitrary nilpotent groups.
The [seven-power character envelope](SymmetricSubgroupAsymptotics/BinarySevenCharacterInstalled.lean)
installs this proved class bound for actual binary target epimorphisms,
retaining the original target automorphism factor and arbitrary survival.
The [complete finite-menu row](SymmetricSubgroupAsymptotics/BinaryOrderSevenCharacterDirectFusion.lean)
has no class-count premise: a literal physical cover yields a forward
ordinary-count recurrence whose aggregate decays exponentially.
The [degree-sixteen installation](SymmetricSubgroupAsymptotics/BinarySmallOrbit16SevenDirect.lean)
proves that cover for every actual binary orbit image of degree 16 and
order at most 256. It retains all original actions and normal axes,
arbitrary complementary actions, and arbitrary earlier-owner exclusions.
This sector does not require action-catalogue coverage or a coarse bound
on total subgroup counts. Larger-order degree-sixteen images remain separate.
The [bounded-width conversion](SymmetricSubgroupAsymptotics/BinarySmallWidthCharacterConversion.lean)
also rechecks old exact character criteria at widths 4, 8 and 16 against
the new rate, preserving the original group and central cardinality.
It makes no conversion claim at arbitrary widths or for the global class predicates.
The [finite-base reduction](SymmetricSubgroupAsymptotics/BinarySmallClassBaseReduction.lean)
reduces that base to bounds 2, 5 and 25 for transitive binary actions in
degrees 2, 4 and 8. Empty, singleton and intransitive actions are proved
internally through the original restriction kernel. The
[small base](SymmetricSubgroupAsymptotics/BinarySmallConjugacyClassBase.lean)
installs the degree-two and degree-four cases; the
[degree-eight table](SymmetricSubgroupAsymptotics/BinaryConjugacyClassTable8.lean)
uses exact original orders for eleven entries and sparse original-group
conjugacy covers for fifteen entries. Complete original-action coverage
then supplies the transitive degree-eight bound of 25.
The [binary quotient specialization](SymmetricSubgroupAsymptotics/TransitiveBinaryCocycleBound.lean)
constructs its generators internally and proves `card H¹ ≤ (card A)^A_k`
for the stated representation of every actual quotient of the original
transitive binary group.
The [sparse class-cover verifier](SymmetricSubgroupAsymptotics/FiniteConjugacyCover.lean)
requires complete original rows and one original-group conjugator per
row. Its [8T35 pilot](SymmetricSubgroupAsymptotics/BinaryConjugacyClass8T35.lean)
proves an upper bound of 25 for the literal original group's class count.
The selected producer `computations/python/export_lean_conjugacy_cover_selected.py`
accepts one explicit `--source` from its pinned eight-point allowlist;
`--write` emits only that source's ignored witness data,
and `--check` performs a read-only replay. Separate Lean checks of the
generated data and consumer establish each literal group bound. All fifteen
selected covers are installed in the degree-eight table; the separate
original-action coverage theorem and block induction establish the
universal binary envelope. The producer itself establishes no Lean theorem.
The [local Schreier adapter](SymmetricSubgroupAsymptotics/BinarySchreierPrunedAdapter.lean)
reuses complete original word certificates and stops every index-two child
when the actual source order is at most twice the cutoff.
The [three-source pilot](SymmetricSubgroupAsymptotics/BinarySchreierPrunedPilot16T1026.lean)
installs the original 16T1026 certificate and proves order bounds of 256
for its two original targets, 16T524 and 16T611. Its local registry therefore
stops at order 128. No catalogue order is used as a proof, and the pilot
does not claim a Sylow root or global coverage.
The [encoded upper-order certificate](SymmetricSubgroupAsymptotics/FiniteEncodedOrderBound.lean)
needs only an encoded identity and closure of its finite rows under the
original generators. It requires neither row injectivity nor parent words;
extraneous rows are allowed because its conclusion is only an upper bound.
The [encoded adapter](SymmetricSubgroupAsymptotics/BinarySchreierEncodedOrderStops.lean)
and [finite-slice assembly](SymmetricSubgroupAsymptotics/BinarySchreierPrunedAssembly.lean)
combine such bounds with the original sparse Schreier certificates.
The [coset-cover order certificate](SymmetricSubgroupAsymptotics/GeneratorCosetOrderBound.lean)
instead covers the generated source by `q` right cosets of any actual
ambient subgroup `K`, proving its order is at most `q * card K` from
right-generator transition defects. Normality, distinct representatives
and representative reachability are unnecessary. Its
[order-stop adapter](SymmetricSubgroupAsymptotics/BinarySchreierCosetOrderStops.lean)
allows compressed certificates to enter the same original-action registry;
the [selected 16T832 pilot](SymmetricSubgroupAsymptotics/BinarySchreierCosetPilot16T832.lean)
uses 16 representatives and five correlated flip columns to prove the
original source has order at most 512 and stop its index-two children at
256. It does not accept that source's own normal axes or prove a global
registry root.
For an original pair action, the
[correlated-flip specialization](SymmetricSubgroupAsymptotics/BinaryPairCosetOrderBound.lean)
proves `card U ≤ q * 2^finrank(C)` from pointwise transition defects in a
proposed flip subspace `C`. It requires no proof that every vector in `C`
occurs in the source, and preserves its actual linear correlations.
The [column certificate](SymmetricSubgroupAsymptotics/BinaryFlipCosetOrderBound.lean)
allows dependent columns and proves the bound `q * 2^d` from pointwise
transition identities. The selected producer
[`export_lean_pair_coset_order.py`](../computations/python/export_lean_pair_coset_order.py)
requires `--source b16_832`, bounds its search, retained inputs and output,
and supports `--write` and read-only exact replay with `--check`.
Its emitted Lean source requires a separate bounded compiler check.
Additional local pilots cover
[16T1025 and six targets](SymmetricSubgroupAsymptotics/BinarySchreierPrunedPilot16T1025.lean)
and [16T832 with its target 16T624](SymmetricSubgroupAsymptotics/BinarySchreierPrunedPilot16T832.lean).
They preserve the original conjugators and do not assert global coverage.
The selected producer
[`export_lean_schreier_order_stop.py`](../computations/python/export_lean_schreier_order_stop.py)
accepts the explicit sources 473, 485, 500, 510, 524, 590, 611, 624 and 633
with `--source b16_524 --write`, for example; `--check` verifies exact replay.
It uses at most 256 rows and four generator edges per row, with fixed
operation, time and output limits. The generated sources are ignored;
each requires its own bounded Lean check.
For the selected 832 sparse certificate,
[`extract_selected_schreier_record.py`](../computations/python/extract_selected_schreier_record.py)
extracts compact untrusted original-point hints into a private JSON file;
[`export_lean_selected_schreier.py`](../computations/python/export_lean_selected_schreier.py)
then emits the source and binding under one shared search budget.
Both require explicit source selection and support read-only exact replay.
The extractor bounds cumulative decompression separately from retained
buffers; the producer never reads the full normal-subgroup data stream.
The finite character criteria now supply original-source analytic envelopes.
Complete weighted-family installation of the character and transport branches
remains separate. The central
binary extension comparison is proved for every exact exterior image and
its nonnegative weights, and is instantiated for C4 powers. Complete
finite-menu coverage, the joint numerical transition estimates, labelled
decoration bounds and the binary-error recurrence remain separate obligations.

[DerivedGeneratorWords](SymmetricSubgroupAsymptotics/DerivedGeneratorWords.lean)
certifies derived membership using expressions in the original generators.
If every original generator square equals such an expression, the binary
evaluation kernel of their literal generated subgroup equals its derived
subgroup. The five degree-sixteen carrier masters have kernel-checked
pointwise permutation witnesses. Their
[all-normal applications](SymmetricSubgroupAsymptotics/BinaryCarrierDerivedMasters16.lean)
prove `a₂ <= m`, and hence `max m a₂ = m`, for every original normal axis
of each master. This conclusion requires no enumeration of those normals.
The other numerical row fields, simultaneous domination and physical
coverage remain separate requirements.

[PrimeNormalHeadCentralizer](SymmetricSubgroupAsymptotics/PrimeNormalHeadCentralizer.lean)
proves `p ^ d_G(N) <= |C_N(u)|` for any finite group, prime `p`, original
normal subgroup `N` and original element `u`. Its commutator-fibre injection
does not require an abelian subgroup or a homomorphism from commutators.
Consequently, one centralizer inside the original derived subgroup bounds
the maximum over every original derived normal.
[DerivedWordCentralizerCertificate](SymmetricSubgroupAsymptotics/DerivedWordCentralizerCertificate.lean)
supplies such a bound from a finite code covering the commuting rows of an
actual derived-word certificate. The
[quotient transport](SymmetricSubgroupAsymptotics/PrimeEvaluationKernelQuotients.lean)
preserves the evaluation-kernel containment, and the
[exact inflation bound](SymmetricSubgroupAsymptotics/BinaryDerivedInflationBound.lean)
then gives `tau <= rho` on the same actual group or quotient.

The five literal degree-sixteen masters have checked derived-group orders
`16, 16, 16, 64, 64` and centralizer bounds giving
`rho <= 3, 3, 3, 4, 3`, respectively. The
[combined axis bounds](SymmetricSubgroupAsymptotics/BinaryCarrierMasterRankBounds16.lean)
install `max(m, a₂) <= min(log₂|N|, r)` for every original normal axis,
with those respective values of `r`. The
[generic capacity theorem](SymmetricSubgroupAsymptotics/BinaryCarrierAxisCapacity.lean)
uses the actual order of `N`; it requires no recorded normal profile.
Sharper exceptional `m` bounds, the other row fields, simultaneous
domination and physical coverage remain separate requirements.

[FiniteQuotientDerivedIntersection](SymmetricSubgroupAsymptotics/FiniteQuotientDerivedIntersection.lean)
reduces the quotient-center preimage and derived-quotient order through the
same actual intersection `N ∩ G'`. The
[row identities](SymmetricSubgroupAsymptotics/BinaryCarrierIntersectionRows.lean)
retain the complete original normal subgroup and its order. The
[finite radical consumer](SymmetricSubgroupAsymptotics/PrimeRelativeRadicalFiniteCertificate.lean)
uses actual candidate membership, whole-group normality and generator tests.

[PrimeDerivedJointHead](SymmetricSubgroupAsymptotics/PrimeDerivedJointHead.lean)
bounds every original normal head above `G'` by the dimension of its actual
quotient image plus a joint commutator annihilator. Only the actual retained
restriction image is put in that annihilator; equality or extendibility of
all invariant derived characters is not assumed. The
[independent-family lemma](SymmetricSubgroupAsymptotics/LinearJointAnnihilatorCapacity.lean)
controls every quotient subspace at once from common-radical bounds. The
[kernel decoder](SymmetricSubgroupAsymptotics/PrimeLinearKernelCertificate.lean)
certifies such bounds on complete finite vector spaces.

The five literal degree-sixteen masters have uniform head theorems for
every original normal `N >= G'`:

| Original action | Bound on `d_G(N)` |
| --- | --- |
| [16T1082](SymmetricSubgroupAsymptotics/BinaryCarrierHeadAboveDerived16T1082.lean), [16T1083](SymmetricSubgroupAsymptotics/BinaryCarrierHeadAboveDerived16T1083.lean), [16T1084](SymmetricSubgroupAsymptotics/BinaryCarrierHeadAboveDerived16T1084.lean) | `max(3, log₂(card N / 16))` |
| [16T1547](SymmetricSubgroupAsymptotics/BinaryCarrierHeadAboveDerived16T1547.lean) | `max(3, log₂(card N / 64))` |
| [16T1332](SymmetricSubgroupAsymptotics/BinaryCarrierHeadAboveDerived16T1332.lean) | `max(4, log₂(card N / 64))` |

Each theorem also uses the actual quotient `N/G'`. Complete
[character coordinates](SymmetricSubgroupAsymptotics/PrimeRelativeCharacterCoordinates.lean)
come from word relations modulo the whole-original-group relative radical.
Actual commutator words bind these coordinates to the forms. The first
four actions use seven single-form and 21 pair certificates. For 1083 and
1084, one original generator has proved-zero evaluation; only the quotient
coordinates drop it, while all seven original conjugators remain.
For 1332 the complete actual family is identified with the
[star family](SymmetricSubgroupAsymptotics/StarAlternatingHead.lean);
[full-family separation](SymmetricSubgroupAsymptotics/StarAlternatingSeparation.lean)
proves independence of its original quotient coordinates. The
[star head theorem](SymmetricSubgroupAsymptotics/PrimeDerivedStarHead.lean)
then controls every quotient subspace without enumerating independent tuples.

[PrimeIntersectionRetainedHead](SymmetricSubgroupAsymptotics/PrimeIntersectionRetainedHead.lean)
handles the exact intersection `B = N ∩ G'`: its actual quotient directions
are central and, under the proved evaluation-kernel condition, have prime
exponent. The retained restriction image annihilates both original powers
and mixed commutators. This gives a head bound from their combined finite
test kernel; it does not identify that kernel with the extendible characters.
The exact crossing results below resolve these retained-head tests for the
four pair-family masters. Coverage of all other normal branches, simultaneous
row domination, and physical weighted coverage still require their own proofs.

The [exact order module](SymmetricSubgroupAsymptotics/BinaryCarrierExactOrders16.lean)
derives `|G| = 2^10, 2^10, 2^10, 2^11, 2^12` for the masters
1082, 1083, 1084, 1332, 1547, respectively, from their proved quotient
coordinate equivalences and actual derived orders. Their 2-group property
is a consequence of these equalities.
[Original normal-interval characters](SymmetricSubgroupAsymptotics/PrimeNormalIntervalCharacters.lean)
supply a nonzero invariant derived character vanishing on every proper
original normal `B < G'`. The
[intersection form constraints](SymmetricSubgroupAsymptotics/PrimeDerivedIntersectionForms.lean)
and [proper-intersection reduction](SymmetricSubgroupAsymptotics/PrimeDerivedProperIntersection.lean)
put the actual image of `N` in its form radical. The
[star parameter capacity](SymmetricSubgroupAsymptotics/StarAlternatingParameterCapacity.lean)
retains the entire vanishing-character subspace in the 1332 case.

Consequently the [five-master intersection theorem](SymmetricSubgroupAsymptotics/BinaryCarrierProperIntersection16.lean)
proves, for every original normal `N` not containing `G'`,
`|N| <= 4 |N ∩ G'|` for 1082, 1083, 1084, 1547, and
`|N| <= 8 |N ∩ G'|` for 1332. The exact
[image-order identity](SymmetricSubgroupAsymptotics/PrimeDerivedIntersectionImage.lean)
identifies these as bounds on the original quotient directions. For every
master, `N ∩ G' <= R` implies `N <= R`, where `R = (G')²[G',G]`
is the actual relative radical. These direction and containment bounds
do not replace the remaining correlated head, radical, and quotient-row
inequalities.

The [character detection theorem](SymmetricSubgroupAsymptotics/PrimeRelativeCharacterDetection.lean)
identifies the common kernel of the complete invariant characters vanishing
on `B` as `B R`; it identifies `B` itself only with an explicit `R <= B` proof.
[Full vanishing-space center detection](SymmetricSubgroupAsymptotics/PrimeDerivedVanishingCenter.lean)
then identifies the actual center preimage modulo `G'` with the common radical
of that entire space, retaining every original conjugation constraint.

The [saturation certificate](SymmetricSubgroupAsymptotics/NormalSubgroupSaturationCertificate.lean)
uses nonempty iterated original commutator words to prove, for every original
normal `M <= G'`, either `M <= R` or `R <= [M,G]`. Selected certificates
prove this for all five masters from at most 64 derived rows, without
constructing the full group or enumerating its normals. The
[bounded exporter](../computations/python/export_lean_carrier_saturation.py)
only emits these certificates; the Lean proofs establish their consequences.
[Exact radical and maximum-head transport](SymmetricSubgroupAsymptotics/NormalSubgroupSaturationHeadBounds.lean)
shows, for `B <= G'` outside `R`, that its maximum over **all** original normals
is `max(m(R), head(B))`.

For the four pair-family masters, the
[exact crossing theorem](SymmetricSubgroupAsymptotics/BinaryCarrierCrossing16.lean)
proves `[N,G] = N ∩ G' = R_N` for every crossing normal, so its head is the
actual image dimension `w`. The
[intersection capacity theorem](SymmetricSubgroupAsymptotics/BinaryCarrierCrossingCapacity16.lean)
proves `m = a₂ = 2`. The
[literal history-row bridge](SymmetricSubgroupAsymptotics/BinaryCarrierCrossingRows16.lean)
then gives the two exact possibilities for `(k,n,m,a₂,c,g)`:

| Original masters | `w = 1` | `w = 2` |
| --- | --- | --- |
| 1082, 1083, 1084 | `(1,4,2,2,2,1)` | `(2,5,2,2,1,1)` |
| 1547 | `(1,6,2,2,2,1)` | `(2,7,2,2,1,1)` |

All six coordinates belong to the same literal normal axis. This covers
crossing normals only and preserves distinct normals with identical rows;
it neither asserts realization of every row nor supplies their total weights.

For the star-family master, the
[full mixed-vanishing identity](SymmetricSubgroupAsymptotics/PrimeDerivedMixedVanishing.lean)
is `L_[N,G] = J_W`; it makes no extendibility assumption and does not identify
`[N,G]` with `N ∩ G'`. The
[generic crossing theorem](SymmetricSubgroupAsymptotics/PrimeDerivedStarCrossing.lean)
retains all original powers in the relative radical and proves
`k + dim(L_B) <= dim(U)`, together with exact center and derived orders.
Its [original 1332 application](SymmetricSubgroupAsymptotics/BinaryCarrierStarCrossing16T1332.lean)
keeps `ell = dim(L_B)` and `w = dim(NG'/G')` from the same normal:
`ell,w >= 1`, `ell+w <= 4`, `k <= 4-ell`,
`m <= max(2,4-ell)`, `c = 4-w`, and `g = ell`.

The [small-radical profiles for 1547](SymmetricSubgroupAsymptotics/BinaryCarrierRadicalProfiles16T1547.lean)
cover every original normal `M <= R`, using the exact central subgroup `Z`
of order two and `R_R = [R,G] = Z`. Their exact rows are
`(0,0,0,0,1,6)`, `(1,1,1,0,2,5)`, `(1,2,1,1,1,4)`,
and `(2,3,2,1,3,3)`. The order-four alternative covers all such original
normal planes through one theorem; it assumes no list or count of planes.
The [center preimage theorem](SymmetricSubgroupAsymptotics/BinaryCarrierRadicalCenter16T1547.lean)
retains the same subgroup in both quotient-order calculations.

The [star row bridge](SymmetricSubgroupAsymptotics/BinaryCarrierStarCrossingRows16T1332.lean)
keeps the exact order `n = 6-ell+w`, bounds all six fields together, and
places every star crossing row below `(3,8,3,3,3,3)`. The
[common-envelope certificate](SymmetricSubgroupAsymptotics/BinaryCarrierStarEnvelope.lean)
proves both mark bounds, its self comparison, and every comparison with the
41 displayed H16/X/J/P numerical rows in the sixth cone colour. It checks
all degree-eight columns as well. This scalar certificate does not assert
that arbitrary actual normals belong to the displayed menu.
The [1547 small-radical row bridge](SymmetricSubgroupAsymptotics/BinaryCarrierRadicalRows16T1547.lean)
likewise transports the four universal profiles into literal carrier histories.

The remaining normal branches now have uniform original-action proofs.
[NormalOrderTwo](SymmetricSubgroupAsymptotics/NormalOrderTwo.lean) and
[PrimeDerivedOrderTwoProfiles](SymmetricSubgroupAsymptotics/PrimeDerivedOrderTwoProfiles.lean)
give both small-radical rows for the first three masters. The four-row
[1332 radical structure](SymmetricSubgroupAsymptotics/BinaryCarrierRadicalStructure16T1332.lean)
and its [exact profiles](SymmetricSubgroupAsymptotics/BinaryCarrierRadicalProfiles16T1332.lean)
prove that every original normal inside its radical is trivial, the central
order-two subgroup, or the radical itself; its normal-head maximum is one.

For `R < N < G'`, the
[pair-family theorem](SymmetricSubgroupAsymptotics/PrimeDerivedPairIntermediate.lean)
and [full-star theorem](SymmetricSubgroupAsymptotics/PrimeDerivedStarIntermediate.lean)
retain the entire vanishing-character space. They prove exact radical,
maximum-head, order and quotient fields. The star argument works for arbitrary
horizontal dimension and explicitly excludes the zero-parameter endpoint.
The [above-derived transport](SymmetricSubgroupAsymptotics/BinaryCarrierAboveDerivedRows16.lean)
gives the simultaneous bound `(max(e,w), d+w, e, e, s-w, 0)` for all five
original carriers, with exact order and quotient slopes.

[Pair-family coverage](SymmetricSubgroupAsymptotics/BinaryCarrierPairNormalRows16.lean)
and [star-family coverage](SymmetricSubgroupAsymptotics/BinaryCarrierStarNormalRows16T1332.lean)
combine these results with the crossing branches. They cover **every original
normal axis** of the five degree-sixteen masters, without enumerating normals
or assuming a complete normal-subgroup catalogue. Distinct normals remain
distinct inputs; possible invariant rows are not a count of normals.

The [effective-envelope theorem](SymmetricSubgroupAsymptotics/JointCapacityEffectiveEnvelope.lean)
compares the whole coupled polygon using `min(n,k+m)`. It preserves the literal
subgroup order in all group identities, and its cost comparison allows a
negative first mark. The
[scalar master comparisons](SymmetricSubgroupAsymptotics/BinaryCarrierMasterEnvelopes.lean)
reuse the displayed H16 rows for the resulting branches. The
[all-five envelope bridge](SymmetricSubgroupAsymptotics/BinaryCarrierMasterEnvelopeCoverage16.lean)
assigns every original normal axis one of twelve H16 envelopes or two star
envelopes; both star envelopes have sixth-colour cross-column certificates.
The [weighted-history adapter](SymmetricSubgroupAsymptotics/BinaryCarrierWordEffectiveEnvelope.lean)
transfers proved envelope inequalities without merging axes or changing weights.
The [complete displayed pair table](SymmetricSubgroupAsymptotics/BinaryCarrierDisplayedPairs.lean)
proves all 1,681 ordered comparisons and both marks with the original scales.
Its small proof modules use the reusable
[polygon budget](SymmetricSubgroupAsymptotics/JointCapacityPolygonBudget.lean).
The [fourteen-envelope energy certificate](SymmetricSubgroupAsymptotics/BinaryCarrierMasterMenuEnergy.lean)
includes both extra star envelopes and their mutual comparison.

[Master-word history bounds](SymmetricSubgroupAsymptotics/BinaryCarrierMasterWords16.lean)
now install this certificate on every ordered word of the five literal
degree-sixteen groups, with arbitrary repetitions and survival conditions.
Each original position contributes mass eight. For `T = 2 * word.length`,
the quadratic exponent is `(R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2`.
The theorem retains the explicit polynomial loss and the original
`axisWeightProduct`; it does not substitute a count of envelope labels.
[Unit weights](SymmetricSubgroupAsymptotics/BinaryCarrierUnitWeights.lean)
identify that product with the number of actual normal histories and bound it
from the original group orders. The
[degree-sixteen terminal theorem](SymmetricSubgroupAsymptotics/BinaryCarrierMasterTerminal16.lean)
then proves a concrete fixed-word counting bound with exactly one critical
terminal attachment, arbitrary terminal survival tests, and a proved internal
normal multiplicity of at most `2^(4096 * word.length)`. It takes no weight-bound
hypothesis. Original labelled-action normalizers and profile factors remain
outside this fixed-word count.
The [exact tail decomposition](SymmetricSubgroupAsymptotics/SubgroupTailFibre.lean)
and its [critical terminal specialization](SymmetricSubgroupAsymptotics/BinaryCarrierTerminalFamily.lean)
identify those fibres with literal original subgroups, preserving arbitrary
predicates and requiring fullness only on each specified coordinate. The
[fixed-product theorem](SymmetricSubgroupAsymptotics/BinaryCarrierMasterProduct16.lean)
therefore states the reserve directly for actual subgroup cardinalities.

[Upper profile assembly](SymmetricSubgroupAsymptotics/OrbitProfileUpperAssembly.lean)
retains the original normalizer orders and occurrence factorials using only
naturality of the local subgroup family. Each labeling fibre contains a free
copy of the original internal-symmetry group, so an upper bound does not need
transitivity, separation of action types, or uniqueness of presentations.
The [real-weight consumer](SymmetricSubgroupAsymptotics/OrbitProfileUpperWeights.lean)
inserts a proved model count under exactly that original profile weight.

The [literal occurrence chart](SymmetricSubgroupAsymptotics/BinaryCarrierOccurrenceWord.lean)
identifies an explicitly enumerated product with its original repeated
occurrences. [Critical/carrier regrouping](SymmetricSubgroupAsymptotics/BinaryCarrierCriticalOccurrence.lean)
preserves the original regular C2 and V4 block conditions, every nonabelian
critical projection, and arbitrary predicates on the reconstructed subgroup.
The [sum-profile chart](SymmetricSubgroupAsymptotics/OrbitProfileProductSum.lean)
splits the two classes of original occurrences with the same exactness.
The [mixed degree-sixteen model count](SymmetricSubgroupAsymptotics/BinaryCarrierMixedProfile16.lean)
combines these charts for the literal critical and five-master actions,
retaining every individual full projection and arbitrary original predicates.
Its [labelled count](SymmetricSubgroupAsymptotics/BinaryCarrierLabelledProfile16.lean)
has physical degree `2*R+16*L` and the original action normalizers and
occurrence factorials. Arbitrary survival families are bounded by inclusion
in the full family; the theorem does not assume their invariance.
The [generic mixed-profile theorem](SymmetricSubgroupAsymptotics/BinaryCarrierMixedProfile.lean)
provides the same transport for any finite menu of original binary actions,
given a history certificate and order bound on its exact occurrence word.
The [general product reserve](SymmetricSubgroupAsymptotics/BinaryCarrierWordProductEnergy.lean)
also supports words with different physical scales. It discharges internal
normal multiplicity from the original group orders and counts actual product
subgroups with one terminal attachment.

The [full numerical menu](SymmetricSubgroupAsymptotics/BinaryCarrierFullMenu.lean)
and its [energy certificate](SymmetricSubgroupAsymptotics/BinaryCarrierFullMenuEnergy.lean)
preserve scales one and two across all 43 envelopes. The
[mixed-scale history theorem](SymmetricSubgroupAsymptotics/BinaryCarrierFullMenuHistory.lean)
installs their bounds from actual row coverage and the exact sum of original
physical scales. Repeated labels retain separate original normal choices and
weights; the numerical menu does not count normals.
The [original mixed-word certificate](SymmetricSubgroupAsymptotics/BinaryCarrierMixedMenuWord.lean)
supplies those inputs for arbitrary words in X, J, P and the five degree-sixteen
masters. Its [weighted and subgroup reserves](SymmetricSubgroupAsymptotics/BinaryCarrierMixedMenuReserve.lean)
use the structural total scale of the original word, including repetitions.
The [literal mixed actions](SymmetricSubgroupAsymptotics/BinaryCarrierMixedActions.lean)
identify that scale with the original physical degree `2*R+8*T` and install
the reserve in the original-normalizer labelled bound, without a supplied
counting or numerical-certificate hypothesis.
Their [original order bound](SymmetricSubgroupAsymptotics/BinaryCarrierMixedOrder.lean)
gives `2^(6*T + numberOfP)` for the complete master product and each actual
subgroup, hence the uniform `2^(7*T)` bound. A P occurrence has physical
scale one and order 128; words containing no P recover `2^(6*T)`.
The [coordinate epimorphism pullback](SymmetricSubgroupAsymptotics/CarrierEpimorphismPullback.lean)
preserves the complete exterior image and reconstructs the original subgroup.
It gives a family injection and retains any original profile scalar while
requiring fullness only on the individual carrier coordinates. The
[concrete degree-eight routes](SymmetricSubgroupAsymptotics/BinaryCarrierRoutes8.lean)
prove all four required epimorphisms from the literal original generators:
J to 8T28, and P to 8T18, 8T29 and 8T31. Together with the identity routes,
the [original-action theorem](SymmetricSubgroupAsymptotics/BinaryCarrierOriginalActions.lean)
counts all seven degree-eight and five degree-sixteen carrier colours.
Its [generic profile pullback](SymmetricSubgroupAsymptotics/BinaryCarrierMixedProfileEpimorphism.lean)
reconstructs each original subgroup and preserves arbitrary survival tests.
The physical degree is `2*R+8*T`; original target normalizers and occurrence
factorials remain distinct even when targets share a source master.
The [binary-mixture numerical inequalities](SymmetricSubgroupAsymptotics/BinaryMixtureNumerics.lean)
also prove the manuscript's carrier linear deficit and small-carrier Hall
deficit. The [C4 terminal comparison](SymmetricSubgroupAsymptotics/BinaryCarrierCyclicFourProductEnergy.lean)
applies the reserve directly at rank `R+2a`, preserving all individual
nonabelian critical and carrier fullness conditions. Its comparison family
allows every binary abelian image, so no support split is needed.

The [exterior-preserving comparison](SymmetricSubgroupAsymptotics/BinaryPGroupExteriorComparison.lean)
replaces a finite group of order `2^u` by its elementary abelian comparison
while preserving arbitrary predicates on the exact exterior image; the
exterior may be nonabelian. The original C4
[square obstruction](SymmetricSubgroupAsymptotics/BinaryCyclicFourSquareObstruction.lean),
[exact two-column count](SymmetricSubgroupAsymptotics/BinaryCyclicFourCount.lean),
and [Gaussian estimate](SymmetricSubgroupAsymptotics/BinaryCyclicFourCountNumerics.lean)
give the [mixed subgroup bound](SymmetricSubgroupAsymptotics/BinaryCyclicFourMixedHall.lean)
with explicit factor `(a+1)*(R+u+a+1)/eulerProduct^2` and exponent
`(a^2+(R+u+a)^2)/4`. It counts all original product subgroups and bounds
arbitrary survival subfamilies by inclusion. No general Hall-partition
formula or arbitrary-group subgroup-count estimate is an input.
The [abelian quotient-graph classification](SymmetricSubgroupAsymptotics/AbelianProductGraphClassification.lean)
also gives the exact double Hom sum for arbitrary finite abelian first
factor and arbitrary finite second factor. The
[sectional character bound](SymmetricSubgroupAsymptotics/PrimeSectionalCharacterRank.lean)
and its [terminal application](SymmetricSubgroupAsymptotics/BinaryTerminalSectionalRank.lean)
prove `tau(H) <= a+u` for every actual `H <= C4^a × B`, including proper
subdirect tails. The [Gaussian product identity](SymmetricSubgroupAsymptotics/TerminalGaussianProductIdentity.lean)
sums every such literal tail exactly. The
[critical-family Hall theorem](SymmetricSubgroupAsymptotics/BinaryCriticalCyclicFourHall.lean)
therefore counts the original critical product attached once to this tail,
with arbitrary original survival tests and only individual nonabelian
critical projections required to be full. Its explicit exponent is
`(a+u+7)^2/3 + (a^2+(R+u+a)^2)/4`; its prefactor is
`2*(R+1)*(c+1)*(a+1)*(R+u+a+1)/eulerProduct^5`, where `c` is the number
of nonabelian critical factors. The complete finite-alphabet summation
below absorbs the analytic and profile errors. Exhaustive global ownership
remains separate; these local results do not prove T1.

The [thirteen-colour Hall consumer](SymmetricSubgroupAsymptotics/BinaryCarrierOriginalCyclicFourHall.lean)
installs this estimate on the actual regular C4 translation action and all
twelve original carriers. The source order satisfies `u <= 6*T + numberOfP
<= 7*T`; the physical degree is `2*R+4*a+8*T`, and the denominator still
contains the original target normalizers and occurrence factorials.

The [full-block rank construction](SymmetricSubgroupAsymptotics/PermutationFullBlockRankGap.lean)
and [concrete noncritical actions](SymmetricSubgroupAsymptotics/BinaryNoncriticalActionRankGap.lean)
derive a strict gap for a correlated original subgroup from one actual full
noncritical block. The [faithful permutation transgression bound](SymmetricSubgroupAsymptotics/BinaryTerminalPermutationRank.lean)
also bounds the retained annihilator dimension by half the original degree.
Their [thirteen-colour adapter](SymmetricSubgroupAsymptotics/BinaryCarrierOriginalCyclicFourRankGap.lean)
supplies both marks for the same original tail, using the actual C4
translation model of the Hall consumer.

The [original small-support count](SymmetricSubgroupAsymptotics/BinaryCarrierOriginalSmallSupport.lean)
partitions each original subgroup by its unique full noncritical tail and
applies the [single-tail attachment estimate](SymmetricSubgroupAsymptotics/BinaryTerminalFullTailCount.lean).
Only the number of tails uses master preimages: the
[binary-group count](SymmetricSubgroupAsymptotics/BinaryPGroupSubgroupCount.lean)
proves that a source of order `2^q` and every onto image have at most `G_q`
subgroups. The [Gaussian comparison](SymmetricSubgroupAsymptotics/TerminalGaussianComparison.lean)
retains the original rank gap, giving the
[normalized model estimate](SymmetricSubgroupAsymptotics/BinaryCarrierSmallSupportNormalized.lean)
with prefactor `4*(N+1)^4/eulerProduct^6` and exponent
`-N/2+1/2+(211/192)*C^2+(14/3)*C+49/3`, where `N=R+C` and `C=2*a+4*T`.
The [uniform scalar estimates](SymmetricSubgroupAsymptotics/BinaryMixtureAbsorption.lean)
absorb the full critical coefficient shift and fixed logarithmic costs in
all three mixture regimes. The
[complete small-support union](SymmetricSubgroupAsymptotics/BinaryCarrierAllSmallSupport.lean)
now sums every positive support `C ≤ sqrt(N)/4` in the original thirteen-colour
alphabet and proves that its actual labelled subgroup count, divided by
`exactBenchmark (2*N)`, is eventually at most `2^(-N/4)`.
The [profile sum](SymmetricSubgroupAsymptotics/BinaryCarrierSmallSupportProfiles.lean)
retains the entire coefficient shift and every original normalizer/factorial
weight; the [physical assembly](SymmetricSubgroupAsymptotics/BinaryCarrierSmallSupportPhysical.lean)
uses a forgetful surjection, so overlapping presentations cause no difficulty.
The [complete finite-alphabet mixture](SymmetricSubgroupAsymptotics/BinaryCarrierMixtureCompletion.lean)
also installs the Hall and carrier-reserve branches on the same original
physical parameter bins. Their rates are respectively `1/50` and
`29/1490432` in half-degree `N`. Summing every bin and absorbing its
polynomial cost gives the unconditional bound
`card(Family N) / exactBenchmark(2*N) ≤ 2^(-(29/2980864)*N)` eventually.
This theorem has no count, weight or numerical estimate as a premise.
Its family is the literal union of all positive-support profiles in the
specified thirteen-colour alphabet on `Fin (2*N)`; global binary coverage,
remaining odd actions, nonbinary ownership and the full remainder recurrence are
separate obligations.

The [singleton extension theorem](SymmetricSubgroupAsymptotics/BinaryCarrierOddSingleton.lean)
transfers this complete finite-alphabet bound to degree `2*N+1`, with the
same rate, for every original complement chart. The
[relabel equivalence](SymmetricSubgroupAsymptotics/BinaryCarrierMixtureRelabel.lean)
proves the required closure of the actual even family; the
[chart comparison](SymmetricSubgroupAsymptotics/SingletonExtensionCharts.lean)
then forgets all chart witnesses without an extra factorial.
The physical factor `2*N+1` is absorbed exactly by the
[odd benchmark inequality](SymmetricSubgroupAsymptotics/SingletonBenchmark.lean).
This covers the singleton sector, not every odd-degree subgroup.

The [complete S3 sector](SymmetricSubgroupAsymptotics/BinaryCarrierS3Completion.lean)
proves the same rate `29/2980864` for every positive-support profile in
the original thirteen-colour alphabet with one natural S3 orbit.
The [exact model equivalence](SymmetricSubgroupAsymptotics/BinaryCarrierS3Model.lean)
proves that the original exterior is a binary group, forces the marker's
A3 kernel, and adds one C2 occurrence while retaining every original
carrier coordinate and its individual fullness condition.
The [weight identity](SymmetricSubgroupAsymptotics/BinaryCarrierS3Weights.lean)
retains the original divisor six and the occurrence factorial:
`weight(p)/6 = ((p.c2+1)/3)*weight(p.addC2)`.
The shifted half-degree is `N=R+2*a+4*T+1`.
The [complete weighted mixture](SymmetricSubgroupAsymptotics/BinaryCarrierWeightedMixture.lean)
supplies the bound on the original profile sum directly, and the
[physical union](SymmetricSubgroupAsymptotics/BinaryCarrierS3Union.lean)
absorbs the linear weight correction and quadratic number of bins.
The [union of both odd sectors](SymmetricSubgroupAsymptotics/BinaryCarrierOddMixtureCompletion.lean)
is a literal family of subgroups of `Perm (Fin (2*N+1))`.
Its normalized count is eventually at most `2*2^(-(29/2980864)*N)`,
hence at most `2^(-(29/5961728)*N)`.
These theorems have no counting estimate as a premise. Their finite
alphabet and single-marker scope do not supply global odd-action coverage.

For the degree-eight J carrier, the selected
[states](SymmetricSubgroupAsymptotics/GeneratedCarrierNormal8T27/States.lean) and
[registry](SymmetricSubgroupAsymptotics/GeneratedCarrierNormal8T27/Registry.lean)
certify all thirteen literal normal subgroups and exhaustive coverage.
Their [complete six-field profiles](SymmetricSubgroupAsymptotics/BinaryCarrierNormalProfiles8T27.lean)
are now proved from actual radical words, second radicals, normal containments,
and quotient center/derived certificates. Every field uses the same original
normal; equal numerical rows do not merge subgroup identities. In particular,
the whole-group profile retains second head 2 and maximum derived head 1.
The [original J row bridge](SymmetricSubgroupAsymptotics/BinaryCarrierNormalRows8T27.lean)
places all thirteen normals in the displayed table at scale one, keeping the
same original subgroup across all fields.
The [X evaluation-kernel theorem](SymmetricSubgroupAsymptotics/BinaryCarrierEvaluationKernel8T26.lean)
also proves that the actual binary evaluation kernel equals the commutator.
The selected [X registry](SymmetricSubgroupAsymptotics/GeneratedCarrierNormal8T26/Registry.lean)
certifies all 27 original normal subgroups with exhaustive coverage.
Their [six-field profiles](SymmetricSubgroupAsymptotics/BinaryCarrierNormalProfiles8T26.lean)
and [exact row bridge](SymmetricSubgroupAsymptotics/BinaryCarrierNormalRows8T26.lean)
retain one original normal index across radicals, second radicals, maximum
heads, orders and quotient invariants. All 27 normals match the nine displayed
X rows at scale one; equal rows retain their separate original normals.
The selected [P registry](SymmetricSubgroupAsymptotics/GeneratedCarrierNormal8T35/Registry.lean),
[six-field profiles](SymmetricSubgroupAsymptotics/BinaryCarrierNormalProfiles8T35.lean),
and [exact row bridge](SymmetricSubgroupAsymptotics/BinaryCarrierNormalRows8T35.lean)
do the same for all 28 original P normals and all ten displayed scale-one
P rows. All three degree-eight masters now feed the mixed history theorem
alongside the five degree-sixteen masters, and their quotient routes are
installed in the original profiles. The finite-alphabet normalized sum is
proved above; exhaustive physical source coverage and the complete remainder
recurrence remain separate.

The [finite factorial profile bound](SymmetricSubgroupAsymptotics/FiniteFactorialProfiles.lean)
retains every original denominator and bounds any finite profile sum by
`exp(sum_i (1/w_i))`, hence by `exp(numberOfColours)` when all denominators
are at least one. Exact noncritical normalizer orders are unnecessary for
this upper bound; the critical coefficient ratios remain separate.
The [original profile-weight adapter](SymmetricSubgroupAsymptotics/BinaryCarrierProfileWeights.lean)
factors the literal mixed denominator into the exact critical weight and
those original carrier factors. It bounds the complete finite carrier sum,
and then all critical profiles of a fixed rank, by
`criticalCoefficient R * exp(numberOfColours)` without merging colours.
The [local rank-gap theorem](SymmetricSubgroupAsymptotics/PermutationCharacterRankGap.lean)
preserves a proved gap on an invariant original block through its faithful
complement. The [master rank-gap theorem](SymmetricSubgroupAsymptotics/BinaryCarrierMixedRankGap.lean)
supplies the gap for all eight literal masters and their actual onto images,
using the already checked normal rows at the original physical scales.

The abstract recurrence results retain their kernel and counting hypotheses;
they do not establish a subgroup asymptotic without those estimates.
The primitive endgame now separates the finite nonaffine catalogue match from
the affine remainder: the checked 116-row receipt is used only after a literal
semisimple outer-log profile exists, while the complementary primitive and
minimal-block cases must construct an already integrated source.  This prevents
the project-owned affine action exhaustion from being hidden inside the
published primitive-catalogue input.
The [verification boundary](../ASSUMPTIONS.md#formal-theorem-boundary)
distinguishes conditional assembly, proofs relative to named published inputs,
and closed theorems. T1 remains unproved in Lean. The unconditional subgroup
asymptotics T2 and T3 therefore remain open, while both implications from T1
and both independent analytic benchmark estimates are proved.

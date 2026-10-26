# Lean formalization

The local project pins Lean **4.30.0** and mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Its package dependency graph is
recorded in `lake-manifest.json`. The checking scripts require Python 3.11+
and a POSIX environment with `fcntl`, process groups, and `ps`.
With elan installed, obtain mathlib's
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

For a fresh checkout, the serial closure wrapper discovers the local import
graph and checks dependencies before their consumers. From the repository root:

```sh
python3 -B scripts/check_lean_closure.py --log-dir ../lean-check-logs --plan
python3 -B scripts/check_lean_closure.py --log-dir ../lean-check-logs --resume
```

The first command only prints the plan. The second checks the public root,
reusing only matching successful receipts from that log directory. It preserves
previous receipts and logs before reruns and stops on a failed check. Each
compiler invocation uses `check_lean.py`, with 16 GiB limits and a one-hour
wall timeout. To select only the final theorem's dependencies, add
`--root SymmetricSubgroupAsymptotics.MarkedC4PublishedSevenTargets`.
The public root imports that proof facade and the specification's equivalent
shared-threshold statements. Optional regression fixtures and alternative
certificates can be selected through their own `--root` module names.
This workflow checks source/object correspondence; the mathematical input
boundary and exported declarations' axiom audits remain separate obligations.

The runner requires existing import objects and validates available local
check receipts. It records legacy imports without receipts as unverified;
it does not recursively certify all installed dependency objects.
It permits one compiler at a time and one Lean thread, with defaults of
16 GiB allocator memory and a sampled 16 GiB process-group RSS watchdog.
Selected modules may use up to `--memory-mb 16384 --rss-limit-mb 16384`,
allowing 16 GiB for both limits. Larger limits
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
The closure wrapper's import-order, resume, and failure-preservation tests run
with `python3 -B scripts/test_check_lean_closure.py`, also without Lean.

A successful source check does not by itself establish a standard-axioms-only
proof. Legacy finite certificates may use `native_decide`; their generated
native-computation axioms must be distinguished from `propext`,
`Classical.choice`, and `Quot.sound` in the exported theorem's axiom audit.
Use kernel-checked finite certificates (`decide +kernel`) and recheck affected
consumers before claiming that stronger boundary. A theorem whose type names
an entire catalogue can inherit dependencies from its other entries; audit
literal-row exports and catalogue-facing exports separately.

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

## Folder structure

| Path | Contents |
|---|---|
| `SymmetricSubgroupAsymptotics/` | Definitions, analytic estimates, group-theoretic proofs, finite certificates, and theorem assemblers. |
| `SymmetricSubgroupAsymptotics/External/` | Selected proof ports, concrete classification models, and mathlib backports, with preserved notices and pinned provenance. |
| `SymmetricSubgroupAsymptotics/External/CFSG/` | Concrete CFSG models and exhaustiveness proposition, frozen at the source revision recorded in `../provenance/CFSG_SOURCE.md`. The proposition alone supplies no generation, order or automorphism theorem. |
| `SymmetricSubgroupAsymptotics/CFSGSharedInfrastructure.lean` | Optional import for concrete classification transport, alternating-family bounds, literal type-A and Suzuki generation/Sylow witnesses, integral Serre lemmas, soluble-generation lifting, and bounded binary counting. |
| `SymmetricSubgroupAsymptotics.lean` | Public import of the final proof facade and shared-threshold formulations. Optional certificate modules have their own imports. |
| `SymmetricSubgroupAsymptotics/CFSGTypeAModelGeneration.lean` | Proved two-generation for the entire literal matrix type-A family; all other residual model obligations remain explicit. |
| `SymmetricSubgroupAsymptotics/CFSGSuzukiModelGeneration.lean` | Actual Suzuki generating pair and exact classifier dispatch, with the original positive-parameter guard. |
| `SymmetricSubgroupAsymptotics/CFSGSuzukiModelGoodSylow.lean` | Actual Suzuki Sylow witness, soluble normalizer and opposite-subgroup generation; the original matrices supply every structural premise. |
| `SymmetricSubgroupAsymptotics/CFSGSuzukiModelCardinality.lean` | Exact Suzuki order from a proved, disjoint two-cell decomposition with unique coordinates. |
| `SymmetricSubgroupAsymptotics/CFSGSuzukiOuterBound.lean` | Actual outer group has order at most `2*m+1`; combined with original central-root orbits, this proves both required least-index bounds. |
| `SymmetricSubgroupAsymptotics/CFSGPSLTwoSimpleIndexReduction.lean` | Both actual least-index inequalities for every original rank-one type-A model, including field orders four and five uniformly. The outer bound retains the square-scalar normalizer and cancels the actual inner torus. |
| `SymmetricSubgroupAsymptotics/CFSGTypeASimpleIndexReduction.lean` | Both required simple-index inequalities for the entire original type-A family. Higher rank uses actual root geometry, PGL frame alignment, and an injective frame-stabilizer map to field automorphisms. The literal type-A branch is removed from the remaining-model predicate. |
| `SymmetricSubgroupAsymptotics/CFSGTypeALeastIndexSquare.lean` | Actual higher-rank type-A squared-index bound, from a projective point stabilizer and the full linear-group product formula. `CFSGTypeAMinimumIndexLower` proves `q^r <= ell`; the final type-A assembler discharges the outer premise of its numerical adapter. |
| `SymmetricSubgroupAsymptotics/CFSGProjectiveLinearCardComparison.lean` | The actual scalar quotient `PGL_n(F)` has cardinality at most `n` times that of `PSL_n(F)`, using the polynomial-root bound on the actual special-linear centre. |
| `SymmetricSubgroupAsymptotics/CFSGTypeARootPermutation.lean` | Actual SL/PSL transvections are intrinsically recognized using Sylow centres. Product geometry and exact parameter counts prove every automorphism sends full point-root or hyperplane-root groups to groups of those same two kinds. No arbitrary PSL-automorphism lift is assumed. |
| `SymmetricSubgroupAsymptotics/CFSGColorOrientationIndex.lean` | A literal action on a connected bipartite geometry has a subgroup preserving the two sides with index at most two. The generic incidence and compatible-action faithfulness modules supply the orientation factor in the complete type-A automorphism count. |
| `SymmetricSubgroupAsymptotics/CFSGSerreDividedPowers.lean` | Binomial multiplication on the literal integral Serre lattice, preserved by base change. Uniform finite-type nilpotence remains open. |
| `SymmetricSubgroupAsymptotics/CFSGSerreRootOperatorInvertible.lean` | Every original root operator has an actual invertible lift, proved through pointwise divided-power nilpotence in every characteristic. This supplies neither additive root parameters nor cross-root relations. |
| `SymmetricSubgroupAsymptotics/CFSGSerreOrdinaryTwistModels.lean` | Original diagram/Frobenius graph identifications for twisted A, D, E6 and triality, built on the same integral lattice and its scalar extension. Exceptional long-short isogenies are separate. |
| `SymmetricSubgroupAsymptotics/CFSGSerreRepresentationDescent.lean` | Actual invariant-kernel descent of the generated group action, retaining every original root polynomial. A simple projective source maps isomorphically to its nontrivial projective image; identifying that image with a classical group remains separate. |
| `SymmetricSubgroupAsymptotics/CFSGSerreGeneratorRepresentation.lean` | The six literal Serre generator identities imply an actual rational quotient representation; each concrete matrix realization must still prove those identities. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticImageCentralizer.lean` | The actual symplectic matrices satisfy all six rational Serre identities and preserve the original integral lattice. Every original root polynomial acts by matrix conjugation on its actual base-change image, whose commutant is scalar. The later full-group theorem proves the natural identification. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticProjectiveRealization.lean` | Equality of the original source and literal elementary matrix action ranges yields an isomorphism of their actual central quotients whenever the original projective source is simple. The target is the subgroup generated by the displayed matrices; no full symplectic-group generation theorem is assumed. |
| `SymmetricSubgroupAsymptotics/CFSGSerreEvenOrderRefinement.lean` | In characteristic two every original four-term root operator squares to one. Actual root generation proves even cardinality for every nontrivial quotient, and removes all eight untwisted characteristic-two families from the explicit parity residual without classical-model recognition. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticEvenOrderRefinement.lean` | A concrete terminal rotation in the elementary matrix realization proves even order for every original simple type-C model, in every characteristic. The entire type-C branch is removed from the explicit parity residual. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticBinaryGenerationReduction.lean` | An explicit generating pair for the actual elementary matrices over the two-element field, transported through the original Serre realization, proves two-generation for every classifier-admissible binary type-C model. Nonbinary type-C models remain explicit. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticGenerationReduction.lean` | Two-generation for the entire original type-C family, using separate explicit pairs at field orders two, three and at least four. Full parameter extraction and signed Coxeter propagation recover every original simple root. All type-C tags are removed from the exact generation residual. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticFormPreservation.lean` | Every literal root preserves the standard alternating form. The actual elementary matrix group embeds into mathlib's symplectic group; the subsequent full-group theorem proves surjectivity. |
| `SymmetricSubgroupAsymptotics/CFSGSerreSquareZeroMatrixActions.lean` | Reusable rational, integral and base-change realization from proved square-zero matrix generators. The original Serre action and the literal elementary-matrix action have equal ranges on the same actual image. |
| `SymmetricSubgroupAsymptotics/CFSGOrthogonalDProjectiveRealization.lean` | All six original type-D Serre identities, integral descent, scalar commutant and actual action-kernel calculations give an isomorphism of the original simple projective model with the literal elementary central quotient, in every characteristic. |
| `SymmetricSubgroupAsymptotics/CFSGOrthogonalDEvenOrderRefinement.lean` | A noncentral chain Weyl word with fourth power one proves even order for every original type-D model of rank at least four. All D tags are removed from the exact parity residual. |
| `SymmetricSubgroupAsymptotics/CFSGOrthogonalDBinaryGenerationReduction.lean` | An actual Coxeter word and disjoint order-three/root word generate every original binary type-D model of rank at least four. Literal star-root recovery gives every original simple root; nonbinary D models remain explicit. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticMinimumIndexLower.lean`, `CFSGSymplecticMinimumIndexUpper.lean` | Actual root conjugacy and a moved projective point give `q <= ell` and `ell*(q-1) <= q^(2*r)-1` for the original symplectic model. Both simple-index inequalities are closed by the complete C packet below. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticCenterCardinality.lean`, `CFSGSymmetricMatrixCardinality.lean` | The actual natural symplectic centre has order at most two, and is trivial in characteristic two. A literal injective block cell has exactly `q^(r*(r+1))` symmetric parameter pairs; actual group membership is proved in the symmetric-shear packet below. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticLeastIndexSquare.lean` | The original type-C least proper subgroup index satisfies `ell^2 < |G|` at every admissible rank and field. An injective actual cell consists of two arbitrary symmetric shears and a two-coordinate SL Borel; its cardinality, the centre bound and the projective-point upper bound imply the inequality. The outer-automorphism bound is proved in the complete C packet below. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticHyperbolicPairOrbit.lean` | Actual elementary words move every nonzero natural vector and adjust a hyperbolic partner while fixing its first vector. All natural symplectic transvections belong to the same literal group, in every characteristic. This does not assert intrinsic recognition by abstract group automorphisms. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticFullGroup.lean` | Over every field and in every rank, the same elementary C matrix group is the full natural symplectic group. The first-pair stabilizer restricts faithfully onto the smaller elementary group; rank-one Gaussian elimination and the actual hyperbolic-pair words complete induction. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticCardinality.lean` | The exact finite-field order `q^(n*n) * product_(i=1..n) (q^(2*i)-1)` is proved for the actual elementary group and mathlib symplectic group, including ranks zero and one. Literal affine functional fibres count hyperbolic pairs, and the proved first-pair stabilizer gives the recurrence; no order formula is assumed. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticProjectiveNaturalRootLines.lean` | Actual natural transvections descend injectively modulo the original elementary centre. Root parameters, field-order cardinality, projective-vector labels and conjugation laws remain exact. The later complete C packet proves odd-characteristic intrinsic recognition and a characteristic-two stabilizer of index at most three. |
| `SymmetricSubgroupAsymptotics/CFSGGTwoEvenOrderRefinement.lean` | The literal G2 Serre matrices come from the actual D4 outer-node folding, with checked Cartan/Serre relations and integral quadratic root coefficients. A noncentral fourth-root word on the same representation image proves even order for every original simple untwisted G2 model. Only that branch is removed; no irreducibility of its natural eight-dimensional module is assumed. |
| `SymmetricSubgroupAsymptotics/CFSGOrthogonalDGenerationReduction.lean` | Two-generation for every original type-D model at rank at least four, over every prime-power field. The nonbinary pair recovers a full star-root line, propagates its signed parameters, and handles both endpoint geometries by actual subgroup conjugation before recovering every defining root. Combined with the binary pair, the entire D branch leaves the exact generation residual. |
| `SymmetricSubgroupAsymptotics/CFSGSymplecticSimpleIndexReduction.lean` | Both required simple-index inequalities for every original classifier-admissible C model. Actual projective-root recognition in odd characteristic and a root-family stabilizer of index at most three in characteristic two give a faithful action on the same points. The actual projective similitude count, exact field frame stabilizer and inner-group cancellation prove the outer bound; the entire C branch is removed from the residual. |
| `SymmetricSubgroupAsymptotics/CFSGOrthogonalBProjectiveRealization.lean` | The actual quadratic short-root operators descend through the rational, integral and original tensor image. The fourth coefficient vanishes on that same image. In odd characteristic, the actual scalar commutant and action kernels identify the original simple projective model with the elementary central quotient. |
| `SymmetricSubgroupAsymptotics/CFSGOrthogonalBEvenOrderRefinement.lean` | A genuine chain Weyl word handles odd characteristic; the proved original root-involution route handles characteristic two. Every original type-B model has even order, and all B tags are removed from the exact parity residual. |
| `SymmetricSubgroupAsymptotics/CFSGOrdinarySubgroupUpperProof.lean` | Coarse all-subgroup count from three retained inputs, using actual bounded nilpotent counts and constructed soluble covers. |
| `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` | Pinned compiler, package configuration, and exact dependencies. |
| `../scripts/check_lean.py` | Serialized compiler runner with memory, RSS, and wall-time limits. |
| `../scripts/check_lean_closure.py` | Dependency-order planning and conservative serial resume for a local module closure. |
| `../computations/python/` | Reproducible producers for the retained finite certificates. |

Build logs, receipts, scratch proofs, and research status records are kept
outside the publication repository.

The concrete CFSG statement is pinned at commit
`25507f8795f2e499b392f3312a576538e1c5ef78`; see
[source provenance](../provenance/CFSG_SOURCE.md). The optional shared
infrastructure keeps its remaining model cases explicit. An exhaustiveness
isomorphism supplies no quantitative property of a model without a proof of
that property. In particular, importing this infrastructure does not discharge
the remaining seven published inputs in the T1 facade below.

## Explicit input boundary

The final exports are
[T1_of_seven_published_inputs](SymmetricSubgroupAsymptotics/MarkedC4PublishedSevenTargets.lean)
and `allTargets_of_seven_published_inputs`. Their **seven named inputs** are listed
below. The character bundle has one published general class-number field. Both
abelian-quotient statements are now supplied by checked proofs. These are explicit theorem parameters,
not new Lean axioms. The kernel audit of both exports uses only `propext`,
`Classical.choice`, and `Quot.sound` in addition to the stated parameters.

Formerly external requirements are now discharged by checked proofs
or proved consumer replacements on the same pinned toolchain:

| Proved result | Export and proof source |
|---|---|
| Burnside: finite groups of order `p^a q^b` are soluble. | [`burnsideTwoPrimeSolvability`](SymmetricSubgroupAsymptotics/BurnsideTwoPrimeSolvability.lean), from the Klatzco–Kirov `odd-order-lean` proof. |
| Clifford: restriction to an actual normal subgroup is semisimple and irreducible constituent types are conjugate, over any field. | [`CliffordRawRestriction.proved`](SymmetricSubgroupAsymptotics/CliffordRestriction.lean), from the FormaTheoria Clifford proof and its arbitrary-field adapter. |
| Binary normal-subgroup bound: `#normalSubgroups(G) · 2^(−l²/4) ≤ 8 · 2^(2l)` for a group of order `2^l`. | [`fusariSpigaBinaryNormalSubgroup`](SymmetricSubgroupAsymptotics/BinaryNormalSubgroupBound.lean), from the stronger Palcoux–Spiga interval-count theorem, with coefficient `7.371968802 < 8`. |
| `PSL(3,F)` is simple for every field `F`, hence for `F₂` and `F₃`. | [`ProjectiveThreeSimplicity.simple`](SymmetricSubgroupAsymptotics/ProjectiveThreeSimplicity.lean), using new [elementary generation and perfectness proofs](SymmetricSubgroupAsymptotics/SLThreeElementaryGeneration.lean), mathlib's Iwasawa criterion and Apache-licensed projective-action backports. No ATLAS code is included. |
| `PGL₂(F₅) ≃ S₅`, using the actual quotient of `GL₂(F₅)` by its center. | [`PGLTwoFiveIsomorphism.publishedProjectiveIsomorphism`](SymmetricSubgroupAsymptotics/PGLTwoFiveIsomorphism.lean), through its faithful six-point projective action and a proved order-120 subgroup recognition theorem in `S₆`. No external classification or ATLAS source is used. |
| A faithful degree-five affine action is `C₅`, `D₁₀` or natural `F₂₀`, retaining literal point relabelling in the last case. | [`DegreeFiveAffineClassification.classification`](SymmetricSubgroupAsymptotics/DegreeFiveAffineClassificationComplete.lean), from actual regular-translation coordinates, a faithful embedding into `F₂₀`, and the unique order-ten subgroup. |
| Soluble subdirect socle length is at most the maximum factor socle length. | [`publishedSolubleSubdirectHeight`](SymmetricSubgroupAsymptotics/SolubleSubdirectSocleHeight.lean), from semisimple integral conjugation modules, the exact joint socle intersection, and quotient induction. This is the literal upper socle series. |
| Every actual degree-six action with three physical pairs has one of the seven required abstract group models. | [`DegreeSixThreePairClassificationProof.representativeClassification`](SymmetricSubgroupAsymptotics/DegreeSixThreePairClassificationProof.lean), from `C₂ ≀ S₃ ≃ S₄ × C₂`, the central projection dichotomy, and internal four-point subgroup recognition. Both actual `S₄` actions are retained by the original source interface. |
| Every degree-six two-triple affine cell with nontrivial kernel signs has one of the four required models. | [`publishedDegreeSixThreeByTwoAffineClassification`](SymmetricSubgroupAsymptotics/DegreeSixThreeByTwoClassificationProof.lean), through actual block coordinates, axes/product recognition, an irreducible `C₄` chart, and the full-wreath branch. No finite action classification premise is used. |
| Every actual transitive nonbinary eight-point action is point-conjugate to a fixed canonical representative. | [`S8TransitiveCanonicalCoverage.publishedClassification`](SymmetricSubgroupAsymptotics/S8TransitiveCanonicalCoverage.lean), through an actual transitive binary subgroup, unconditional binary action coverage, regular-seed normalizer and join certificates, and literal point-conjugacy witnesses. No eight-point classification premise is retained. |
| Every abelian p-group quotient of a faithful degree-n action has order at most p^(floor(n/p)); in particular every binary abelian quotient has order at most 2^(n/2). | [`abelian_pQuotient_card_le`](SymmetricSubgroupAsymptotics/PermutationAbelianQuotientOrderBound.lean), from full abelianization-order induction on actual central-prime blocks and complementary orbits, followed by actual Sylow restriction. Higher prime-power cyclic factors are retained. |
| A transitive binary eight-point group of excess two is the actual Heisenberg group E8; a nonabelian normal quotient has trivial denominator and center/derived orders two. | [`publishedDegreeEightExceptional`](SymmetricSubgroupAsymptotics/RDTDegreeEightExceptionalProof.lean), from unconditional coverage of all 26 binary actions, short ambient normal-generation words for the other 25 actions, and the intrinsic E8 center/derived structure. |
| Every abelian quotient of a faithful degree-n action has order at most 3^(n/3). | [`kovacsPraegerAbelianizationBound`](SymmetricSubgroupAsymptotics/KovacsPraegerAbelianizationProof.lean), using an actual nilpotent supplement, coprime support compression, and full p-group abelianization orders. |
| t ambient normal generators of the actual socle yield t jointly faithful finite irreducible complex representations. | [`zmudFaithfulCharacterTupleInput_proved`](SymmetricSubgroupAsymptotics/ZmudFaithfulCharacterProof.lean), through primary semisimple duality, coinduction and injected irreducible constituents. The empty tuple and arbitrary nonsoluble groups are included. |
| The bounded-factor ordinary epimorphism estimate retains every actual normal target F and the original derived-normal projection kernel. | [`rdtTheorem46BinaryInput_proved`](SymmetricSubgroupAsymptotics/RDTBoundedFactorEpimorphismProof.lean), from short adapted tuples and joint kernel incidence; its constants depend only on the factor-order bound. |
| A nilpotent permutation group of faithful degree-n has at most (38/25)^n conjugacy classes. | [`nilpotentConjugacyClassInput`](SymmetricSubgroupAsymptotics/NilpotentConjugacyClassProof.lean), using proved binary, ternary and large-prime fourth-power bounds and actual disjoint coprime supports. All sharp character consumers are unchanged. |
| If N is normal in a transitive binary permutation group and N≤G′, its ambient normal-generator number is at most floor(n/4). | [`publishedDerivedNormalQuarterBinary_proved`](SymmetricSubgroupAsymptotics/BinaryDerivedNormalQuarterProof.lean), by original-degree induction through actual central-pair kernels and faithful top images. The nonelementary top has a proved quarter-module bound; an elementary top kills the derived image. No excess classification is assumed. |
| O'Nan–Scott structure: a finite faithful primitive action is affine, or its full socle is T^k with the exact degree alternatives and a faithful original quotient embedding into Out(T) ≀ S_k. | [`publishedONanScottStructure`](SymmetricSubgroupAsymptotics/PrimitiveSocleRawONanScottProof.lean), from actual minimal normals, the proved Scott subdirect theorem, point-stabilizer maximality, coordinate automorphisms and the exact inner kernel. Both minimal normals are retained in the two-regular case. No simple-group classification is assumed for this structural theorem. |
| Uniform refined induced-module bounds, with one tuple length satisfying the half, logarithmic, coprime, primary and prime-power ceilings simultaneously. | [`traceyRefinedInducedModuleInput_proved`](SymmetricSubgroupAsymptotics/TraceyRefinedInducedModuleProof.lean), through actual Sylow/Mackey pieces, finite chain widths, Nakayama and coprime semisimplicity. The least actual uniform capacity satisfies every field; no induced-module theorem is assumed. |
| The two actual consumers of the soluble-orbit input. | [`traceySolublePermutationFormulaRawInput_proved`](SymmetricSubgroupAsymptotics/TraceySolublePermutationFormulaProof.lean) proves the exact soluble permutation formula using actual mixed-prime chains and an odd Hall subgroup. [`degreeFourCoreInduced_uniform_half`](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeFourCoreCapacityProof.lean) retains the actual globally normal ternary core and cyclic derangement quotient. The stronger arbitrary-local per-orbit input is unused and is not claimed as proved. |
| The actual strict-head and degree-eighteen consumers. | [Actual primitive consumers](SymmetricSubgroupAsymptotics/MarkedMomentComponentExhaustionWithoutCatalogue.lean) use the strict head bound away from degrees 10 and 12 and pay those two actual semisimple branches in the complete physical C3 source. [The degree-eighteen bound](SymmetricSubgroupAsymptotics/DegreeEighteenHeadFromActualSmallConsumers.lean) uses actual small heads. The stronger global strict-head statement and the 253-row correspondence are unused. |
| Complete actual primitive and imprimitive affine consumers. | [The order-based assembly](SymmetricSubgroupAsymptotics/CFSGSufficientAffineConsumerOrderAssembly.lean) retains every original block, normal denominator and translation kernel. Literal order divisors settle the general ranges; degree 32 uses the faithful binary five-dimensional representation, and degree 64 uses actual Clifford blocks, scalar fields and simple normal subgroups. No primitive composition theorem or affine-catalogue correspondence is a parameter. |
| The actual semisimple primitive-component compression. | [`primitiveComponentExhaustion_without_composition`](SymmetricSubgroupAsymptotics/PrimitiveComponentExhaustionWithoutComposition.lean) retains the actual full socle, quotient and block system with the sufficient margin `3q ≤ 2r`. Actual semisimple sources replace the bounded 116-row correspondence and the stronger unused degree-six/twelve classifiers. |


| Exact binary excess classification, including all degree bounds and proper-normal restrictions. | [`publishedProposition53Binary_proved`](SymmetricSubgroupAsymptotics/BinaryExcessProposition53Proof.lean) has no hypotheses. It retains the original pair kernels, joint parity and square carries, and proves the full abelianization and proper-normal consequences. |
| Full binary normal-F quotient theorem, including the exceptional degree-eight case. | [`publishedTheorem57Binary_proved`](SymmetricSubgroupAsymptotics/BinaryNormalFTheorem57Proof.lean) has no hypotheses. All original actions, normal denominators, ambient commutators `[F,Q]`, centralizers and excess/rank alternatives are retained. The degree-32 critical cases use actual joint capacities and annihilator-aware invariant intervals, with selected cocycle lifts proved internally. |
| Primitive ternary chief weight and the 3/10 weight bound. | [Both order-based bounds](SymmetricSubgroupAsymptotics/CFSGSufficientPrimitiveWeightsOrder.lean) retain every original chief series and use the literal affine-order divisor or full-socle quotient, with the sufficient simple-index bound. No primitive composition-length theorem or 336-row correspondence is required. |
| Complete twelve-pair sources without the transitive-twelve catalogue. | [Actual pair-source assembly](SymmetricSubgroupAsymptotics/DegreeTwoSourceWithoutTwelveOrSixteenCatalogue.lean) keeps all original axes and quotient fibres through actual minimal-block geometry. No 301-action correspondence is required. |
| Complete sixteen-pair and degree-four affine sources without primitive-sixteen correspondence. | [The actual affine consumer assembly](SymmetricSubgroupAsymptotics/PrimitiveAffineActualConsumerAssembly.lean) uses actual elementary translation kernels and the proved `GL₄(F₂) ≃ A₈` geometry. It constructs the required source, rather than assuming or asserting a stronger finite classifier. |

These proved results, both final exports, the T1-to-T2/T3 transfers and the
definition checks have standard-only axiom audits. Historical lower-level
constructors still accept the corresponding interface types; these are
filled internally in the final exports and are no longer assumptions there.
Selected upstream proofs and backports live in `External/`; exact revisions,
authorship, licenses and changes are recorded in
[`External/NOTICE`](SymmetricSubgroupAsymptotics/External/NOTICE).

The half-dimension and logarithmic induced-module statements follow from
that proved refined theorem through
[`TraceyRefinedInputConsequences`](SymmetricSubgroupAsymptotics/TraceyRefinedInputConsequences.lean).
The final route needs only the actual automorphism bound `|Aut(S)| ≤ |S|²`.
[`CFSGSimpleAutomorphismOrderBound`](SymmetricSubgroupAsymptotics/CFSGSimpleAutomorphismOrderBound.lean)
derives it from the retained simple-index inequalities by counting the literal
inner subgroup and outer quotient. The actual affine-wreath and semisimple
coefficients retain their original coefficient three. The stronger
finite-simple two-generation theorem is not a final input or a claimed
unconditional conclusion; its older consumers remain compatibility routes.

Likewise,
[`CFSGPrimitiveRelativeThreeHeadTail`](SymmetricSubgroupAsymptotics/CFSGPrimitiveRelativeThreeHeadTail.lean)
proves `20 δ_G(N) < 3w` for every actual primitive normal pair of degree
`w ≥ 34`. Affine heads use the literal affine-order divisor; nonaffine heads
use the actual full-socle quotient. Below 1024 the affine arithmetic ranges
over bounded prime-power parameters, and the nonaffine proof has at most four
socle factors. Above that cutoff an elementary quadratic-log bound suffices.
No ordinary primitive normal-generator theorem is assumed. The stronger
ordinary-rank statement is not asserted by this replacement.

The binary transitive permutation-submodule formula follows from the
proved refined induced-module theorem. The uniform soluble formula uses
two actual capacities on the same induced module. The three ordinary
original-word prices of RDT Theorem 5.5(ii) follow from the now-proved exact
binary excess theorem and intrinsic proper-normal ceiling. Their original
dependent factors and maximal full tail are unchanged.

The full primitive degree-six, degree-nine, bounded-socle and small-affine
classifiers remain optional conditional APIs. T1 instead uses actual
semisimple and affine sources with sufficient numerical margins. No finite
catalogue-completeness input remains in the final signature. The stronger
global strict-head theorem is also unused: the complete physical C3 source
pays the actual degree-10/12 sector separately.

The auxiliary odd-Hall construction and stabilizer-induced module transport
are proved internally, including the empty and singleton endpoints. The
standalone Kovács–Praeger parameter is filled by the proved full
abelianization theorem.

The separate Dixon and soluble-linear cube inputs are removed.
[Dixon's order bound](SymmetricSubgroupAsymptotics/ElementaryDixonOrderWithoutCatalogue.lean)
uses actual primitive linear/socle structure and block and orbit induction.
At degree 81, every complement has an original chief-charge budget at most 17 from `|GL₄(F₃)| = 24261120`. The full Schur bottom layer adds at most one unit, so the complete exponent is at most `18 log₂(3)/3 < 9.6` and fits the physical window. This constructs the required source without asserting the stronger soluble-complement cube bound or the general Halasi–Maróti theorem.

The large-orbit soluble generation estimate is proved without either sharp primitive input in
[`CFSGSolubleOrbitFinal`](SymmetricSubgroupAsymptotics/CFSGSolubleOrbitFinal.lean).
The proof uses unconditional soluble primitive order and rank bounds and
preserves the original correlated orbit actions. The actual full affine
consumer is assembled in
[`CFSGSufficientAffineConsumerOrderAssembly`](SymmetricSubgroupAsymptotics/CFSGSufficientAffineConsumerOrderAssembly.lean).
The stronger ordinary primitive composition-length theorem remains a
compatibility interface and is not claimed proved by these replacements.

The Pyber representative input is unnecessary for the final marked moment.
The [constructed soluble cover](SymmetricSubgroupAsymptotics/CFSGSolubleWreathContainersRate.lean)
has at most `2^(4096 b log₂(b+2)^4)` labels, retaining every original orbit
and point label. Its [marked encoding](SymmetricSubgroupAsymptotics/CFSGConstructedSolubleContainersMoment.lean)
chooses one actual containing soluble group, records the same relative
tuple there, and retains the original character restrictions and bounded
source moment. The [global assembly](SymmetricSubgroupAsymptotics/CFSGConstructedContainersGlobal.lean)
therefore needs neither `h86` nor a transitive-count premise. The separate
nonsoluble pre-E7 menu still uses `hLMM`. This does not assert Pyber's
stronger `2^(13n)` conjugacy-class estimate. The final [catalogue adapter](SymmetricSubgroupAsymptotics/T1CatalogueFromMarkedMoment.lean)
uses this proved moment directly. The character bundle's binary field is
also filled internally. The mixed-prime abelianization and faithful-character
tuple theorems, and the arbitrary-normal-target epimorphism theorem, are
proved internally as well.

The sharp unrestricted nilpotent-core theorem is no longer needed by T1.
[`bounded_nilpotent_core_generation`](SymmetricSubgroupAsymptotics/BoundedNilpotentCoreGeneration.lean)
proves that a finite soluble group of socle height ≤L, with every chief
section of every subgroup of order ≤B and every abelian section of
prime-factor length ≤M, has an actual nilpotent subgroup supplemented by
at most `L*(B!+1)*floor(sqrt M)` ordinary generators. The proof uses the
actual socle's isotypic rows, shares generators across small multiplicities,
and centralizes the large rows before quotient induction. For the original
orbit cutoff C, the checked choices are `L=B=C!` and `M=2b`.
[`CFSGConstructedContainersGlobal.marked_bound`](SymmetricSubgroupAsymptotics/CFSGConstructedContainersGlobal.lean)
keeps that original source and orbit cutoff; only the fixed tuple-control
constant increases. This removes `hseven` without asserting the sharper
unrestricted `4L*sqrt M` theorem. No new hypothesis replaces it.

The coarse ordinary bound is now supplied by
[`ordinarySubgroupUpper_of_soluble_generation`](SymmetricSubgroupAsymptotics/CFSGOrdinarySubgroupUpperFromSoluble.lean).
For each fixed orbit cutoff C, the actual bounded nilpotent family satisfies
`#NilpotentFamily(C,b) ≤ 2^(b²/16 + A_C b log₂(b+2))`.
The proof retains the actual binary and odd nilpotent sectors, their original
cutoff and their joint subdirect words. A constructed soluble container menu
has size `2^(O(b log⁴(b+2)))`; original-support compression and the retained
large-orbit generator bound then give `s_n ≤ 2^(n²/16 + β n√n)`.
This removes `hodd` as an independent parameter. The old eleven-input
exports remain available as compatibility theorems.

RDT means Roney-Dougal–Tracey, arXiv:2503.05416v1. TR means Tracey's
2018 transitive-generation paper, with page locators referring to its linked
author manuscript. HRD means Holt–Roney-Dougal (2013); GPRV means
Glasby–Praeger–Rosa–Verret (2018). PRIM means the published primitive
classifications and pinned PrimGrp 3.4.4; TRANS means the published
transitive classifications and pinned TransGrp 3.6.5. CLASS means the
Garonzi–Maróti general class-number theorem and the now-proved Maróti
nilpotent bound. Full titles, links, and
version conventions appear in the [literature register](../provenance/LITERATURE.md).

The remaining inputs are ordinary published mathematical theorems.
No action-catalogue correspondence, project capacity, marked moment,
complete source or asymptotic target is included in them. The labelled
transitive-count theorem remains a counting input. The coarse
all-subgroup upper bound is proved from `hAG` alone. The actual soluble
primitive bounds and large-orbit generation theorem are now unconditional
(`CFSGSolublePrimitiveCoarse.lean`, `CFSGSolubleOrbitFinal.lean`).
The primitive composition-length and ordinary normal-generator theorems are no longer T1 parameters; the required actual consumers are proved from orders and the retained simple-index inequalities.

| Lean parameter and definition | Mathematical input | Published source or correspondence |
|---|---|---|
| [lit : PreE7CharacterPublishedInputs](SymmetricSubgroupAsymptotics/CharacterLiteratureProvedBinary.lean) | One field: permutation class number ≤5^((b−1)/3) for b≥4. | Garonzi–Maróti, Theorem1.1. The two abelian-quotient fields and nilpotent class-number field of the older internal API are proved and filled internally. |
| [hAG : PublishedAschbacherGuralnickSolubleGeneration](SymmetricSubgroupAsymptotics/MarkedC4AschbacherGuralnickSolubleGeneration.lean) | Every finite group generated by a soluble subgroup and one element. | Aschbacher–Guralnick, J.Algebra77 (1982),189–201; RDT Thm8.4 p32. Ambient-recovery field internal. |
| [hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput](SymmetricSubgroupAsymptotics/TraceyCorollaryThreeTwelveRaw.lean) | Exceptional degree3·2^m action has actual soluble subgroup and full binomial orbit partition, Mersenne exponent≥3. | TR Cor3.12 p17 PLUS preceding nonabelian PSL₂(p) construction Thm1.8/Cor3.11 excluding p=3. Cor3.12 alone is insufficient for exponent≥3. |
| [hLMM : LucchiniMenegazzoMorigiTransitiveCountInput](SymmetricSubgroupAsymptotics/Non2PreE7MenuMassAggregation.lean) | Labelled transitive subgroup count is subquadratic-exponential. | Lucchini–Menegazzo–Morigi, BLMS32 (2000),191–195; exact labelled2^(Cn²/√logn) statement is sourced through RDT introductionp2. ID LIT-TRANSITIVE-COUNT. |
| [hTraceyPerm : TraceyPermutationGeneratorInput](SymmetricSubgroupAsymptotics/TraceyAffineInducedModuleInput.lean) | Transitive degree w≥2 group generated by≤ceil(w/√log₂w). | weakening; TR Thm1.1(1), constantc<1. Not the sharper2021 √3/2 bound. |
| [hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds](SymmetricSubgroupAsymptotics/PrimitiveSocleRawSimpleIndex.lean) | For the actual least proper subgroup index ℓ of a finite nonabelian simple T: ℓ² < card(T) and card(Out(T)) ≤ 3 log₂ ℓ. | Ballester-Bolinches–Esteban-Romero–Jiménez-Seral, Theorem A(4), p.4 of arXiv:2203.16976v2; LIT-SIMPLE-INDEX. The bound ℓ ≥ 5 and all profile deductions are internal. |
| [hMN : McIverNeumannPermutationGeneratorBound](SymmetricSubgroupAsymptotics/McIverNeumannPermutationSection.lean) | Every subgroup of S_s except literally fullS3 has≤floor(s/2) generators. | Blackburn–Neumann–Venkataraman, Enumeration of Finite Groups (2007), Lemma 5.2; proof reference Cameron–Solomon–Turull, Journal of Algebra 127 (1989), §4; LIT-MCIVER-NEUMANN. |

The degree-eight affine-complement branch has complete checked coverage
of all fifteen actual `GL₃(F₂)` subgroup classes. Invariant vector and dual
flags exclude twelve, and literal intertwiners identify the three survivors.
The current degree-16 consumer keeps the original translation kernel; the
degree-27 consumer uses proved linear structure. Their stronger catalogue
interfaces are unused. Full transitive degree-eight correspondence is
separately proved internally as described above.

The quantitative `PublishedPrimitiveSocleDichotomyInput` is constructed from
the proved `publishedONanScottStructure` and the retained `hSimpleIndex`;
neither raw O'Nan–Scott structure nor the quantitative profile is an additional
parameter here. Likewise the complete small-affine receipt, degree-25
scalar datum and chief bound, exceptional Tracey `5/16` deduction, actual
Clifford restriction and faithfulness, Burnside solvability, the binary normal-subgroup bound, projective-three simplicity and the projective-five isomorphism, the degree-five affine classification, all low-degree source data, marked-C₄ moment, and
`PreE7PrimitiveAffineConsumerData` are internal conclusions. The weaker
`PermutationSubgroupGeneratorBound` is derived from `hMN`, including the
full `S₃` exception.

The independent mathematical input audit is closed at this boundary.
Recursive source/object verification of the final facade and public root,
and the final exported-declaration axiom audit, passed on 22 October 2026.
The published hypotheses remain explicit mathematical inputs.

## Proof organization

The final composition follows this chain:

1. Checked Burnside, Clifford, subgroup-count and projective-three proofs,
   the checked subdirect socle-height and degree-six classifiers, and the
   remaining published structure and formulas construct the finite affine package,
   quantitative socle profiles, exceptional Tracey head bound, and actual
   Clifford restriction consequence.
2. Primitive and imprimitive affine consumers supply complete original
   action sources, retaining the literal normal axes, module charts,
   source weights, and quotient maps.
3. Fusion, menu aggregation, binary rank tails, and the marked-C₄ moment
   give the complete negligible remainder and forward recurrence.
4. The critical-family counting identity and recurrence prove T1. The
   proved saddle and elementary transfers then give AllTargets.

| Part | Main modules | Role |
|---|---|---|
| Definitions | [Statements](SymmetricSubgroupAsymptotics/Statements.lean), [DefinitionsVerified](SymmetricSubgroupAsymptotics/DefinitionsVerified.lean) | Literal subgroup counts, explicit benchmarks, and definition checks. |
| Analysis | [ShiftedCoefficientRatio](SymmetricSubgroupAsymptotics/ShiftedCoefficientRatio.lean), [SaddleBenchmarkEstimates](SymmetricSubgroupAsymptotics/SaddleBenchmarkEstimates.lean), [ElementaryBenchmarkEstimates](SymmetricSubgroupAsymptotics/ElementaryBenchmarkEstimates.lean) | Uniform coefficient estimates and the transfers from T1 to T2 and T3. |
| Final composition | [T1RelativeClosure](SymmetricSubgroupAsymptotics/T1RelativeClosure.lean), [MarkedC4PublishedSevenTargets](SymmetricSubgroupAsymptotics/MarkedC4PublishedSevenTargets.lean) | Complete remainder estimate and final T1/AllTargets exports. |
| Affine consumers | [PrimitiveAffinePrimitiveConsumer](SymmetricSubgroupAsymptotics/PrimitiveAffinePrimitiveConsumer.lean), [PrimitiveAffineImprimitiveComponentTransfer](SymmetricSubgroupAsymptotics/PrimitiveAffineImprimitiveComponentTransfer.lean) | Transfer through actual block systems, including small and binary component groups. |
| Finite affine structure | [SmallAffineCanonicalReceipt](SymmetricSubgroupAsymptotics/SmallAffineCanonicalReceipt.lean), [DegreeTwentyFiveActualProjectiveData](SymmetricSubgroupAsymptotics/DegreeTwentyFiveActualProjectiveData.lean), [PrimitiveAffineCanonicalFiniteLiterature](SymmetricSubgroupAsymptotics/PrimitiveAffineCanonicalFiniteLiterature.lean) | Construct all 34 receipts, the actual scalar datum and every-chief bound, and the full finite affine package. |
| Nonaffine structure | [PrimitiveSocleRawDichotomy](SymmetricSubgroupAsymptotics/PrimitiveSocleRawDichotomy.lean), [PrimitiveSocleRawProfile](SymmetricSubgroupAsymptotics/PrimitiveSocleRawProfile.lean) | Construct the profile on the actual full socle and exact original quotient from ordinary published structure. |
| Raw module inputs | [TraceyExceptionalThreeFromRaw](SymmetricSubgroupAsymptotics/TraceyExceptionalThreeFromRaw.lean), [CliffordActualRetainedConstituent](SymmetricSubgroupAsymptotics/CliffordActualRetainedConstituent.lean) | Derive the 5/16 head bound and retained-wreath faithfulness. |
| Degree two | [PrimitiveAffineDegreeTwoClosedSourceAssembly](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoClosedSourceAssembly.lean), [DegreeSixteenCompleteGeometricSource](SymmetricSubgroupAsymptotics/DegreeSixteenCompleteGeometricSource.lean) | Assemble complete actual pair sources; the latter supplies the former adapter's sixteen-pair argument. |
| Joint and B6 sources | [PrimitiveAffineDegreeTwoTwelveJointComplete](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoTwelveJointComplete.lean), [SixPairActualCompleteRepresentativeSource](SymmetricSubgroupAsymptotics/SixPairActualCompleteRepresentativeSource.lean), [PairedEightActualRepresentativeSource](SymmetricSubgroupAsymptotics/PairedEightActualRepresentativeSource.lean) | Resolve every joint entry and use universal sources for six and eight pairs, without 182-action or 527-action source census assumptions. |
| Degrees three and four | [PrimitiveAffineDegreeThreeConcreteSource](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeThreeConcreteSource.lean), [PrimitiveAffineDegreeFourPublishedResidueSource](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeFourPublishedResidueSource.lean) | Complete the other small-component branches with original module and quotient data. |
| Marked-C₄ counting | [MarkedC4RDTAssembly](SymmetricSubgroupAsymptotics/MarkedC4RDTAssembly.lean), [MarkedC4PublishedBoundedWordReduction](SymmetricSubgroupAsymptotics/MarkedC4PublishedBoundedWordReduction.lean) | Construct the marked moment from ordinary unmarked theorems. No marked reduction or moment bound is assumed. |

Lower-level APIs retain conditional constructors. For example,
`source_of_sixteenPairSource` accepts data supplied by
`DegreeSixteenCompleteGeometricSource.residualSource`. Such local arguments
are intermediate interfaces, not extra assumptions of the final target.

## Finite certificates and coverage

The checked finite families include all **108/108 degree-four rows**, all
**283/283 joint degree-two entries**, and all **34/34 small-affine
representative receipts**. Degree-three sources and the actual six-pair,
eight-pair, and sixteen-pair constructions are complete. Sixteen-pair
coverage uses actual minimal-block geometry: primitive, eight pairs, four
quartets, or two primitive eight-point blocks. The older incomplete
sixteen-point locator is not a final premise.

Local certificate checks and catalogue completeness are different claims.
Kernel checks prove the numerical and structural assertions at the fixed
representatives. The explicitly named published correspondences supply
their coverage. Neither an exporter finishing nor an old object file proves
a newly edited Lean source theorem.

The finite affine chief bound uses a nonabelian order saving on the original
group or an actual monolithic quotient. It permits central abelian factors,
including those in GL₂(4) and GL₃(3); it does not require a nonabelian core
inside every nontrivial original normal subgroup. The degree-25 argument
also handles nonsplit scalar covers through the original chief series.

The selected small-affine producer is
[export_lean_small_affine_soluble_order.py](../computations/python/export_lean_small_affine_soluble_order.py).
It handles one selected representative and supports `--verify-existing`.
The old bulk action-table and normal-lift computations are not part of this
recovery workflow.

## Verification boundary

On 22 October 2026, recursive verification of all 10,825 local modules in
the public import closure matched their current sources,
compiled objects, direct dependency fingerprints, and pinned toolchain
against successful check receipts. Matching historical receipts were reused
with explicit relocation evidence; stale consumers were checked serially.
All sources in this closure are tracked in the main checkout and match the
audited bytes. Optional modules outside this public closure are not covered
by this release claim.

A fresh axiom audit of `T1_of_seven_published_inputs`,
`allTargets_of_seven_published_inputs`, `T2_of_T1`, `T3_of_T1`,
`allTargets_iff_T1`, and `definitionChecks` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The final audit used the serialized
runner with 16 GiB allocator and RSS limits. Logs, receipts, relocation
attestations, and detailed audit records stay outside this repository.
Pinned external Lean/mathlib objects form a separate dependency boundary;
their contents were not recursively rebuilt and source-certified here.

A standard-only `#print axioms` result excludes extra Lean axioms and native
computation acceptance from that theorem. It does not prove its explicit
published hypotheses or certify stale source objects. This release combines
the explicit mathematical boundary above, current kernel checks, and
matching dependency provenance. It establishes verification relative to
the stated published inputs, rather than a proof of those inputs themselves.

The optional CFSG route also includes `CFSGOrthogonalBGenerationCharTwoReduction.lean`: every original classifier-admissible type-B model over a field of characteristic two is proved two-generated. The actual natural B-to-C restriction is injective by its transpose-quadratic invariant and surjective by finite-field squaring. Original-source descent uses the same actual action image and its nontrivial central quotient. The subsequent `CFSGOrthogonalBGenerationReduction.lean` closes odd characteristic as well: an actual torus/filter pair, cleaned signed orbit and coefficient-two recovery yield all original simple roots. Every original B model of rank at least three is now two-generated and all B tags leave the residual.

The optional exceptional infrastructure constructs the actual E6/E7/E8 norm-two lattices and derives finiteness, a coordinate base, reducedness, irreducibility and the exact transposed Cartan matrices (`CFSGExceptionalNormTwoBases.lean`). It maps each original rational Lie presentation to its literal Geck matrices. `CFSGNormTwoRootStrings.lean` derives the simply-laced ordinary string coefficients from positive integer norms. `CFSGExceptionalGeckIntegralData.lean` now supplies integral divided powers and same-image fourth-coefficient cancellation for all three original Cartan sources over every coefficient ring. The actual same-image Weyl word is now proved noncentral of fourth power one in every characteristic (`CFSGExceptionalGeckEvenOrderRefinement.lean`), giving even order on all three original simple projective models. Those three untwisted tags leave the parity residual. The later checked continuation proves good-Sylow generation and sufficient outer-order bounds; stronger two-element generation is separate and unused by T1.

`CFSGOrthogonalBCharTwoSimpleIndexReduction.lean` transfers both simple-index bounds from the actual natural projective C group to the original characteristic-two B model. The original B image kernel is proved trivial by an actual fixed-vector orbit argument; the same centre quotients are transported before transferring simplicity. No C-source simplicity or characteristic-two B scalar-commutant hypothesis is assumed. The whole B family now leaves the simple-index residual, by the odd-characteristic continuation described below.

The generic primitive-input foundations (`CFSGCompositionLengthCardinality.lean`, `CFSGSubnormalSimpleProduct.lean`, `CFSGSimpleProductCompositionLength.lean`) now prove that every actual composition series has length at most log₂ of the original group order; every subnormal subgroup of a finite product of nonabelian simple groups is a literal coordinate product; and every composition series of that product has length at most its number of original factors. These are proved without CFSG or a Jordan–Hölder input. They do not discharge the sharper primitive composition-length or normal-generation bounds.

The original type-D models now have proved least-index bounds (`CFSGOrthogonalDIndexSquare.lean`, `CFSGOrthogonalDIndexStarLower.lean`): for rank r ≥ 4, q^(r−1) ≤ ℓ, ℓ(q−1) ≤ q^(2r)−1, and ℓ² < |D_r(q)|. The lower bound uses a literal projective root-star and actual conjugators; the upper and squared bounds use the actual point action and an injective matrix cell. This holds in every characteristic. The continuation below now proves the D outer bound in every rank at least five. The stronger coefficient-three simple-index/Out residual retains D4 only;
the sufficient internal boundary below now handles D4 too.

Odd-characteristic B now also satisfies the original-model squared-index bound and explicit index bounds (`CFSGOrthogonalBIndexBounds.lean`): q ≤ ℓ, ℓ(q−1) ≤ q^(2r+1)−1, and ℓ² < |B_r(q)| for r ≥ 3. The proof retains the actual quadratic short roots, establishes centre one from the preserved form and determinant, and counts an injective shear/SL cell. This includes r=3, q=3. The subsequent polar realization and actual SO/elementary index now prove the outer bound as well; both characteristics leave the exact B residual below.

The optional generic primitive route also proves bounds on the same actual series and subgroups (`CFSGCompositionExtension.lean`, `CFSGAffineCoarseComposition.lean`, `CFSGNonaffineCoarseComposition.lean`, `CFSGNonaffineNormalRank.lean`). For S=T^k, every original composition series satisfies a(G) ≤ k+log₂|G/S|; the actual outer-wreath embedding bounds |G/S| by |Out(T)|^k k!. Every faithful affine profile of degree n has composition length and ordinary subgroup rank at most (1+⌊log₂n⌋)log₂n. For normal N in the nonaffine group, d(N) ≤ 2k+log₂|G/S| follows under the explicitly displayed d(T) ≤ 2 premise. These coarse bounds and ordinary-rank extension lemmas do not discharge the sharp primitive published inputs or add new public assumptions.

`CFSGPrimitiveCoarseDegreeBounds.lean` combines those actual affine and full-socle constructions into degree-only bounds for every faithful nontrivial finite primitive action: a(G) ≤ L²+3L for every original composition series, and d(N) ≤ L²+4L for each actual normal subgroup, where L=log₂(degree). The first theorem displays only `PublishedSimpleIndexBounds`; the second also displays `FiniteSimpleTwoGeneratorBound`. Neither uses the sharp primitive composition or primitive normal-generation input. These coarse conclusions do not replace those sharper public T1 premises yet.

The type-D intrinsic infrastructure (`CFSGOrthogonalDIndexUnipotentCenter.lean`, `CFSGOrthogonalDIndexUnipotentFixedSpace.lean`) identifies the centre of the actual flag-unitriangular subgroup with its highest paired-root line and the additive group of the same field, in every characteristic. Its fixed vectors are exactly the first natural line. The proof preserves the actual split quadratic form, excluding the spurious diagonal shear in characteristic two. The continuation (`CFSGOrthogonalDIndexOddSylow.lean`) proves that this same subgroup is Sylow in odd characteristic, using its actual partial-flag normalizer and middle two-plane action. The all-characteristic continuation is now proved in `CFSGOrthogonalDIndexSylow.lean`: parity of three maximal singular-space distances excludes the final-pair swap from the actual unipotent normalizer. The completed polar and D4 triality automorphism continuations are described below.

The odd-B intrinsic packet (`CFSGOrthogonalBProjectiveLongRoots.lean`) now proves that the literal flag-unitriangular subgroup is Sylow, its normalizer is the actual flag Borel, and its centre is exactly the highest long-root field line. Actual projective automorphisms preserve the conjugate root lines (`CFSGOrthogonalBProjectiveRootLines.lean`). Each line has a well-defined natural two-plane label, recovered as range(x-I) from any nonidentity root element. All statements retain the same original matrix subgroup and projective quotient. The continuation `CFSGOrthogonalBSingularPlaneAction.lean` now proves coverage of all totally singular two-planes and the exact projective automorphism action on them, using actual pair normalization and the literal tail embedding. The polar-point action, semilinear realization and odd-B outer bound are now proved by the continuation below.

`CFSGPrimitiveSublinearBounds.lean` proves that those estimates are uniformly sublinear across all actual primitive actions. Its first applications are an eventual c=1 relative-character tail and an eventual three-tenths primitive chief-weight tail. The statements retain only the displayed simple-index/Out and, where used, simple-two-generation inputs; they do not invoke the sharp primitive inputs. These are infinite-tail replacements with a uniform eventual threshold, not proofs of the existing cutoffs 34/45 or of the intervening bounded ranges. The public T1 premises are unchanged.

The original untwisted F₄ parity branch is now proved (`CFSGFFourEvenOrderRefinement.lean`). The actual E₆ fold satisfies the pinned F₄ Serre relations; a long-root Weyl word has fourth power one and is noncentral on the same original image, in every characteristic. This removes precisely F₄ from the optional parity residual. The original F₄ good-Sylow theorem is also proved (`CFSGFFourOriginalGoodSylow.lean`), as are its least-index square and complete outer-order budget. The public seven-input boundary is unchanged; the optional CFSG endpoint below removes this model from both residual callbacks.

The optional soluble-generation reduction now proves actual good-Sylow
data for every original A, B, C, D and Suzuki model
(`CFSGClassicalGoodSylowReduction.lean`). The original B and D proofs
retain their actual flag-unitriangular subgroups, soluble normalizers and
displayed opposition/Coxeter conjugates; C uses its actual J-conjugate.
Central-quotient and original-source transport preserve those witnesses.
Exactly these families leave the narrowed Aschbacher–Guralnick callback;
that entire published input is still retained for the other open models.

Original twisted E₆ now has even order in every characteristic
(`CFSGTwistedE6EvenOrderRefinement.lean`). Odd characteristic uses literal
commutators in its derived fixed subgroup. At prime two, the actual A₂
Singer-seven and Weyl-braid identities yield both root signs in the derived
image; exact commutator-image transport returns preimages in the original
derived fixed subgroup. This removes precisely twisted E₆ from the parity
residual. This optional family result does not discharge another entire public input. Actual odd-B singular-vector normalization is
also proved (`CFSGOrthogonalBSingularVectorOrbit.lean`), in rank at least
two, using original matrix elements. It supplies the original-vector input to the point reconstruction below;
the B outer bound is proved by the later polar continuation.

The original odd-B local point reconstruction is now proved in
`CFSGOrthogonalBPointStars.lean`. Exact counts of the same original
singular cone and tangent cones yield a fourth singular plane through
any point avoiding three given directions. The reconstructed point action
is faithful on the plane-relation automorphism group and preserves original
orthogonality (`CFSGOrthogonalBPointOrthogonality.lean`). The actual R11
lower common-neighbour count is now proved on the original residual vectors
in `CFSGOrthogonalBR11CommonNeighbourCount.lean`. The resulting
`CFSGOrthogonalBPointAction.lean` installs the faithful original projective-group
automorphism action, with no count or recognition hypothesis. The later
semilinear realization and actual SO/elementary index now close the B outer bound.

`CFSGOrthogonalDIndexSingularPlaneOrbit.lean` now proves the full original
singular-vector, pair and two-plane orbit in every characteristic.
`CFSGOrthogonalDIndexProjectiveRootRelation.lean` proves intrinsic
root-product adjacency preservation on the original central quotient.
Specific quotient commutation and product equalities lift using common
fixed vectors; no arbitrary quotient-automorphism lift is assumed.
The continuation below now proves the actual D₄ triality point action and
outer cardinality bounds.

`CFSGExceptionalGeckSylowGeneration.lean` proves that the original E₆,
E₇ and E₈ models are generated by two conjugate defining-characteristic
Sylow subgroups. The actual positive-root subgroup is normal in its
literal soluble torus envelope, and every defining-prime-power element
of that envelope lies in the positive subgroup
(`CFSGNormTwoGeckBorelPowerElements.lean`). The continuation now proves actual Sylow maximality and soluble
normalizers in every characteristic (`CFSGExceptionalGeckGoodSylow.lean`).
Its diagonal-factor proof allows ambient scalar normalizers; no equality
with a prematurely restricted Borel is assumed. Exactly E6, E7 and E8 leave
the narrowed AG callback in `CFSGExceptionalGoodSylowReduction.lean`.
Other families remain explicit, and the public T1 theorem still retains
the seven listed published inputs.


The optional polar continuation transports every original singular subspace
and preserves its dimension. The **whole original B family now satisfies both
simple-index inequalities**, in both characteristics
(`CFSGOrthogonalBSimpleIndexReduction.lean`). For odd B, actual point/plane
reconstruction, unique global field coherence, maximal-space linearity,
opposed-space normalization, common mixed-scalar coherence, the genuine
square obstruction, and the actual special-isometry kernel prove the full
polar realization (`CFSGOrthogonalBSemilinearPolarIsometry.lean`). The actual
SO/elementary index is at most two in every positive rank over an odd finite
field; cancellation gives |Out| ≤ 2|Aut(K)|. No named SO/Omega recognition,
independent automorphism theorem, or group-order formula is assumed. Every B
tag is removed from the exact remaining simple-index predicate.

For D of rank at least five, `CFSGOrthogonalDIndexPolarPointAction.lean`
constructs the faithful original point action from the proved R11 neighbour
gap. `CFSGOrthogonalDIndexSingularSubspaceSemilinear.lean` extends it to actual
quadratic singular subspaces and proves their local projective semilinearity.
The carriers require Q=0 over every field, including characteristic two.
`CFSGOrthogonalDGlobalField.lean` now proves ONE global field component and
actual linear normalization on all maximal singular spaces. The proof uses
the checked rank-two base, genuine two-component maximal-space normalization,
and codimension-two root overlaps. `CFSGOrthogonalDNegativeDilation.lean`
proves that linear pieces fixing both opposed halves give one actual
quadratic dilation on every singular point. The direct cross-pairing
zero-locus argument now glues opposed pieces to a genuine quadratic
similitude. `CFSGOrthogonalDSemilinearPolarSimilitude.lean` installs this
whole realization on every original rank-at-least-five automorphism.
The actual O/E index is at most four (at most two in characteristic two);
scalar-kernel containment bounds the GO point image by |O|, and the actual
elementary centre has order at most two. Thus |Out| ≤8|Aut(K)|. The original
q^(r−1) least-index lower bound proves both required simple-index
inequalities in every rank r≥5 and every characteristic. These tags leave
the exact residual in `CFSGOrthogonalDHigherRankSimpleIndexReduction.lean`.
For D4, `CFSGOrthogonalDIndexTrialityD4TwinQuotient.lean` proves the reversible
local quotient by true twins, with exact q-element original neighbour fibres
and three literal projective parameters. The actual root-plane stabilizer
now has a proved local direction homomorphism with kernel index at most six
(`CFSGOrthogonalDIndexTrialityD4LocalDirectionIndex.lean`). The original plane
graph is connected, and its local maximal cliques are exactly the literal
tops and the two sorts of point/maximal-space stars. The genuine global
type homomorphism is proved, and the subgroup preserving the natural
POINT type has index at most THREE
(`CFSGOrthogonalDIndexTrialityD4PointTypeStabilizer.lean`). It may interchange
the two maximal-space types. The connected classes of original star
cliques now reconstruct the actual quadratic points, and the subgroup
action on them is faithful and preserves point/plane incidence and polar
orthogonality in every characteristic. The same rank-four semilinear
realization and actual inner/outer cancellation prove
**|Out(D4)|≤24|Aut(K)|**, sharpened to **6|Aut(K)|** in characteristic two
(`CFSGOrthogonalDFourOuterCardinality.lean`).

`CFSGClassicalSufficientSimpleIndexReduction.lean` consequently removes
**all original untwisted classical models and Suzuki** from the exact
sufficient simple-index residual. This internal boundary retains the
squared-index inequality, coefficient three for least index below27,
coefficient six in general, and Out≤24 below30. Checked consumers preserve
the original chief-weight, strict-head and component-compression targets:
degrees27..63 use actual quotient rounding, and degree64 onward uses
the two-thirds compression. The stronger published coefficient-three
theorem remains available. Full T1 and AllTargets forwarding from the
sufficient boundary is proved in
[`CFSGSufficientPublishedTargetsOrder`](SymmetricSubgroupAsymptotics/CFSGSufficientPublishedTargetsOrder.lean).
This optional route has six other published inputs plus sufficient
simple-index bounds. Its CFSG variant still exposes the unproved
nonclassical model callback; it is not a CFSG-only theorem.

The exceptional Geck infrastructure proves arbitrary-parameter collecting,
actual positive-complement factorization, rank-one parabolic cells and torus
normalization over all fields. Integral lattice gradings detect membership
in the actual complement or simple-root subgroup and are transported by the
actual Weyl matrices. `CFSGNormTwoCoordinateBruhatCover.lean` proves the
unconditional whole Bruhat cover in the SAME actual Geck group.
`CFSGNormTwoCoordinateNormalizerDiagram.lean` reduces its actual normalizing
Weyl words to integral diagram permutations. The actual matrix/lattice word kernel is now proved abelian, and the
remaining diagram action is soluble. For E6 an integral mod-three
discriminant excludes its diagram flip even in characteristic two.
The actual diagonal-factor argument then proves positive-root Sylow
maximality, soluble normalizers and the good-Sylow endpoint for each
original E6/E7/E8 model in every characteristic. Two-element generation remains separate and unused by T1; the later outer-order continuation is proved below. These modules
belong to the optional CFSG backend. The public T1 endpoint has the seven
published inputs listed above. Eliminating the two stronger generation
premises does not prove their full statements or close the other inputs.

The E6 generation pilot now uses two concrete original matrices and recovers
all parameters on the original root lines U3,U4,U5 for every finite field
of order at least three (`CFSGE6GenerationFirstRootRecovery.lean`). The
proof uses the actual integral root operators, torus characters and
Weyl-word identities. Generated-Lie triangularity, original lattice degrees
and primitive integral entries now recover the actual negative fifth-root
line as well (`CFSGE6GenerationNegativeFifthRecovery.lean`). Full
two-element generation, including the two-element field, remains open and
is no longer required by T1.

The complete alternating-family good-Sylow theorem is proved in
[`CFSGAlternatingGoodSylow`](SymmetricSubgroupAsymptotics/CFSGAlternatingGoodSylow.lean).
It constructs two generating conjugate Sylow two-subgroups in every degree
at least five and proves self-normalization in degree at least six; the
actual degree-five normalizer is handled separately. The original
rank-two twisted-A models also have good Sylow witnesses, proved through
their literal fixed/derived Serre groups in
[`CFSGTwistedA2GoodSylowReduction`](SymmetricSubgroupAsymptotics/CFSGTwistedA2GoodSylowReduction.lean).
Neither statement leaves a model-identification premise. The original G2
models now have a defining-prime good-Sylow witness as well
([`CFSGGTwoGoodSylowReduction`](SymmetricSubgroupAsymptotics/CFSGGTwoGoodSylowReduction.lean)).
Its normalizer proof uses the actual folded D4 matrices and singular-flag
recovery in every characteristic, including two and three.

The full positive Sylow centres of the original E6/E7/E8 models have the
field's cardinality
([`CFSGExceptionalOriginalSylowCenters`](SymmetricSubgroupAsymptotics/CFSGExceptionalOriginalSylowCenters.lean)).
Their projected dominant-root conjugacy families are preserved by every
actual group automorphism, and full unit scaling proves that each proper
subgroup index is at least the field order
([`CFSGExceptionalOriginalIntrinsicRootFamily`](SymmetricSubgroupAsymptotics/CFSGExceptionalOriginalIntrinsicRootFamily.lean),
[`CFSGExceptionalRootDegree`](SymmetricSubgroupAsymptotics/CFSGExceptionalRootDegree.lean)).
The original projective order is at least q^(2N), with N the number of
positive roots, and the strict least-index inequality ell² < |G| is now
proved for all three exceptional families
([`CFSGExceptionalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGExceptionalIndexSquare.lean)).
A common lattice argument gives at most 512 roots and at least ten
positive commuting roots for every root. The actual outer-order continuation
is now proved below.

The original-group automorphism infrastructure now includes inner
alignment of both literal opposite Sylow subgroups
([`CFSGNormTwoCoordinateOriginalPairAlignment`](SymmetricSubgroupAsymptotics/CFSGNormTwoCoordinateOriginalPairAlignment.lean)).
For automorphisms preserving the positive subgroup, its simple axes in
the actual abelianization form an intrinsic family and are permuted
([`CFSGNormTwoCoordinateOriginalAxisPermutation`](SymmetricSubgroupAsymptotics/CFSGNormTwoCoordinateOriginalAxisPermutation.lean)).
For automorphisms preserving both opposite subgroups, full normalizer
intersections recover the literal simple-root groups and a Cartan diagram
permutation
([`CFSGNormTwoCoordinateOriginalSimpleRootAction`](SymmetricSubgroupAsymptotics/CFSGNormTwoCoordinateOriginalSimpleRootAction.lean)).
These statements use actual quotient maps and do not assume that an
arbitrary projective automorphism lifts. Stabilizing the simple-root
lines forces one common field automorphism along the connected diagram
([`CFSGNormTwoCoordinateOriginalCommonField`](SymmetricSubgroupAsymptotics/CFSGNormTwoCoordinateOriginalCommonField.lean)).
Explicit integral Smith witnesses bound the literal Cartan scaling-image
indices by 3, 2, and 1 for E6, E7, and E8 respectively
([`CFSGCartanE6PowerIndex`](SymmetricSubgroupAsymptotics/CFSGCartanE6PowerIndex.lean),
[`CFSGCartanE7PowerIndex`](SymmetricSubgroupAsymptotics/CFSGCartanE7PowerIndex.lean),
[`CFSGCartanE8PowerIndex`](SymmetricSubgroupAsymptotics/CFSGCartanE8PowerIndex.lean)).
Faithful restriction to the signed root parameters and the actual inner
Cartan torus now prove the outer-order bounds
**6|Aut(K)|, 2|Aut(K)|, and |Aut(K)|** on the original E6, E7 and E8 models
([`CFSGExceptionalOriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGExceptionalOriginalOuterBound.lean)).
No automorphism-lifting or group-recognition premise is supplied.
The sufficient internal budget is proved in
[`CFSGExceptionalOuterBudget`](SymmetricSubgroupAsymptotics/CFSGExceptionalOuterBudget.lean):
coefficient six globally, coefficient three below least index 27, and
Out≤24 below30. For E6's small-index case, 36 explicit positive-root
witnesses and the original order lower bound force the two-element field.
All three tags leave the sufficient simple-index residual. This does not
assert the stronger published coefficient-three inequality globally.

For the remaining classical good-Sylow cases, the whole upper unitary
subgroup lies in the original fixed group's derived image, including the
small middle-block cases
([`CFSGTwistedAUnitaryWholeUpperDerived`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryWholeUpperDerived.lean)).
The literal upper subgroup is a defining-characteristic Sylow subgroup
and its normalizer is soluble
([`CFSGTwistedAUnitaryOriginalSylow`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryOriginalSylow.lean)).
Actual opposite-subgroup words give nonzero column pivots, and upper
radicals clear the corresponding isotropic columns
([`CFSGTwistedAUnitaryOppositePivot`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryOppositePivot.lean),
[`CFSGTwistedAUnitaryNaturalColumnClearing`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryNaturalColumnClearing.lean)).
The actual Gaussian factorization now proves generation by the two
literal opposite upper Sylow subgroups in every admissible rank and field
([`CFSGTwistedAUnitaryGoodSylowReduction`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryGoodSylowReduction.lean)).
Its rank-two induction includes the raw two-element-field base without
asserting that this small base is perfect. Original derived-image and
central-quotient transport close the whole classifier twisted-A branch,
with no model-identification premise.
The same literal groups now have the exact upper order
`q^(r*(r+1)/2)`
([`CFSGTwistedAUnitaryUpperCardinality`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryUpperCardinality.lean)).
Disjoint opposite Sylows survive the actual central quotient. The original
projective point stabilizer then proves `ell^2 < |G|` in every rank at least
four
([`CFSGTwistedAUnitaryHigherIndexSquare`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryHigherIndexSquare.lean)).
Rank three is also proved, including q=2
([`CFSGUnitaryRankThreeIndexSquare`](SymmetricSubgroupAsymptotics/CFSGUnitaryRankThreeIndexSquare.lean)).
Its actual first-point orbit lies on a nonzero Hermitian polynomial of
degree q+1. The proved Schwartz--Zippel count, with every unit-scalar fibre
retained, bounds that orbit by q^6; the actual quotient order is strictly
greater than q^12. Rank two is also proved for every classifier-admissible
field
([`CFSGUnitaryRankTwoIndexSquare`](SymmetricSubgroupAsymptotics/CFSGUnitaryRankTwoIndexSquare.lean)).
Its actual point orbit gives `ell*(q-1) <= q^4`; literal upper, opposite and
torus images give `q^6*(q^2-1) <= 3*|G|`. The torus kernel bound is proved
from its unipotent action, without assuming a centre or group-order formula.
[`CFSGUnitaryAdmissibleIndexSquare`](SymmetricSubgroupAsymptotics/CFSGUnitaryAdmissibleIndexSquare.lean)
combines every admissible rank and field. The actual rank-two outer bound
`|Out(G)| <= 6*f` is now proved
([`CFSGTwistedA2OuterOrder`](SymmetricSubgroupAsymptotics/CFSGTwistedA2OuterOrder.lean)).
The full Sylow-pair normalizer intersection is the literal torus; faithful
restriction to the actual radical bounds the pair stabilizer by
`(q^2-1)*2*f`. The proved projective torus kernel costs at most three,
and a single inner-torus cancellation gives the outer bound.
No automorphism-lifting or group-recognition premise is used. The higher-rank
unitary outer-order budget is now also proved. In those ranks the original
automorphism group now acts faithfully on all literal singular point
lines, preserving their full orthogonality relation
([`CFSGTwistedAUnitarySingularPointAction`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitarySingularPointAction.lean)).
The carrier equality is proved by actual vector-clearing words; neither
semilinear reconstruction nor its eventual outer-order count is assumed
by this point-action theorem.

The same original groups satisfy `q^r <= ell` in every admissible rank
([`CFSGTwistedAUnitaryAdmissibleIndexLower`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryAdmissibleIndexLower.lean)).
The proof counts actual Heisenberg orbits and retains arbitrary proper
prime-field central subspaces. Their actual upper centre is the literal
q-element central root line
([`CFSGTwistedAUnitaryUpperCenter`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryUpperCenter.lean)).

The original twisted-D derived image also has a defining-characteristic
Sylow subgroup with soluble normalizer
([`CFSGTwistedDDerivedSylowNormalizer`](SymmetricSubgroupAsymptotics/CFSGTwistedDDerivedSylowNormalizer.lean)).
Its whole natural preimage is literally fixed by the twist
([`CFSGTwistedDDerivedFixed`](SymmetricSubgroupAsymptotics/CFSGTwistedDDerivedFixed.lean)).
Fixed-chain parameters, literal paired-root tori, and the complete
nonzero singular-vector normalization are proved in that same derived image
([`CFSGTwistedDSingularVectorNormalization`](SymmetricSubgroupAsymptotics/CFSGTwistedDSingularVectorNormalization.lean)).
The stronger normalization by literal relative-root words is also proved,
including complete hyperbolic-pair normalization
([`CFSGTwistedDRelativeHyperbolicPairNormalization`](SymmetricSubgroupAsymptotics/CFSGTwistedDRelativeHyperbolicPairNormalization.lean)).
Its companion shear is a proved product of actual root words, including
characteristic two. The normalization now works in every relative rank,
including the rank-two and rank-three recursion bases
([`CFSGTwistedDAllRankHyperbolicPairs`](SymmetricSubgroupAsymptotics/CFSGTwistedDAllRankHyperbolicPairs.lean)).
Actual frame induction leaves a norm-one residual plane
([`CFSGTwistedDFrameReduction`](SymmetricSubgroupAsymptotics/CFSGTwistedDFrameReduction.lean),
[`CFSGTwistedDResidualPlane`](SymmetricSubgroupAsymptotics/CFSGTwistedDResidualPlane.lean)).
The retained residual torus has index at most two. Transport through the
actual central-cocycle preimage is now proved, and the original derived
projective image equals the image of the literal relative-root group
([`CFSGTwistedDRelativeDerivedImage`](SymmetricSubgroupAsymptotics/CFSGTwistedDRelativeDerivedImage.lean)).
Its positive and negative root closures are p-groups and generate that
whole group. The two-p-subgroup theorem therefore supplies two generating
Sylow subgroups, with the previously proved soluble normalizer
([`CFSGTwistedDRelativeGoodSylow`](SymmetricSubgroupAsymptotics/CFSGTwistedDRelativeGoodSylow.lean)).
This closes the twisted-D good-Sylow callback in every admissible rank and
field, including characteristic two. Its least-index square is also
proved on the same original model
([`CFSGTwistedDIndexSquare`](SymmetricSubgroupAsymptotics/CFSGTwistedDIndexSquare.lean)).
Two literal hyperbolic-frame charts give `|R| >= q^(8*r-12)`;
its centre has at most two elements, and the actual fixed-vector orbit
gives `ell <= q^(2*r)`. The strict square inequality follows for every
`r >= 4` and `q >= 2`, without a supplied classical group-order formula.
Its outer-order budget is now proved as well. A literal root star in the
same original quotient gives `q^(r-2) <= ell`
([`CFSGTwistedDIndexStarLower`](SymmetricSubgroupAsymptotics/CFSGTwistedDIndexStarLower.lean)).
The complete bound removes this family from the simple-index callback
([`CFSGTwistedDOuterBudget`](SymmetricSubgroupAsymptotics/CFSGTwistedDOuterBudget.lean)).

[`CFSGSevenTargetsReeGTwoOuter`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsReeGTwoOuter.lean)
threads these completed model cases, including the entire unitary and
twisted-D branches and the original twisted E6 good-Sylow data, all unitary and twisted-D index squares,
their full outer-order budgets, the original G2, triality, F4 and twisted E6 index squares, and the
sufficient E6/E7/E8 simple-index bounds into T1 and AllTargets.
Its parameters are CFSG, five published inputs (general class count, the
two Tracey inputs, labelled transitive count, and ordinary permutation
rank), and **two still-unproved model callbacks**: the remaining good-Sylow
cases and the remaining sufficient simple-index/outer bounds. E6/E7/E8
are absent from both callbacks, and all twisted-A and twisted-D tags are
absent from the good-Sylow callback. The original triality case is now also
absent from that callback, as are the original F4 and twisted E6 cases. All twisted-A and
twisted-D tags are also absent from the simple-index callback. Original
twisted E6, triality and F4 are now absent from that callback as well:
their full outer-order budgets and index squares are proved.
Original G2 is now absent from both callbacks: its least-index square
and full outer-order budget are proved. The actual original ReeG2
good-Sylow theorem is now also threaded through this endpoint: the
good-Sylow callback retains only ReeF4, Tits and the 26 sporadic tags.
ReeG2 is now absent from the simple-index/outer-order callback as well:
its actual outer bound is `|Out| <= 2*(2*m+1)` and its defining field
has size at most every proper permutation degree. Both callbacks retain
only ReeF4, Tits and the 26 sporadic tags, with their respective full payloads.
The current family and endpoint audits use only
`propext`, `Classical.choice`, and `Quot.sound`. This residual
interface is not a theorem from CFSG alone; the canonical public endpoint
continues to have seven published inputs.

The original ReeF4 good-Sylow case is now also proved for every `m > 0`.
A single finite odd torus average matches all coordinates of each actual
positive height layer by a product of genuine commutators. The exact
kernel and terminal filtration then put the full positive subgroup in
the derived subgroup. Opposite generation and the actual full-centre
quotient give the original-model good-Sylow witness.
The newer endpoint
[`CFSGSevenTargetsReeFFourGoodSylow`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsReeFFourGoodSylow.lean)
therefore retains only Tits and the 26 sporadic tags in its good-Sylow
callback. Its separate simple-index/outer callback still retains ReeF4,
Tits and the sporadic tags.
The further endpoint
[`CFSGSevenTargetsReeFFourIndexSquare`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsReeFFourIndexSquare.lean)
also installs the proved original ReeF4 least-index square. Its ReeF4
numerical payload retains only `SufficientOuterOrderBudget`; the Tits
and sporadic payloads remain unchanged.
The further endpoint
[`CFSGSevenTargetsReeFFourOuter`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsReeFFourOuter.lean)
also installs the actual original outer bound `|Out(ReeF4(m))| <= 2*m+1`
and its sufficient numerical budget. Both callbacks now retain only
**Tits and the 26 sporadic tags**. The four published bundles and CFSG
remain explicit parameters, as do those residual model obligations;
this is not a CFSG-only endpoint.

The checked endpoint
[`CFSGSevenTargetsTitsComplete`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsTitsComplete.lean),
installs the actual Tits least-index square, two-Sylow generation and
outer-order budget. **Both model callbacks retain only the 26 sporadic
tags.** The four published bundles and CFSG remain explicit;
this is not a CFSG-only proof.

The checked endpoint
[`CFSGSevenTargetsMathieuTwentyTwoIndexSquare`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsMathieuTwentyTwoIndexSquare.lean),
also supplies the actual M22 least-index square. Its literal 22-point
action and elements with orders divisible by 5, 8 and 11 imply that the
group order is divisible by 440. Simplicity and Sylow arithmetic exclude
order 440, so the order exceeds `22^2`. Its numerical callback therefore
asks only for the outer budget on M22. The 26 sporadic tags and all
other explicit inputs remain; this is a reduction of one payload field,
not a discharge of the whole sporadic callback
([`CFSGMathieuTwentyTwoActualIndexSquare`](SymmetricSubgroupAsymptotics/CFSGMathieuTwentyTwoActualIndexSquare.lean)).

The checked endpoint
[`CFSGSevenTargetsMathieuTwentyTwoGoodSylow`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsMathieuTwentyTwoGoodSylow.lean),
also proves the actual M22 good-Sylow case at the prime 11. Two literal
conjugate words of order dividing 11 recover both original generators,
so suitable conjugate Sylow 11-subgroups generate the group. The exact
order 443520 and transitivity of the same 22-point action imply that
each Sylow 11-subgroup is cyclic and acts without fixed points. Its
generator has two 11-cycles; its permutation centralizer and cyclic
normalizer are soluble. The exact order and transitivity certificates
are ported from Kenta's Apache-2.0 formalization, with source hashes and
attribution recorded in
[`m22-certificates.json`](../provenance/CFSG/m22-certificates.json).
The **good-Sylow callback now retains 25 sporadic tags**. The numerical
callback still retains all 26, with only the outer budget required on
M22. The four published bundles and pinned CFSG remain explicit; this
is not a CFSG-only endpoint. All 21 audited exports use only the
standard Lean axioms, while these theorem parameters remain visible.

The newest checked endpoint,
[`CFSGSevenTargetsMathieuElevenIndexSquare`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsMathieuElevenIndexSquare.lean),
also installs M11's good-Sylow case and least-index square. All five
relations of the pinned presentation are checked on an actual pair in
the original 11-point action. A literal recovery word proves
surjectivity; inherited simplicity proves injectivity. The resulting
equivalence gives exact order 7920, using the separately ported
Apache-2.0 order certificates
([provenance](../provenance/CFSG/m11-certificates.json)).
The same faithful action has an order-four element with two four-cycles.
A Sylow 2-subgroup containing it has Frattini rank at most three; its
automorphism and centralizer divisors force the normalizer order to
divide 144. The internally proved Burnside theorem makes this
normalizer soluble, and the original presentation generators supply
the generating Sylow pair. A proper point stabilizer gives least index
at most 11, hence its square is strictly less than 7920.
The **good-Sylow callback now retains 24 sporadic tags**. The numerical
callback retains 26, with only outer budgets required on M11 and M22.
The four published bundles and CFSG remain explicit. The combined
25-export Good-Sylow audit and nine-export index-square audit use only
the standard Lean axioms; the endpoint is still conditional on its
displayed inputs.

A further optional endpoint,
[`CFSGSevenTargetsTraceyPublished2018Bundle`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsTraceyPublished2018Bundle.lean),
consolidates the separate ordinary-generator parameter into a **stronger,
explicit retention of the same published Tracey 2018 theorem**.
Its bundle retains the old coarse conclusion and the sharper floor bound
only for degrees 4 through 21, where Theorem 1.1(2)'s exceptional degrees
cannot occur. A proved numerical adapter and the original small-degree
bases derive the full McIver--Neumann conclusion from that bundle.
This endpoint has four published parameters, CFSG and two
residual model callbacks; the newer ReeF4 endpoint above uses the same
published bundle and the reduced good-Sylow callback. The additional sharp field is published input;
it is not proved from the old coarse field or from CFSG. Future proofs
must also avoid using the global MN consequence to establish its own
Tracey premise. The canonical endpoint and its seven-input table remain
unchanged.

The bounded ordinary-generator route now proves **every original
nonaffine imprimitive sharp case below degree 22**, or retains an actual
Tits/sporadic factor witness. Simultaneous prime-index capacities pay
prime tops through the same chief trace. An actual least-index-five
coset action recognizes A5 and supplies the extra saving at degree ten;
the four-point top uses the actual half-capacity and exact sharp floor
at degree twenty. Every nonpaired Lie-type factor has proper index at
least 24, excluding it internally from smaller primitive components.
This closes the nonaffine imprimitive branch of the bounded sharp field
([`OriginalNonaffineBoundedSharpCFSGReduction`](SymmetricSubgroupAsymptotics/OriginalNonaffineBoundedSharpCFSGReduction.lean),
[`PrimitiveSocleNonpairDegreeTwentyFour`](SymmetricSubgroupAsymptotics/PrimitiveSocleNonpairDegreeTwentyFour.lean)).
The primitive assembler now covers every original primitive action in
degrees 4 through 21, or retains **an actual affine degree-16 profile or
an actual Tits/sporadic socle factor**. At degree nine, the faithful
complement acts on the four projective points of the ternary plane; its
scalar kernel has order at most two. This gives three complement
generators and one translation. The small nonaffine cases retain the
literal socle quotient and its divisibility by both the outer-group
order and the original permutation quotient order. No primitive
catalogue or additional model callback is assumed. The primitive affine
degree-16 case remains open
([`PrimitiveBoundedSharpCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveBoundedSharpCFSGReduction.lean),
[`PrimitiveAffineNineOrdinaryGenerators`](SymmetricSubgroupAsymptotics/PrimitiveAffineNineOrdinaryGenerators.lean)).
A further degree-16 adapter uses the actual eight-point action of
`GL(4,2)`. It either proves rank at most five, or produces a least failed
primitive sporadic action on at most eight points. The Tits case is
excluded by its checked order lower bound. This is a global failed
action witness, not an asserted subquotient of the original complement;
the sporadic alternative remains to be discharged
([`PrimitiveAffineSixteenEightPointSharpReduction`](SymmetricSubgroupAsymptotics/PrimitiveAffineSixteenEightPointSharpReduction.lean)).
The imprimitive affine sharp assembler now covers **every original
minimal-block affine component below total degree 22**, or retains
**total degree 16 or a genuine global primitive sporadic counterexample
on at most ten points**. The prime-power fibre menu is proved internally;
local degrees 2, 3, 4, 5, 7 and 9 use the same chief trace and actual
quotient. At the six-point ternary top, the joint induced capacity pays
the defining-prime layer without separately maximizing its two parts.
The four-by-four degree-16 configuration is now proved: its actual
odd-kernel partition has one, two or four classes. Shared translation
heads and the same odd/sign layers give six generators in every case,
with no induction, CFSG or published generator premise. The
8/2 case is now also proved, using its shared translation head and the
graph-or-axis dichotomy for the two literal complement coordinates.
The last binary 2/8 case now has a complete structural reduction too:
nonelementary top Sylow subgroups pay the quarter module bound; an
elementary top Sylow gives three top generators in the affine, paired
primitive and both imprimitive branches. The resulting facade retains
only **an actual primitive sporadic eight-point top of rank greater than
three**, or **a separate global failed-half sporadic action on at most
ten points**. The former is the same original top and need not fail the
half-degree bound. Thus no unexplained affine degree-16 shape remains,
but these sporadic alternatives are still open
([`OriginalAffineBoundedSharpSporadicReduction`](SymmetricSubgroupAsymptotics/OriginalAffineBoundedSharpSporadicReduction.lean)).
A shared prime-product argument now excludes nine pinned sporadic tags
from faithful actions on at most ten points. A selected actual
Mathieu22 order-four witness excludes that model from the
**elementary-Sylow top**. Its literal word `a^3*b^2` now has a checked
point orbit of prime length eleven, so eleven divides that same
model's order. This also excludes M22 from the separate global
failed-half action on at most ten points. The actual Co2 relators exclude Co2 from the
same top: elementary Sylow 2-subgroups force a commuting cyclic orbit
of its involution generator, making the whole model soluble. A checked actual Co3 word has order
divisible by 14. Perfectness forces every faithful image of its simple
factor into the alternating group; an even permutation with that order
divisor occupies at least 11 points. Co3 is therefore excluded from
both small-action alternatives, using the same literal word and fixed
vector trace. This leaves 14 possible tags in the actual-top obstruction
and 15 in the global small-action obstruction
([`OriginalAffineBoundedSharpCoTwoTopRefinement`](SymmetricSubgroupAsymptotics/OriginalAffineBoundedSharpCoTwoTopRefinement.lean),
[`CFSGCoThreeSelectedWordOrder`](SymmetricSubgroupAsymptotics/CFSGCoThreeSelectedWordOrder.lean),
[`PrimitiveSocleCoThreeSmallActionExclusion`](SymmetricSubgroupAsymptotics/PrimitiveSocleCoThreeSmallActionExclusion.lean),
[`PrimitiveSocleMathieuTwentyTwoSmallActionExclusion`](SymmetricSubgroupAsymptotics/PrimitiveSocleMathieuTwentyTwoSmallActionExclusion.lean)).
All actual transitive 2-groups of degree sixteen separately satisfy the
six-generator bound
([`BinarySixteenTwoGroupSharpStep`](SymmetricSubgroupAsymptotics/BinarySixteenTwoGroupSharpStep.lean)). The small sporadic witness is global and is not asserted
to be a subquotient of the original action. No induction or published
generator input is assumed by this bounded affine reduction
([`OriginalAffineBoundedSharpCFSGReduction`](SymmetricSubgroupAsymptotics/OriginalAffineBoundedSharpCFSGReduction.lean)).

For binary translations of order eight, every subgroup of the actual
faithful semidirect product now has at most **24 conjugacy classes**.
The proper translation kernel is retained as a prime-field submodule
of the same projected group. For a full translation kernel, the exact
dual commuting-pair identity gives at most 14 classes in the irreducible
case; the reducible case gives 24. This uses no action census, splitting
of a proper-kernel subgroup, or subgroup-class monotonicity. Transferring
the bound through the original affine profile gives
`k(H)^3 <= 5^(8-2)`, paying the original two/three-block actions
([`ActualAffineEightSmallTopClassGap`](SymmetricSubgroupAsymptotics/ActualAffineEightSmallTopClassGap.lean)).
The native minimal-block installer needs just **one actual base affine
profile**, for fibre degree eight or nine. Literal component conjugation
embeds every coordinate subgroup into that base component, where the
all-subgroup bound applies. No profile family or supplied capacity remains
([`OriginalMinimalBlockAffineSmallTopClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockAffineSmallTopClassBound.lean)).

For class counts, every subgroup of a faithful semidirect product with
an abelian translation group of order nine now has at most **39 classes**.
The literal fixed subgroup of each nonidentity complement element is
proper and has at most three elements. Keeping this together with the
actual projected complement gives `k(H)^3 <= 5^(9-2)`. The original
block adapter therefore pays affine degree-nine components under two
or three blocks, without a splitting or class-count hypothesis
([`ActualAffineNineSmallTopClassGap`](SymmetricSubgroupAsymptotics/ActualAffineNineSmallTopClassGap.lean)).

The affine class-count route is now uniform: for every actual primitive
affine action of degree `a >= 5` and every subgroup `H` of that same group,
`k(H)^3 <= 5^(a-2)` is proved. Prime, square, cube and large-degree bounds
share one argument; the binary linear centralizer charts handle the
remaining degrees 8, 16 and 32. The degree-16 and degree-32 subgroup
bounds are respectively 1544 and 702480 classes. No affine catalogue,
Garonzi–Maróti premise or subgroup-class monotonicity is used
([`PrimitiveAffineAllSubgroupsClassGap`](SymmetricSubgroupAsymptotics/PrimitiveAffineAllSubgroupsClassGap.lean)).
The native installer transfers this bound from one actual affine base
profile through **every original block-top size**. Tops of size two or
three use the stronger gap directly; larger tops use only strict-smaller
general permutation-degree induction. Together with the existing
four-point installer, all affine component degrees at least four are
therefore paid. Small fibres 2 and 3 and the nonaffine class-count
frontier remain separate
([`OriginalMinimalBlockAffineAllTopClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockAffineAllTopClassBound.lean)).
Every primitive affine **top** of degree at least five above binary or
ternary fibres is now paid. The infinite ranges and the exact
prime-power exhaustion reduce to degrees 8, 9, 16, 25, 27, 32 and 64,
which share the same native proof. The degree-16 and
degree-32 parabolic arguments improve their all-subgroup class budgets
to 772 and 351240. The binary proof retains the actual unsigned motion
reserve `(B+1)*2^(n-2)`; the ternary proof uses `3^n*B`. Degree 9 reuses
its 39-class theorem, degree 25 needs only its actual prime-log order
bound, degree 27 uses the retained line/plane parabolic budget 12247,
and degree 64 uses the uniform sparse centralizer bound
([`PrimitiveTopSmallFibreClassBudget`](SymmetricSubgroupAsymptotics/PrimitiveTopSmallFibreClassBudget.lean),
[`PrimitiveAffineBinaryTopSmallFibreClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineBinaryTopSmallFibreClassBound.lean),
[`PrimitiveAffineNineTopSmallFibreClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineNineTopSmallFibreClassBound.lean),
[`PrimitiveAffineTwentyFiveTopSmallFibreClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineTwentyFiveTopSmallFibreClassBound.lean),
[`PrimitiveAffineTernaryTopSmallFibreClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineTernaryTopSmallFibreClassBound.lean),
[`PrimitiveAffineSixtyFourTopSmallFibreClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineSixtyFourTopSmallFibreClassBound.lean)).
The original top may now be imprimitive in all of these degrees. A faithful
regular-normal action on at least five points contains no transposition:
its commutator with a regular translation moves at most four points,
so regularity makes that commutator trivial. Thus the same unsigned
reserve applies without primitivity. If a regular normal `p`-group `N`
has order `p^d` and Frattini quotient rank `r`, its actual affine map
on that quotient has kernel at most `p^((d-r)*(r+1))`. Each original
subgroup keeps its actual image in the elementary holomorph, so the
proved elementary budgets cover nonabelian translation groups too.
In degree 8, rank 3 recovers the 24-class bound. Lower rank supplies
a characteristic subgroup of order 2, whose actual orbits coarsen
ternary fibres to six-point fibres over four blocks. Strict-smaller
general permutation induction pays this source. Thus every original
binary/ternary action with a regular normal prime-group top of degree
at least five is paid. This last induction statement concerns the whole
original action; it does not assert that induction for every subnormal subgroup
([`RegularNormalActionNoSwap`](SymmetricSubgroupAsymptotics/RegularNormalActionNoSwap.lean),
[`FrattiniAffineSmallClassBound`](SymmetricSubgroupAsymptotics/FrattiniAffineSmallClassBound.lean),
[`RegularAffineEightTernaryCoarsening`](SymmetricSubgroupAsymptotics/RegularAffineEightTernaryCoarsening.lean),
[`OriginalMinimalBlockRegularAffineTopCompleteClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockRegularAffineTopCompleteClassBound.lean)).
The global reduction now also discharges every original two- or
three-block source, and every four-block source with binary fibres.
The latter keeps the actual weighted fixed-kernel sum and proves at
most 42 classes. These are bounds on the original transitive source;
they do not assert transitivity for arbitrary subnormal subgroups
([`OriginalSmallTopClassCubeBound`](SymmetricSubgroupAsymptotics/OriginalSmallTopClassCubeBound.lean),
[`OriginalBinaryFourTopClassCubeBound`](SymmetricSubgroupAsymptotics/OriginalBinaryFourTopClassCubeBound.lean)).
Four ternary blocks are now paid for **every transitive top**. The actual
signed-coordinate action retains its translation subspace `W` and sign
kernel `E`. For nonzero proper `W`, self-dual orthogonal coordinates give
the coupled bound `|W|*|E| <= 54`, hence at most 270 classes. For full `W`,
the exact dual stabilizer weights give 330 with full symmetric top, and
at most 360 with binary top. A sign kernel of size above four doubles
the pair-support index, keeping that last weighted sum below the same
capacity. The actual alternating-top case has at most 324 classes.
Since `360^3 <= 5^11`, the original degree-12 source is paid without a
primitive-top premise. The global small-fibre residual now has at least
five blocks and excludes all regular normal prime-group tops
([`OriginalTernaryFourTopClassCubeBound`](SymmetricSubgroupAsymptotics/OriginalTernaryFourTopClassCubeBound.lean),
[`TernaryFourTransitiveProperKernelCapacity`](SymmetricSubgroupAsymptotics/TernaryFourTransitiveProperKernelCapacity.lean),
[`TernaryFourBinaryTopFixedClassWeight`](SymmetricSubgroupAsymptotics/TernaryFourBinaryTopFixedClassWeight.lean)).
This is now threaded into the actual global least-counterexample
argument. Its bounded imprimitive alternatives retain either a literal
fibre of size 2 or 3 at total degree at most 36855, or a literal
**nonaffine, nonsimple** component of degree 5 through 4095 under two
or three blocks, at total degree at most 12285. The other alternative retains
actual Tits/sporadic data in the original component or top. No bounded
class-count callback is introduced
([`GaronziMarotiGlobalNonaffineShapeCounterexample`](SymmetricSubgroupAsymptotics/GaronziMarotiGlobalNonaffineShapeCounterexample.lean)).

A separate generic proper-subnormal argument pays **every actual
simple component** of degree at least four. A deficient correlated
kernel saves one proper-subnormal power; a saturated kernel is the
actual full wreath product and uses its proved two/three-block class
count. Proper subnormal subgroups of a simple component are trivial,
so this needs no extra class-capacity premise. The native theorem uses
only strict-smaller general permutation-degree induction and is
threaded into the existing global frontier above
([`OriginalMinimalBlockSimpleComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockSimpleComponentClassBound.lean)).

The same original induction now pays every component isomorphic to
`S_m`, `m >= 5`, in any faithful representation. A generic proper
subnormal subgroup bound retains its intersection with the normal
simple `A_m` and the actual quotient. Exact small partition counts
and a three-step partition recurrence prove `k(A_m)^3 <= 5^(m-2)`;
the actual representation degree is at least `m`. This excludes all
such symmetric components in the existing global frontier, without
an action census or subgroup-class monotonicity
([`OriginalMinimalBlockSymmetricComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockSymmetricComponentClassBound.lean)).

The same strengthened frontier also excludes every original `G2(q)`
simple-factor profile. A uniform proper-index product bound transfers
to the extra class exponent for every socle multiplicity: one factor
uses its proper subnormal intersection, several factors retain the
full factorial reserve, and the power-degree form uses the actual
`q^12` lower bound and a common logarithmic order reserve. Both original
degree forms and the same actual subgroup remain in the proof
([`OriginalMinimalBlockGTwoComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockGTwoComponentClassBound.lean)).
The same all-factor reserve now also handles the complete E6/E7/E8
component family together. Existing actual proper-index lower bounds
`2048` and order-times-outer bounds of index to power `66` supply its
entire numerical packet. The same subgroup, full factorial and both
original degree forms are retained
([`OriginalMinimalBlockExceptionalEComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockExceptionalEComponentClassBound.lean)).
The sharper actual subnormal class product now supplies a common
square-capacity reserve for every admissible type-A simple socle.
This covers all ranks and fields, every socle multiplicity and both
original degree forms. The former PSL2 fields `4,5,9` are discharged
using existing exact small-group metadata and the same actual
minimum-degree quotient argument. PSL3 and higher ranks reuse their
proved class-equation, cyclic-code and order packets
([`OriginalMinimalBlockTypeAComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockTypeAComponentClassBound.lean)).
The same native transfer is now proved for every admissible unitary
simple socle, across all ranks and fields. Its existing isometry-order
tail and coupled small-field class-equation packets supply the common
proper capacity; no numerical gap is an extra endpoint hypothesis
([`OriginalMinimalBlockUnitaryComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockUnitaryComponentClassBound.lean)).
Every admissible symplectic simple socle is now covered as well, at
every rank, field and multiplicity, in both original degree forms.
The proved order packets and small-field primary and point-stabilizer
packets supply the extra proper-subnormal exponent. The same actual
subgroup is retained, and the whole type-C profile is excluded from
the existing global frontier
([`OriginalMinimalBlockSymplecticComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockSymplecticComponentClassBound.lean)).
The complete type-B family has the same native transfer. Odd fields
reuse the proved point-radical order capacity. In characteristic two,
the actual type-B model is transported to the literal symplectic group;
its checked proper capacities apply with simplicity inherited from
that same model. No independent type-C simplicity premise is used
([`OriginalMinimalBlockTypeBComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockTypeBComponentClassBound.lean)).
Split and twisted orthogonal type D now share one native installer.
Their existing point-radical packets cover all ranks and fields except
binary rank four, where each family's own proved class, outer and
proper-index bounds give the required square capacity. Every factor
count and both actual degree forms are covered, without identifying
different models or assuming a numerical endpoint
([`OriginalMinimalBlockOrthogonalDComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockOrthogonalDComponentClassBound.lean)).
One shared installer now also covers all remaining non-Tits exceptional
families: F4, twisted E6, triality, Suzuki, small Ree and positive-parameter
Ree F4. Their proved order, outer and proper-index packets supply the
same actual proper-subnormal reserve
([`OriginalMinimalBlockExceptionalComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockExceptionalComponentClassBound.lean)).
Exhausting the literal CFSG index now proves that the bounded nonaffine
component's surviving simple factor is Tits or sporadic, retaining
its actual equivalence, factor count and degree form. The separate
small-fibre branch and these finite-model class bounds remain open
([`OriginalMinimalBlockBoundedFiniteFactor`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockBoundedFiniteFactor.lean)).
A separate shared estimate now handles actual binary and ternary fibres
above a nonaffine top. It retains every subnormal source subgroup, all
socle factors and the full factorial. A component class packet pays
every multifactor and distant one-factor case; otherwise it returns the
same proper subgroup at an index between the actual least index and
twice that index plus two. The whole G2 family supplies this packet
([`SmallFibreNonaffineClassPacketResidual`](SymmetricSubgroupAsymptotics/SmallFibreNonaffineClassPacketResidual.lean),
[`SmallFibreGTwoClassPacketResidual`](SymmetricSubgroupAsymptotics/SmallFibreGTwoClassPacketResidual.lean)).
For E6, E7, E8 and twisted E6, the stronger shared inequality
`25*t^198 <= 3^t` for `t >= 2048` absorbs the binary or ternary kernel
at each actual proper index. Their proved order-at-index packets therefore
close **all** these small-fibre cases, including the one-factor short
interval. No fixed field-independent component-order bound is assumed
([`LargeIndexPowerThreeEnvelopeNumerics`](SymmetricSubgroupAsymptotics/LargeIndexPowerThreeEnvelopeNumerics.lean),
[`SmallFibreExceptionalLargeIndexClassGap`](SymmetricSubgroupAsymptotics/SmallFibreExceptionalLargeIndexClassGap.lean)).
The same scaled method now closes the whole small-Ree, F4, triality and Suzuki
families. A generic nonabelian-simple class-equation argument proves
`2*k(S) <= |S|`, supplying the binary triality saving without an order
or class-table assumption
([`SmallFibreReeGTwoClassGap`](SymmetricSubgroupAsymptotics/SmallFibreReeGTwoClassGap.lean),
[`NonabelianSimpleClassOrderHalf`](SymmetricSubgroupAsymptotics/NonabelianSimpleClassOrderHalf.lean),
[`SmallFibreFFourTrialityClassGap`](SymmetricSubgroupAsymptotics/SmallFibreFFourTrialityClassGap.lean),
[`SmallFibreSuzukiClassGap`](SymmetricSubgroupAsymptotics/SmallFibreSuzukiClassGap.lean)).
The whole G2 family is now included as well. Deleting zero from the
retained dual annihilator strengthens the same scalar-word index bound
to `|K|^(m+1)`, without asserting larger-field linearity of the stabilizer.
On the original G2 middle source this gives `q^3` in characteristic
other than three. In particular the actual field-four index is at least
64; its class equation pays the last scaled packet
([`PuncturedAnnihilatorScalarWordIndex`](SymmetricSubgroupAsymptotics/PuncturedAnnihilatorScalarWordIndex.lean),
[`CFSGGTwoPuncturedScalarClassPacket`](SymmetricSubgroupAsymptotics/CFSGGTwoPuncturedScalarClassPacket.lean),
[`SmallFibreGTwoCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreGTwoCompleteClassGap.lean)).
The same punctured argument bounds a proper scalar-invariant subspace
by the index of its preserving subgroup. Applied to the literal Suzuki
stabilizer and its quadratic vector-image bound, it improves the index
from `(q-1)*2^(m+1)` to `q*2^(m+1)`
([`ScalarInvariantSubspaceCardIndex`](SymmetricSubgroupAsymptotics/ScalarInvariantSubspaceCardIndex.lean),
[`CFSGReeFFourPuncturedMiddleSuzukiIndex`](SymmetricSubgroupAsymptotics/CFSGReeFFourPuncturedMiddleSuzukiIndex.lean)).
The positive-parameter ReeF4 small-fibre branch is therefore closed for
`m >= 2` by this actual index and a scaled order envelope. Its field-32
seed has index at least 256. Only `m=1` remains in that positive family;
Tits is separate
([`SmallFibreReeFFourLargeParameterGap`](SymmetricSubgroupAsymptotics/SmallFibreReeFFourLargeParameterGap.lean)).
At `m=1`, the original small-fibre branch is now closed as well. Its
order argument first reduces to one socle factor and the same proper
subgroup of index exactly 109. The actual
sixteen Bruhat cells form a bijection, giving the fixed-group order and
proving that 11 does not divide the original model's order. The proved
Jordan multiple-primitivity theorem would force 110 to divide that
order at any index strictly between 109 and 218. The scaled class
packet pays all larger indices. The whole ternary branch is also closed:
the actual simple-group half-class saving gives component budget
`3*2^77`, whose scalar seed pays every degree from 109. The final binary
case is excluded by an actual Sylow orbit congruence: its fixed-point
count divides 49, and every nonfixed orbit has size divisible by 8.
Degree 109 is incongruent modulo 8 to every divisor of 49. Consequently
every proper subgroup has index at least 218, and both fibre sizes and
all socle multiplicities are paid. No action catalogue or group-order
premise is assumed
([`PrimitivePrimeCycleCardinalityBand`](SymmetricSubgroupAsymptotics/PrimitivePrimeCycleCardinalityBand.lean),
[`CFSGReeFFourSixteenCellCardinality`](SymmetricSubgroupAsymptotics/CFSGReeFFourSixteenCellCardinality.lean),
[`SmallFibreReeFFourFieldEightSingleIndexResidual`](SymmetricSubgroupAsymptotics/SmallFibreReeFFourFieldEightSingleIndexResidual.lean),
[`SmallFibreReeFFourFieldEightTernaryClassGap`](SymmetricSubgroupAsymptotics/SmallFibreReeFFourFieldEightTernaryClassGap.lean),
[`SylowIntersectionDegreeObstruction`](SymmetricSubgroupAsymptotics/SylowIntersectionDegreeObstruction.lean),
[`CFSGReeFFourFieldEightSylowIndexObstruction`](SymmetricSubgroupAsymptotics/CFSGReeFFourFieldEightSylowIndexObstruction.lean),
[`SmallFibreReeFFourFieldEightCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreReeFFourFieldEightCompleteClassGap.lean)).
The global profile and both original-action GM consumers include this
closure. Any selected nonaffine simple model outside the paid global
profiles is now literally Tits or sporadic
([`SmallFibreNonaffineFiniteModelNormalization`](SymmetricSubgroupAsymptotics/SmallFibreNonaffineFiniteModelNormalization.lean)).
The class equation and the actual point-radical indices now close the
whole split-D and twisted-D families. The last twisted binary rank-four
head uses the punctured annihilator on the same arbitrary prime-field
kernel: its index improves from 24 to 32, and the existing class/outer
ceilings 3072 and 8 then pay the scaled packet
([`SmallFibreOrthogonalDClassGap`](SymmetricSubgroupAsymptotics/SmallFibreOrthogonalDClassGap.lean),
[`SmallFibreTwistedDCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTwistedDCompleteClassGap.lean)).
The whole odd-characteristic B and C families are closed as well. The
small B3(3) head uses the same punctured argument to improve its index
from 72 to 81; C2 uses a constructed actual SL2 quotient action, not an
assumed transitivity bound
([`SmallFibreOddOrthogonalBClassGap`](SymmetricSubgroupAsymptotics/SmallFibreOddOrthogonalBClassGap.lean),
[`SmallFibreOddSymplecticCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreOddSymplecticCompleteClassGap.lean)).
In characteristic two, the higher-rank Siegel packet and the rank-two
tail close B and C as well. At rank two over the four-element field, puncturing the retained
annihilator improves the actual index to at least 24; no larger-field
linearity is assumed
([`SmallFibreCharTwoClassicalClassGap`](SymmetricSubgroupAsymptotics/SmallFibreCharTwoClassicalClassGap.lean),
[`SmallFibreBinaryRankTwoClassGap`](SymmetricSubgroupAsymptotics/SmallFibreBinaryRankTwoClassGap.lean)).
The last binary rank-three case uses a faithful 27-element Heisenberg
representation over F4, its actual Fourier/phase normalizers, and the
trace-Hermitian embedding into the binary symplectic group. A generic
compatible-normalizer argument gives proper index at least 27 without
assuming that the normalizer splits. The existing class and outer
bounds then pay the packet. Thus **all admissible B and C parameters**
are closed in this small-fibre branch
([`TernaryHeisenbergCompatibleNormalizerIndex`](SymmetricSubgroupAsymptotics/TernaryHeisenbergCompatibleNormalizerIndex.lean),
[`CFSGSymplecticPauliPrimeIndex`](SymmetricSubgroupAsymptotics/CFSGSymplecticPauliPrimeIndex.lean),
[`SmallFibreCharTwoCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreCharTwoCompleteClassGap.lean)).
A shared exponential envelope and the rank-two class formula close the
higher-A ranges, including every rank-two field from five. A shared
coefficient-word code bounds `k(GL_n(q))` by `(q-1)*(2q-1)^(n-1)`;
the actual special-linear class fibres cost `gcd(q-1,n)`, and classes
then descend through the full projective quotient. This closes all
binary ranks from four and three more small nonbinary parameters.
For rank two over the three-element field, the prime divisor 13
survives the determinant and centre quotients and gives proper index
at least 13. Over the four-element field, the refined normal-key cover
gives `k(SL_3(4)) <= 28`. Multiplication by an actual central scalar of
order three fixes at most one class: its trace and inverse trace must
both vanish, placing it in the same determinant-surjective origin fibre.
The proved central-quotient Burnside formula then gives `k(PSL_3(4)) <= 10`.
Together with outer order at most 12 and proper index at least 16,
the tighter 24-reserve packet closes this case as well. Rank two over
the two-element field is also complete. Its six-class bound leaves only
the original binary seven- and eight-block actions. Their actual top
has order at most 336. The one-factor full transitive socle makes that
top quasiprimitive, so a transposition would force the full symmetric
group and contradict its order. The actual binary kernel embeds
equivariantly into the unsigned permutation module, including for a
nonsplit extension and for each actual subnormal top image. Counting
the identity contribution before taking maxima gives
`k(H) <= 13*2^(n-2)`, which pays both degrees. Thus ten of the eleven
former higher-A heads are closed; the exact remaining parameter is
**`(3,2)`**.
These count parameters in this
small-fibre branch, not action rows or all remaining global obligations
([`SmallFibreTypeAScaledClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTypeAScaledClassGap.lean),
[`FiniteFieldProjectiveLinearClassBound`](SymmetricSubgroupAsymptotics/FiniteFieldProjectiveLinearClassBound.lean),
[`SmallFibreTypeACoefficientClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTypeACoefficientClassGap.lean),
[`SmallFibreTypeARankTwoThreeClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTypeARankTwoThreeClassGap.lean),
[`CentralOrderThreeConjugacyClasses`](SymmetricSubgroupAsymptotics/CentralOrderThreeConjugacyClasses.lean),
[`ProjectiveSLThreeQuaternaryClassBound`](SymmetricSubgroupAsymptotics/ProjectiveSLThreeQuaternaryClassBound.lean),
[`SmallFibreTypeARankTwoQuaternaryClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTypeARankTwoQuaternaryClassGap.lean),
[`BinaryBlockUnsignedGeneralClassReserve`](SymmetricSubgroupAsymptotics/BinaryBlockUnsignedGeneralClassReserve.lean),
[`SmallFibreTypeARankTwoBinaryCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTypeARankTwoBinaryCompleteClassGap.lean),
[`SmallFibreClassicalBoundedHeadParameters`](SymmetricSubgroupAsymptotics/SmallFibreClassicalBoundedHeadParameters.lean)).
Within the remaining binary rank-three parameter, the original
general-linear class bound is now refined to 14. Each actual positive
primary factor has one of seven nonzero-constant irreducible coefficient
words; the weighted multiset has total degree four and exactly 14
possible codes. Equality of codes gives an actual intertwiner, and the
literal special-linear and full projective quotient maps preserve the
class bound. No 14-class premise or group-element census is used
([`BinaryFourPrimaryClassCode`](SymmetricSubgroupAsymptotics/BinaryFourPrimaryClassCode.lean),
[`CFSGTypeARankThreeBinaryClassPacket`](SymmetricSubgroupAsymptotics/CFSGTypeARankThreeBinaryClassPacket.lean)).
The single-factor degree-eight binary action is already closed. Its actual socle
has order 20160, so the actual permutation top has index at most two
in the symmetric group on eight points. The proved half-factorial
recognition identifies that same top as alternating or symmetric,
and the native binary degree-eight bound applies. This requires no
constructed `PSL_4(2) ≃ A_8` isomorphism or relabelled action
([`PrimitivePermutationHalfOrderRecognition`](SymmetricSubgroupAsymptotics/PrimitivePermutationHalfOrderRecognition.lean),
[`OriginalBinaryTypeARankThreeEightClassGap`](SymmetricSubgroupAsymptotics/OriginalBinaryTypeARankThreeEightClassGap.lean)).
The same unsigned reserve now pays every other binary action over this
model; the ordinary 28-class envelope pays ternary actions from nine
blocks. The sole stronger local seam is the actual one-factor ternary
eight-block action. The global GM induction needs exponent `|Ω|-1`,
and `(3^8*28)^3 <= 5^23` pays this action directly. A separate global
profile installs that exact margin, retaining the stronger local API
without asserting its missing margin. Thus **all higher-A parameters**
are closed in the global small-fibre GM branch, including every socle
factor and both degree forms. The global consumer no longer retains
`(3,2)` as an obstruction
([`SmallFibreTypeARankThreeBinaryOrdinaryClassGap`](SymmetricSubgroupAsymptotics/SmallFibreTypeARankThreeBinaryOrdinaryClassGap.lean),
[`SmallFibreKnownModelGlobalClassGap`](SymmetricSubgroupAsymptotics/SmallFibreKnownModelGlobalClassGap.lean)).
The **whole admissible unitary family** is now closed. The existing
infinite ranges leave ten small parameter pairs, all paid by a shared
Hermitian frame count and a determinant saving. Gram--Schmidt is proved
over the actual quadratic field, with a nonzero scalar normalizing the
original signed form. Scaling one basis vector proves determinant
surjectivity for the same original isometry group. This gives
`(q+1)*|TwistedA r q| <= 3*q^((r+1)^2)` without an order formula or a
class census. Actual coupled indices and the class equation then pay all
ten scalar capacities. At binary rank three, the faithful Pauli
normalizer embeds into the original unitary model and gives index 27;
the proved coprime quotient kernel gives outer order at most two.
The resulting theorem retains the original source, its actual subnormal
subgroup, every socle factor and both primitive degree forms
([`CFSGUnitaryFrameOrderUpper`](SymmetricSubgroupAsymptotics/CFSGUnitaryFrameOrderUpper.lean),
[`CFSGUnitaryBinaryRankThreePauliIndex`](SymmetricSubgroupAsymptotics/CFSGUnitaryBinaryRankThreePauliIndex.lean),
[`CFSGUnitaryCompleteScaledClassPacket`](SymmetricSubgroupAsymptotics/CFSGUnitaryCompleteScaledClassPacket.lean),
[`SmallFibreUnitaryCompleteClassGap`](SymmetricSubgroupAsymptotics/SmallFibreUnitaryCompleteClassGap.lean)).
For the separate PSL2 family, the characteristic-prime index bound
closes every prime field from 11. The sharper binary outer bound and a
power induction close every binary field from 16, and the same class
packet pays the odd powers 27 and 49. At order 25, the same actual fixed
counts in Burnside's formula and the modulo-five orbit congruence give
proper index at least 15; the original class and outer bounds then pay
the packet. The field-seven model also closes: its actual order 168,
outer bound two and six-class bound feed the same original binary
seven/eight reserve, without an exceptional isomorphism. Together with
the existing tail, this leaves exactly four
field parameters `{4,5,8,9}` outside the stronger local profiles. Their finite
prime-power complement is checked in Lean; no action census is used
([`CFSGPSLTwoCharacteristicIndex`](SymmetricSubgroupAsymptotics/CFSGPSLTwoCharacteristicIndex.lean),
[`SmallFibrePSLTwoImprovedClassGap`](SymmetricSubgroupAsymptotics/SmallFibrePSLTwoImprovedClassGap.lean),
[`CFSGPSLTwoTwentyFiveIndex`](SymmetricSubgroupAsymptotics/CFSGPSLTwoTwentyFiveIndex.lean),
[`SmallFibrePSLTwoTwentyFiveClassGap`](SymmetricSubgroupAsymptotics/SmallFibrePSLTwoTwentyFiveClassGap.lean),
[`CFSGPSLTwoSevenClassGap`](SymmetricSubgroupAsymptotics/CFSGPSLTwoSevenClassGap.lean),
[`CFSGPSLTwoSmallFieldParameters`](SymmetricSubgroupAsymptotics/CFSGPSLTwoSmallFieldParameters.lean)).
At field eight, scalar determinants are all squares, so each actual
general-linear class contains at most one special-linear class. The
trace fibres and the single scalar class give `k(SL_2(q)) <= q+1` in
characteristic two. The actual field-eight model therefore has at most
nine classes and outer order at most three. The unsigned reserve pays
binary actions from eight blocks, and the ternary eight-block action
pays the exact global `|Ω|-1` margin. Thus the global profile retains
only the final small fields `{4,5,9}`, handled next, with no assumed
index-nine exclusion
([`SLTwoCharacteristicTwoClassBound`](SymmetricSubgroupAsymptotics/SLTwoCharacteristicTwoClassBound.lean),
[`CFSGPSLTwoEightClassGap`](SymmetricSubgroupAsymptotics/CFSGPSLTwoEightClassGap.lean),
[`SmallFibreKnownModelGlobalClassGap`](SymmetricSubgroupAsymptotics/SmallFibreKnownModelGlobalClassGap.lean)).
Those three fields are now closed as well. One shared actual natural
degree-five/six template counts binary wreath classes by the genuine
square bound and ternary classes by the coordinate capacity. The
field-four/five models use the proved literal A5 equivalences; the
field-nine model has actual socle order 360, so its six-point top is
alternating or symmetric on those same points. The other degrees use
the unsigned reserve or ternary capacity, with all socle factors and
both degree forms retained. Consequently **every admissible PSL2
parameter is closed at the global GM margin**. Its global remaining
field set is empty; the older stronger local inventory is kept separate
([`NaturalFiveSixSmallFibreOrdinaryClassBound`](SymmetricSubgroupAsymptotics/NaturalFiveSixSmallFibreOrdinaryClassBound.lean),
[`SmallFibrePSLTwoAlternatingFiveOrdinaryClassGap`](SymmetricSubgroupAsymptotics/SmallFibrePSLTwoAlternatingFiveOrdinaryClassGap.lean),
[`CFSGPSLTwoNineOrdinaryClassGap`](SymmetricSubgroupAsymptotics/CFSGPSLTwoNineOrdinaryClassGap.lean)).
A further uniform installer handles every actual top subnormal in the
full symmetric group on at least five original blocks, for binary and
ternary fibres. The binary proof combines the existing paired class
bound with the small degrees five through seven. For ternary fibres,
`3^n*fib(n+1)` pays the ordinary margin from eight, since
`3*fib(n+2) <= 5*fib(n+1)`; the three smaller degrees use actual
partition counts. Thus literal natural alternating/symmetric tops are
also excluded internally
([`OriginalNaturalSymmetricTopOrdinaryClassBound`](SymmetricSubgroupAsymptotics/OriginalNaturalSymmetricTopOrdinaryClassBound.lean)).
Abstract alternating factors are now closed at **every original degree**,
including nonnatural short-index actions. The finite restricted-partition
recurrence proves `p(m)*5^m <= 64*7^m`: its finite Euler product at `5/7`
is at least `1/64`. Local integer recurrence certificates cover masses
7 through 99, and a symbolic induction handles the tail from 100.
The actual nonsplit binary reserve and ternary coordinates then pay
every degree above the natural one. Degree six uses the same literal
even/split partition fibres, giving seven classes and outer budget four;
degree five was already covered. No small-index subgroup classification,
action census, or new numerical premise is used
([`PartitionGeometricCoefficientBound`](SymmetricSubgroupAsymptotics/PartitionGeometricCoefficientBound.lean),
[`PartitionAllDegreeSmallFibreCapacity`](SymmetricSubgroupAsymptotics/PartitionAllDegreeSmallFibreCapacity.lean),
[`SmallFibreAlternatingSixOrdinaryClassGap`](SymmetricSubgroupAsymptotics/SmallFibreAlternatingSixOrdinaryClassGap.lean),
[`SmallFibreAlternatingOrdinaryClassGap`](SymmetricSubgroupAsymptotics/SmallFibreAlternatingOrdinaryClassGap.lean)).
The existing global class-count counterexample theorem now excludes
these **actual top profiles** internally; it takes no new bounded-head
estimate as a hypothesis
([`SmallFibreKnownModelClassGap`](SymmetricSubgroupAsymptotics/SmallFibreKnownModelClassGap.lean),
[`GaronziMarotiNonaffineShapeCFSGReduction`](SymmetricSubgroupAsymptotics/GaronziMarotiNonaffineShapeCFSGReduction.lean)).
Every actual affine top with at least 128 blocks is also paid, for both
small fibre sizes. The faithful affine order bound
`|Top| <= n^(log₂(n)+1)` feeds one dyadic scalar induction, retaining
the same original projection and subnormal source. Consequently any
surviving affine-top small-fibre counterexample has at most 127 blocks
and at most 381 original points. No supplied primitive-top class bound
or finite action census enters this cutoff
([`AffineTopSmallFibreOrderNumerics`](SymmetricSubgroupAsymptotics/AffineTopSmallFibreOrderNumerics.lean),
[`OriginalMinimalBlockAffineTopClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockAffineTopClassBound.lean)).
The same native installer also covers every prime block count at least
five, every block count at least 49 with `log_p(n) <= 3`, and every
block count at least 64 with `log_p(n) <= 4`. Here `p` belongs to the
same actual regular normal subgroup; no elementary-abelian conclusion
or primitive-top assumption is inserted
([`OriginalMinimalBlockSupportedAffineTopClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockSupportedAffineTopClassBound.lean)).
On the separate original-component branch, every alternating simple
socle is covered, including A6. At its
minimum faithful degree, the actual group/socle quotient divides
`6!/360 = 2`; at larger degree the complete outer factor fits the same
reserve. No action recognition or new model input is needed
([`OriginalMinimalBlockAlternatingAllComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockAlternatingAllComponentClassBound.lean)).

For the general class-count reduction,
[`SmallTopGaronziMarotiCubes`](SymmetricSubgroupAsymptotics/SmallTopGaronziMarotiCubes.lean)
proves `k(A)^3 <= 5^(n-1)` for every faithful action on its original
`n` points with an equivariant partition into two or three blocks, each
of size two or three, and transitive block action. All four size pairs
are covered. The proof retains actual block kernels and nonsplit lifts;
ternary kernels are not assumed abelian. The global class-count theorem
remains one of the explicit published inputs above.

[`AbelianExtensionClassComparison`](SymmetricSubgroupAsymptotics/AbelianExtensionClassComparison.lean)
proves `k(G) <= k(N semidirect (G/N))` for every finite group and normal
abelian subgroup `N`, using the actual quotient conjugation action on
that same `N`. The proof compares each joint quotient fibre of commuting
pairs, including nonsplit extensions. It does not replace `N` by a larger
permutation base group.

The binary full-wreath continuation now injects actual conjugacy classes
into pairs of partitions with their common total size retained. It proves
`k(C2 wreath S_b) <= (b+1)*2^b` and its required class-count cube bound for
every `b >= 7`
([`BinaryFullWreathClassBound`](SymmetricSubgroupAsymptotics/BinaryFullWreathClassBound.lean)).
The original saturated-kernel, full-symmetric-top consumer is also proved.
For an arbitrary correlated binary kernel, the two valid codimension
bounds instead give
`k(A)^2 <= 2^b*k(actualTop)*k(actualFullWreath)`
([`BinaryBlockClassGeometricMean`](SymmetricSubgroupAsymptotics/BinaryBlockClassGeometricMean.lean)).
These estimates retain the actual top group; they assert no monotonicity
under enlargement of the abelian kernel.
The full-symmetric-top estimate is now proved for every correlated binary
kernel when `b >= 12`
([`BinarySymmetricTopClassBound`](SymmetricSubgroupAsymptotics/BinarySymmetricTopClassBound.lean)).
An explicit shrink-and-restore injection on partitions proves the needed
Fibonacci bound, so no finite partition census is assumed.

The cycle code now works for **every finite coefficient group C**, retaining
ordered products rather than replacing noncommutative coefficients by an
abelian quotient. A reversible colored-partition encoding proves
`k(C wreath S_b) <= (b+1)^k(C) * Fibonacci(b+1)`
([`FullSymmetricWreathColoredPartitionBound`](SymmetricSubgroupAsymptotics/FullSymmetricWreathColoredPartitionBound.lean)).
Combining the two bounds on the same actual projection range proves
`k(H)^3 <= 5^(2b-2)` for binary coefficients and `b >= 10`, and
`k(H)^3 <= 5^(3b-2)` for coefficient order at most six, at most three
classes and `b >= 28`, whenever that range is subnormal in the full
symmetric group on the same `b` coordinates. No transitivity, full-base
or splitting assumption is made on H. Original binary and ternary block
actions and their actual nested-block consumers are checked
([`OriginalBinaryBlockSubnormalClassGap`](SymmetricSubgroupAsymptotics/OriginalBinaryBlockSubnormalClassGap.lean),
[`OriginalTernaryBlockSubnormalClassGap`](SymmetricSubgroupAsymptotics/OriginalTernaryBlockSubnormalClassGap.lean),
[`NestedTernarySubnormalSymmetricTopClassBound`](SymmetricSubgroupAsymptotics/NestedTernarySubnormalSymmetricTopClassBound.lean)).
For alternating socles, the sharper actual subnormal cap `4*p(m)` pays
**every multiplicity at least two** in the original binary/ternary
source, without a large-degree cutoff. The single-factor branch is paid
when the actual index is at least `2m+2`; literal degree-m actions are
recognized before the preceding wreath bounds are used. The resulting
same-action residual has multiplicity one and
`m <= actualIndex < 2m+2`. Natural equality can remain only at `m <= 9`
in the binary case or `m <= 27` in the ternary case
([`AlternatingSmallFibreRefinedShortIndexResidual`](SymmetricSubgroupAsymptotics/AlternatingSmallFibreRefinedShortIndexResidual.lean)).
This narrows the class-count proof frontier; it does not certify the
remaining interval or remove the published global class-count input.

For every actual affine profile, every subgroup now satisfies the
class-count cube bound except possibly at degrees `8,16,32`
([`AffineClassThreeDegreeResidual`](SymmetricSubgroupAsymptotics/AffineClassThreeDegreeResidual.lean)).
The proof covers all degrees at least 64, all prime degrees, all degrees
`p^2` for primes `p >= 5`, and all degrees `p^3` for primes `p >= 3`.
The prime-degree argument proves the actual Frobenius class formula;
the prime-power argument bounds automorphisms using an actual generating
set of size at most `log_p(|V|)` in the original regular subgroup.
Neither argument assumes a primitive catalogue or elementary abelianness.
Degree four is proved for every faithful action: the transitive group is
binary, A4 or S4, while the intransitive case splits through its actual
kernel and image. Two sparse conjugacy covers settle the actual A4 and S4
groups, without a subgroup census
([`FourPointPermutationClassBound`](SymmetricSubgroupAsymptotics/FourPointPermutationClassBound.lean)).
Degree nine is also proved for every original affine subgroup, with at
most 54 conjugacy classes. The proof includes cyclic regular groups;
otherwise a faithful action on the four projective rays of the actual
ternary plane gives a complement class bound of 10. Retaining the actual
translation kernel gives bounds of 30 for a proper kernel and 39 for a
full kernel
([`AffineDegreeNineSubgroupClassBound`](SymmetricSubgroupAsymptotics/AffineDegreeNineSubgroupClassBound.lean)).
For genuine primitive affine actions, every degree is now proved for
every original subgroup
([`PrimitiveAffineAllSubgroupsClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineAllSubgroupsClassBound.lean)).
A nonscalar linear automorphism has a sparse centralizer chart, recording
one nonzero image and all but two remaining basis images. On the actual
binary five-dimensional translation space this bounds every nonidentity
centralizer by `31*32^3`. Counting commuting pairs then bounds the classes
of every actual complement subgroup; retaining the proper or full
translation kernel gives `k(H) <= 16252976`, whose cube is at most `5^31`
([`PrimitiveAffineDegreeThirtyTwoClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeThirtyTwoClassBound.lean)).
Primitivity supplies the actual elementary translation module. No matrix
or primitive-group census is assumed in this argument.
Degrees eight and sixteen use a uniform binary quadratic dichotomy:
either three successive orbit vectors are independent, or the operator
is square-zero after subtracting the identity, or it satisfies
`T^2+T+I=0`. Sparse evaluation charts and actual kernel bases bound the
nonidentity linear centralizers by 8 and 288. The identity contribution
in the complement class sum then gives original subgroup class bounds
36 and 2312, whose cubes meet the required budgets
([`PrimitiveAffineBinarySmallClassBound`](SymmetricSubgroupAsymptotics/PrimitiveAffineBinarySmallClassBound.lean)).
The general profile estimates above also apply without primitivity and
retain the three binary degrees; the complete primitive theorem uses
primitivity to construct its elementary translation module.
For primitive degree at least 1024, the complete O'Nan--Scott power-degree
branch is now proved for every actual subgroup. Its original socle and
outer-wreath embedding give an order ceiling of
`n^(4*floor(log_2(n))+2)`, which the uniform numerical tail converts into
the class-count cube bound. The actual primitive dispatcher leaves the
separate proper-simple-subgroup-index branch explicitly open
([`PrimitiveClassIndexFormReduction`](SymmetricSubgroupAsymptotics/PrimitiveClassIndexFormReduction.lean)).
For an actual alternating socle with at least two factors, the entire
proper-index degree branch is also proved for every original subgroup.
The original socle and outer-wreath quotient bound the group order by
`(2*m!)^k*k!`; a uniform factorial induction proves that its cube is at
most `5^(m^k-1)` for `m >= 5` and `k >= 2`. The actual proper index is
at least `m`, so the bound applies without identifying a product action
([`PrimitiveSocleAlternatingProductClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleAlternatingProductClassBound.lean)).
For a single alternating factor, the actual conjugacy-class partition map
has fibres of size at most two, with two classes possible only for a
partition into distinct odd parts. A reversible injection from those
split types to odd-sign partitions proves `k(A_m) <= p(m)` for every
`m >= 2`. The partition Fibonacci bound pays its class-count cube at
every `m >= 5`. The exceptional automorphisms at `m=6` are treated
separately: a small kernel-checked partition menu proves `k(A_6) <= 7`,
the actual faithful degree-six action identifies its original image,
and the literal socle order 360 excludes degree seven.
Together with the product estimate, this closes the alternating
subnormal class-count consumer at every primitive degree, every socle
factor count and both original degree forms
([`AlternatingConjugacyPartitionBound`](SymmetricSubgroupAsymptotics/AlternatingConjugacyPartitionBound.lean),
[`PrimitiveSocleAlternatingAllDegreesClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleAlternatingAllDegreesClassBound.lean)).
The single-factor statement retains actual subnormality.

The type-A, type-B, unitary, symplectic, type-D, twisted-D, F4, twisted E6, E6, E7, E8,
G2, Suzuki and triality simple types are
also covered at every socle factor count, for every original subgroup
and both raw degree forms, when the primitive degree is at least 1024
([`PrimitiveSocleTypeAClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTypeAClassBound.lean),
[`PrimitiveSocleUnitaryClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleUnitaryClassBound.lean),
[`PrimitiveSocleSymplecticClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticClassBound.lean),
[`PrimitiveSocleOrthogonalBClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleOrthogonalBClassBound.lean),
[`PrimitiveSocleOrthogonalDClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleOrthogonalDClassBound.lean),
[`PrimitiveSocleTwistedDClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTwistedDClassBound.lean),
[`PrimitiveSocleGTwoClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleGTwoClassBound.lean),
[`PrimitiveSocleSuzukiClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSuzukiClassBound.lean),
[`PrimitiveSocleTrialityClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTrialityClassBound.lean),
[`PrimitiveSocleFFourClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleFFourClassBound.lean),
[`PrimitiveSocleTwistedE6ClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTwistedE6ClassBound.lean),
[`PrimitiveSocleExceptionalClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleExceptionalClassBound.lean)).
The actual natural representations give order ceilings, while literal
root stars give lower bounds for each proper subgroup's index. One
shared estimate transports the component and outer orders through the
original full socle and outer-wreath quotient, retaining its factorial.
For E6, E7 and E8, finite reflection certificates cover all original
integral roots with 72, 126 and 240 entries, respectively. Their positive
parts have 36, 63 and 120 entries. An actual `U-T-word-U` cover and a
signed root-label bound on original word values give group-order
ceilings `q^126`, `q^189` and `q^320`. Actual commuting root stars and
their elementary-row conjugations give proper-index lower bounds
`q^2`, `q^3` and `q^5`. Together with the proved outer bounds, these
fit the same component budget in every characteristic, including `q=2`
([`CFSGExceptionalOriginalOrderUpper`](SymmetricSubgroupAsymptotics/CFSGExceptionalOriginalOrderUpper.lean),
[`CFSGExceptionalChainStarIndex`](SymmetricSubgroupAsymptotics/CFSGExceptionalChainStarIndex.lean)).
The bounded-degree E6/E7/E8 cases are also closed uniformly. One literal
21-root configuration, padded from E6 into E7 and E8, embeds the
prime-field Heisenberg group of order `p^21` into each original model.
The actual commutator pairing bounds a point stabilizer missing its
prime-order centre by `p^10`. Simplicity makes a nonidentity central
element move some coset, proving every proper index is at least
`p^11 >= 2048`. Both raw socle degree forms inherit that lower bound.
Thus the three class-count consumers apply at every degree, with no
small-field or action census
([`CFSGExceptionalHeisenbergIndex`](SymmetricSubgroupAsymptotics/CFSGExceptionalHeisenbergIndex.lean),
[`PrimitiveSocleExceptionalAllDegreesClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleExceptionalAllDegreesClassBound.lean)).
Twisted D uses its actual faithful action on the fixed space over the
fixed field, avoiding a larger matrix-space ceiling over the quadratic
extension. G2 uses its faithful natural eight-dimensional matrices and
the proved original outer bound. None of these consumers requires an
order, representation-recognition or class-count callback.
For triality an actual twelve-word Bruhat cover, its four-parameter
pair-normalizer bound and its positive subgroup of order `q^12` give
the original order ceiling `q^32`. Together with the proved outer bound
and proper-index estimate, this supplies the same component budget.
For F4, the actual diagram-fixed positive subgroup has at most `q^24`
elements. The successive orthogonal-root frame fibres have sizes at most
24, 6, 4 and 2, so the actual relative Weyl actions have at most 1152
values. The resulting original four-factor cover, with the actual
opposed-pair normalizer of size at most `q^4`, gives order at most `q^63`.
The proved outer bound and proper-index lower bound then give the
component budget `|F4(q)|*|Out(F4(q))| <= q^66 <= index^66`
([`CFSGFFourOriginalOrderUpper`](SymmetricSubgroupAsymptotics/CFSGFFourOriginalOrderUpper.lean)).
This count does not identify the opposed-pair normalizer with a torus.
The same checked fixed-height and finite Weyl machinery applies over the
quadratic extension for twisted E6. Keeping all six ambient scalar
coordinates gives the sufficient bounds `q^48` for each positive factor
and `q^12` for the actual pair normalizer. The original group therefore
has order at most `q^119`. Its proved outer bound and `q^2` proper-index
lower bound pay the same component budget, without fixed-field scalar
coupling or an additional finite catalogue
([`CFSGTwistedE6OriginalOrderUpper`](SymmetricSubgroupAsymptotics/CFSGTwistedE6OriginalOrderUpper.lean)).
The exact CFSG dispatcher retains the original surviving simple-model
witness
([`PrimitiveLargeSubnormalCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveLargeSubnormalCFSGReduction.lean)).
An all-degree dispatcher now combines that large-range result with the
complete alternating and E6/E7/E8 consumers, retaining the literal
surviving simple-model witness and its original degree form in every
remaining bounded case
([`PrimitiveAllDegreeSubnormalCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeSubnormalCFSGReduction.lean)).
A further actual-model refinement leaves only finite field/rank parameter
sets for the bounded classical branches, retaining the same original
subnormal subgroup and degree witness
([`PrimitiveAllDegreePrimaryClassCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreePrimaryClassCFSGReduction.lean)).
A shared basis-prefix argument bounds every finite faithful linear group
preserving a nonsingular bilinear form by `q^(n*(n+1)/2)`. The same
argument accepts a separating sesquilinear pairing. On the original
models this gives orthogonal orders at most `q^(2*r^2+r)` for D and
twisted D, `q^(2*r^2+3*r+1)` for B, and `q^((r+1)*(r+2))` for unitary.
The actual rank-one A Borel coordinates also give the stronger `q^3`
order bound. These estimates retain every original subgroup, socle
factor count, factorial and degree witness. Their checked numerical
tails remove a common batch of parameter cases. The original rank-one A
class-capacity branch is now complete over every permitted finite field
([`PrimitiveSocleTypeARankOneCompleteClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTypeARankOneCompleteClassBound.lean)).
The SL2 trace-class bound and central-involution quotient count give
`2*k(PSL2(q)) <= q+5` in odd characteristic. Actual torus and root actions
handle the even fields and the small odd fields uniformly; the fields of
orders four and five use proved alternating-group equivalences. For order
nine, a shared order-360 argument either constructs an A6 equivalence from
an index-six subgroup or proves every proper index is at least eight.
These bounds apply to the original subnormal subgroup and both original
degree forms, with no new census assumption.
The entire rank-two A branch is now complete as well
([`PrimitiveSocleTypeARankTwoCompleteClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTypeARankTwoCompleteClassBound.lean)).
Actual three-dimensional cyclic, eigenspace and square-zero bases give
`k(SL3(q)) <= gcd(q-1,3)*(q^2+2*q)` over every finite field. Scalar
centralizers bound GL-to-SL class splitting by `gcd(q-1,n)` in every
dimension, and the same exact central-scalar count sharpens the original
outer bound to `2*gcd(q-1,n)*|Aut(F)|`. The two-element field uses the
proved order 168 and a faithful coset action to force proper index at
least seven, without an exceptional isomorphism or census.
The class equation gives a reusable improvement from a proper-index lower
bound `b`: `k(S) <= |S| / b + 1` for center-free `S`. Exact determinant
and central quotients discharge three further A parameters with this
test. Separately, the original odd-characteristic C2 model has proper
index at least `q^2`. One uniform numerical induction then closes its
capacity for every `q >= 7`. Over a prime field the same coupled
stabilizer gives the stronger bound `q^3`, which also closes the two
small odd fields. Thus the whole odd-characteristic C2 branch is closed
([`PrimitiveSocleSymplecticOddRankTwoClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticOddRankTwoClassBound.lean)).
For the two remaining binary type-A parameters, one polynomial-module
template injects actual general-linear conjugacy classes into finite
multisets of interior coefficient words. The checked covers have 18
codes in dimension four and 104 in dimension six. Literal surjective
matrix and central-quotient maps transfer the bounds to the original
projective models, closing both component capacities without exceptional
isomorphisms or matrix enumeration
([`PrimitiveSocleTypeABinaryCyclicClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTypeABinaryCyclicClassBound.lean)).
In every higher rank `r >= 3`, the original odd-characteristic model
now has proper index at least `p*q^(2*r-2)`. The proof couples the actual
Heisenberg kernel and full symplectic tail stabilizer, retaining genuine
prime-field annihilators. Explicit transvection words and the same
original coset action discharge the embedding and motion premises.
One numerical template then closes the class-count capacity in every
odd characteristic and rank
([`PrimitiveSocleSymplecticOddHigherRankClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticOddHigherRankClassBound.lean)).
In characteristic two, actual symmetric shear matrices and their literal
general-linear normalizer yield the same `q^2` proper-index bound for
`q >= 8`. The coupled argument retains an arbitrary prime-field
annihilator of the actual stabilizer kernel, with no extension-field
linearity assumption. The shared numerical budget closes these C2
capacities as well; field order four uses the primary class-count proof below
([`PrimitiveSocleSymplecticBinaryRankTwoClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticBinaryRankTwoClassBound.lean)).
A sharper actual quadratic-level argument proves
`q*(q-1)^2 <= 2*[S:H]` for every proper original binary C2 subgroup,
including index at least 18 at field order four, as used in the
field-four primary class-count application below
([`CFSGSymplecticBinaryRankTwoSharpIndex`](SymmetricSubgroupAsymptotics/CFSGSymplecticBinaryRankTwoSharpIndex.lean)).
The same-annihilator argument now works in every characteristic-two rank
`r >= 3`: the actual symmetric shear kernel, its projected general-linear
stabilizer and the original coset action give
`(q-1)*q^(r-2)*(q^r-q) <= 2*[S:H]`. A genuine prime-field functional
reconstructs a quadratic form; its two-frame orbit is counted jointly
with the same kernel quotient. This pays the component capacity whenever
`q >= 4` or `r >= 5`. The field-two budget retains the exact lower bound
`2^(r-3)*(2^r-2)`. The literal symplectic realization also transfers the
same theorem to characteristic-two B models, inheriting simplicity from
that B model rather than assuming it for an independent C model
([`PrimitiveSocleSymplecticBinaryHigherRankClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticBinaryHigherRankClassBound.lean)).
Over the two-element field, a second point-radical argument retains the
same kernel, projected stabilizer and normalized value-one annihilator
slice. Actual tail transvections give the proper-index lower bound
`2^(r-1)*(2^(r-1)-1)` for every rank at least three. At rank four this is
`56`; the literal component cube is at most `2^117 <= 5^55`. This pays
both original `C4(2)` and `B4(2)`, with simplicity inherited from the
original model in each case
([`PrimitiveSocleSymplecticBinaryPointRankFourClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticBinaryPointRankFourClassBound.lean)).
For split orthogonal D in rank `r >= 4`, actual elementary words are now
transitive on every nonzero quadratic level, in every characteristic.
Counting a positive-nonzero level slice and retaining the genuine
prime-field annihilator of the same point-radical stabilizer gives
`(q^(r-1)-1)*q^(r-2) <= [S:H]`. There is no additional prime multiplier.
The shared order budget pays every field order at least three and every
rank at least five; `D4(2)` uses the quadratic class-count proof below
([`PrimitiveSocleOrthogonalDPointRadicalClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleOrthogonalDPointRadicalClassBound.lean)).
In odd characteristic the actual type-B point radical gives
`(q^(r-1)-1)*q^(r-1) <= [S:H]` for every rank `r >= 3` and every proper
subgroup of the original model. The common order budget pays all these
cases, for every original factor count and both degree forms. The type-B
binary rank-three case uses the primary class-count proof below
([`PrimitiveSocleOrthogonalBPointRadicalClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleOrthogonalBPointRadicalClassBound.lean)).
The family-independent class-equation test also closes seven further
orthogonal, twisted-orthogonal and unitary parameter cases, combining the actual matrix
order and outer-order estimates before taking the cube. The twisted-D
application retains the proved outer bound `8*f`, rather than enlarging
it to a power of the field order
([`ClassicalClassEquationSmallParameters`](SymmetricSubgroupAsymptotics/ClassicalClassEquationSmallParameters.lean)).
The twisted-D point radical now gives the actual unmultiplied bound
`(q^(r-2)-1)*q^(r-1) <= [S:H]` in every admissible rank and characteristic.
Its construction includes the rank-three anisotropic-tail base and keeps
the prime-field annihilator and the tail stabilizer of the same subgroup.
The common component budget pays every field order at least three and
every rank at least five; `twistedD4(2)` uses the quadratic class-count proof below
([`PrimitiveSocleTwistedDPointRadicalClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleTwistedDPointRadicalClassBound.lean)).
For unitary rank two, the actual nonabelian radical retains its central
intersection, vector image and projected torus subgroup from the same
stabilizer. Their coupled cardinal identity and orbit bounds give proper
index at least `27`, `40` and `50` at field orders `3`, `4` and `5`.
The shared class-equation division test pays all three using the existing
coarse outer bound `6*f`
([`PrimitiveSocleUnitaryRankTwoCoupledClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleUnitaryRankTwoCoupledClassBound.lean)).
For unitary ranks at least four, the same nonabelian radical retains its
central intersection and vector image together with the actual middle
special-unitary action. Genuine prime-field isotropy and a counted
same-norm vector orbit give
`p*(q^2-1)*q^(2*r-5) <= [S:H]`. The actual original model supplies the
central element moving a coset. At binary ranks four, five and six,
the resulting bounds `48`, `192` and `768` pay the shared class-equation
capacity and are installed in the native dispatcher
([`PrimitiveSocleUnitaryHigherCoupledClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleUnitaryHigherCoupledClassBound.lean)).
For unitary rank three at field orders two and three, actual middle-group
orbits and the same radical annihilator give proper indices at least
`24` and `48`. The binary case also retains a counted first isotropic
column, sharpening the original model's order bound. These estimates,
the rank-two and higher-rank results, and the general isometry estimate
now prove the required class-count capacity for every admissible unitary
rank and field
([`PrimitiveSocleUnitaryCompleteClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleUnitaryCompleteClassBound.lean)).
The guarded classical frontier is now empty, down from 187 literal
field/rank pairs. Every admissible classical model is discharged by the
native dispatcher on the same original primitive action
([`PrimitiveAllDegreeClassicalCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeClassicalCFSGReduction.lean)).
This is a theorem for the original action, rather than an action census.
The entire twisted-E6 family is now discharged at every degree as well
([`PrimitiveAllDegreeTwistedE6CFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeTwistedE6CFSGReduction.lean)).
Two actual diagram-stable commuting root families give an injective
Heisenberg group over the literal quadratic fixed field, with ten
coordinates in each half. Its signed pairing is nondegenerate even in
characteristic two, using trace surjectivity rather than averaging.
The injection survives the original central quotient. Every proper
subgroup therefore has index at least `p*q^10 >= 2048`
([`CFSGTwistedE6HeisenbergIndex`](SymmetricSubgroupAsymptotics/CFSGTwistedE6HeisenbergIndex.lean)).
This excludes the whole bounded branch; the existing large-degree bound
then applies through both original socle degree forms.
The entire Suzuki family is also discharged at every degree
([`PrimitiveAllDegreeSuzukiCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeSuzukiCFSGReduction.lean)).
For `q = 2^(2*m+1)` and `m >= 1`, every proper original subgroup has
index at least `(q-1)*2^(m+1)`
([`CFSGSuzukiQuadraticTorusIndex`](SymmetricSubgroupAsymptotics/CFSGSuzukiQuadraticTorusIndex.lean)).
The proof couples the same subgroup's central intersection, vector image
and projected torus. An arbitrary prime-field annihilator and actual
square isotropy bound the vector image; its scalar dual orbit pays the
central quotient and projected torus together. The resulting index,
exact original order and proved outer bound pay the full component
order cube, including `m=1`, and both original primitive degree forms
([`PrimitiveSocleSuzukiCompleteClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSuzukiCompleteClassBound.lean)).
The actual four-pair fixed-root Heisenberg subgroup also pays every
F4 field order at least three. It gives proper index `p*q^4`, and its
injection proves original order at least `q^9`. One scalar seed and a
uniform polynomial tail pay the full component order cube
([`PrimitiveAllDegreeFFourHeisenbergCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeFFourHeisenbergCFSGReduction.lean)).
The binary field is now discharged as well. The actual quadratic Levi
source retains the same central intersection, vector image and join index;
its normalized annihilator orbit gives proper index at least `128` and
original order at least `2^15`. The component bound `2^66` pays its full
order cube since `2^198 <= 5^127`. This closes the entire original F4
primitive class-count family
([`CFSGFFourBinaryQuadraticLeviIndex`](SymmetricSubgroupAsymptotics/CFSGFFourBinaryQuadraticLeviIndex.lean),
[`PrimitiveAllDegreeFFourCompleteCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeFFourCompleteCFSGReduction.lean)).
The entire ReeG2 family is now discharged at every parameter as well
([`PrimitiveAllDegreeReeGTwoCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeReeGTwoCFSGReduction.lean)).
For an arbitrary subgroup of its actual positive group, the first image,
middle image of the first-kernel intersection, and central intersection
are retained together. Their literal commutator implies multiplication
orthogonality over the prime field. Exact layer cardinalities then give
proper index at least `3*q`, without torus invariance or full-field
linearity of the subgroup. The same original fixed/derived group and
proved outer bound pay the order cube through both primitive degree forms.
With the complete triality, G2 and ReeF4 closures below, the primitive
class-count frontier retains only Tits and the 26 sporadic models.
The global general class-count input remains explicit.
A reusable central-extension theorem now proves the sharp bound
`p*q^m <= [N:L]` from the actual scalar commutator pairing on a
`2*m`-dimensional quotient, whenever the same subgroup `L` does not
contain the central field line. Exact kernel/image cardinalities and
prime-field annihilators supply the proof; no Heisenberg recognition
isomorphism or full-field linearity of `L` is required
([`CentralExtensionScalarPairingIndex`](SymmetricSubgroupAsymptotics/CentralExtensionScalarPairingIndex.lean)).
The actual triality cube pairing, complementary coefficient separation,
fixed tensor coordinates and scalar-valued raw commutator are checked.
Their fixed-field binding is now complete, including characteristic
three without averaging: the actual fixed middle radical has order
`q^9` and injects into the same original model, giving proper index
`p*q^4`. This pays every original triality primitive component at
`q>=3`, with all socle factors and both raw degree forms retained
([`PrimitiveAllDegreeTrialityHeisenbergCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeTrialityHeisenbergCFSGReduction.lean)).
The binary triality case is also proved on the actual middle source of
order 512. Its centre has order two and its intrinsic quotient has 256
elements. Actual root translations and a short Weyl word force an
invariant quotient subspace to be zero or full. The same stabilizer and
join then give proper index at least 64. The original component ceiling
pays its cube at this index, closing the entire triality family
([`PrimitiveAllDegreeTrialityCompleteCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeTrialityCompleteCFSGReduction.lean)).
No full linear-group image or model-recognition premise is used.
Separately, an actual twelve-word fixed Bruhat
cover improves the original G2 order ceiling to
`24*f*q^12*(q-1)^2`, with no group-order formula assumed
([`CFSGGTwoD4GeckFixedBruhatOrderUpper`](SymmetricSubgroupAsymptotics/CFSGGTwoD4GeckFixedBruhatOrderUpper.lean)).
The actual diagram-fixed middle pairing is also nondegenerate in
characteristic other than three. A proved finite-order defect argument
gives genuine fixed-word lifts, and the actual radical has order `q^5`.
Its injection into the same original model gives proper index `p*q^2`.
Together with the sharper component order ceiling, this pays every
`q>=5` in characteristic other than three, with the full original socle
and both degree forms retained
([`PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction.lean)).
The characteristic-three degeneration is now handled at every field
order at least nine. Its full centre has order `q^3`; the actual endpoint
image has order `q^2`. The same original-source stabilizer, full central
intersection and join index give proper index `3*(q^2-1)`, paying the
original component-order cube through both primitive degree forms
([`PrimitiveAllDegreeGTwoEndpointCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeGTwoEndpointCFSGReduction.lean)).
No averaging, split extension or full-field linearity of the stabilizer
is assumed in the characteristic-three proof. The field-four G2 case is
now discharged separately: actual middle-node torus words realize every
nonzero scalar on the whole centre, while the full normalizer action
needs only prime-field linearity. The same central intersection, vector
image and join give proper index `q^2*(q-1)=48`. The exact component bound
`192*4^14` pays its cube at this index. The field-three case is also
proved, using two actual source orbits. A highest-root-moved orbit has
size at least 27; if its size is below 54, the retained central plane
fixes the entire orbit. The actual exceptional root exchange supplies
a disjoint second moved orbit of size at least 27. Thus every proper
subgroup of the original simple G2(3) has index at least 54. The component
ceiling `48*3^14` pays its full cube. This closes the entire G2 primitive
class branch with every socle factor and both actual degree forms retained
([`PrimitiveAllDegreeGTwoCompleteCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeGTwoCompleteCFSGReduction.lean)).
The combined frontier also removes the entire ReeF4 tail `m>=4` in both
degree regimes: the proved original index and order bounds pay the cube
by an induction from field order 512
([`PrimitiveAllDegreeReeFFourTailCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeReeFFourTailCFSGReduction.lean)).
The actual middle Suzuki Borel in the same original ReeF4 source also
gives proper index `(q-1)*2^(m+1)`. A single induction beginning at `m=2`
pays every component cube for `m>=2`. The remaining field-eight case is
also proved: an actual fixed word of 70 signed roots moves a vector of
period 109 in the original 26-coordinate action. Its 25 consecutive
transitions and degree-25 annihilator are checked in Lean. The actual
central quotient kernel lies in the same Borel, whose order is prime to
109, so every proper subgroup of the original simple ReeF4(8) has index
at least 109. This pays the full component cube. The combined primitive
reduction now leaves exactly 27 models: Tits and the 26 sporadic groups.
It retains the original action, subnormal subgroup, all socle factors
and both degree forms, and explicitly discharges the inherited
large-degree ReeG2 witness using its proved whole-family bound.
The remaining finite-model estimates are open and are not installed
as new T1 assumptions
([`CFSGReeFFourFieldEightPrimeIndex`](SymmetricSubgroupAsymptotics/CFSGReeFFourFieldEightPrimeIndex.lean),
[`PrimitiveAllDegreeReeFFourCompleteCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveAllDegreeReeFFourCompleteCFSGReduction.lean)).
For an actual nonsplit extension with abelian kernel `N` and quotient `Q`,
a checked joint commuting-fibre formula bounds `|Q|*k(G)` by the sum of
`[N : image(mu(s,t))]` over commuting quotient pairs. Each motion map
retains both quotient elements and the same kernel; no full-base
class-number monotonicity is assumed. The binary block kernel and the
actual ternary even kernel are bound to this formula
([`SmallFibreJointMotionClassBound`](SymmetricSubgroupAsymptotics/SmallFibreJointMotionClassBound.lean)).
A separate uniform numerical estimate and the actual coordinate class
budgets pay both binary and ternary block actions when their top has
at least 4096 points and order at most `b^(4*log_2(b)+24)`, with the
integer logarithm used in Lean. Actual affine, nonaffine power-form and
index-form top adapters supply that order bound under their stated
structural hypotheses
([`LargeTopSmallFibreStructureBounds`](SymmetricSubgroupAsymptotics/LargeTopSmallFibreStructureBounds.lean)).
Every Lie-type model now supplies one of the two required component
order budgets at every proper subgroup index: the logarithmic power
`index^(4*log_2(index)+23)` or the fixed power `index^66`. The actual
primitive-top reduction is also complete for alternating factors:
a checked injection bounds the partition number by
`(n+1)^4 * 6^((n+4)/5)`, and the resulting class budget pays every
alternating socle multiplicity. At top degree at least 4096, only
Tits or sporadic factors remain, retaining the same socle,
proper-index subgroup and both failed component-order budgets
([`CFSGModelComponentIndexOrderBudget`](SymmetricSubgroupAsymptotics/CFSGModelComponentIndexOrderBudget.lean),
[`PartitionFiveSeparatedEncoding`](SymmetricSubgroupAsymptotics/PartitionFiveSeparatedEncoding.lean),
[`LargeTopFiniteModelResidual`](SymmetricSubgroupAsymptotics/LargeTopFiniteModelResidual.lean)).
For an actual minimal block component of degree at least 4096, a separate
reduction pays every top from strictly smaller general permutation cases,
again retaining only an actual Tits or sporadic component witness.
The actual four-point minimal component is also complete for every
top, from strictly smaller general permutation cases. Proper coordinate
kernels have a proved class saving; saturation instead gives an actual
equivalence with the full wreath product with the same component and
top. Ordered cycle products give coarse class codes for noncommutative
two- and three-cycle wreath actions, closing the small-top seam. These
lemmas do not compare a proper subgroup's class count monotonically
with an enlarged base
([`OriginalMinimalBlockLargeComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockLargeComponentClassBound.lean),
[`ActualBlockProperClassDichotomy`](SymmetricSubgroupAsymptotics/ActualBlockProperClassDichotomy.lean),
[`WreathShortCycleClassBound`](SymmetricSubgroupAsymptotics/WreathShortCycleClassBound.lean),
[`OriginalMinimalBlockFourComponentClassBound`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockFourComponentClassBound.lean)).
Actual consecutive minimal-block choices now bind the large intermediate
component to the same original two quotient maps. At least four outer
blocks use strictly smaller general permutation cases; two or three
outer blocks with intermediate fibre at least 4096 use the same-source
subnormal class gap. The alternating intermediate branch uses its actual
subnormal coordinate, rather than an order bound for an arbitrary subgroup
([`OriginalMinimalBlockTopRefinement`](SymmetricSubgroupAsymptotics/OriginalMinimalBlockTopRefinement.lean),
[`NestedBlockPrimitiveIntermediateClassResidual`](SymmetricSubgroupAsymptotics/NestedBlockPrimitiveIntermediateClassResidual.lean)).
Consequently the global statement has an explicit least-counterexample
reduction: either the published class bound holds, or an actual failed
permutation action has degree between 4 and 36855, or an actual failed
action retains a literal Tits/sporadic component, top or intermediate
component. Both original primitive degree forms and the failed subnormal
budgets are retained. This does not prove the bounded actions, and it
introduces no bounded-degree hypothesis into T1
([`GaronziMarotiGlobalBoundedCounterexample`](SymmetricSubgroupAsymptotics/GaronziMarotiGlobalBoundedCounterexample.lean)).
The bounded block seams and finite-model estimates therefore still remain
before the global Garonzi--Maroti input can be removed.

The shared class-count route now constructs the literal fixed-polar
quadratic-refinement torsor and its actual contragredient affine action.
Burnside counting of joint fixed sets proves affine inertia domination.
Consequently a quadratic isometry group over a field of order two has
class count at most that of its full polar-preserver group plus one
nonzero-vector stabilizer, whenever that natural action is transitive
on nonzero vectors. The isometry group is the same literal definition
used by the split and twisted orthogonal models; no quadratic-type
classification is a premise
([`QuadraticIsometryPolarStabilizer`](SymmetricSubgroupAsymptotics/QuadraticIsometryPolarStabilizer.lean)).
The actual point stabilizer now maps onto the smaller affine symplectic
group with kernel of order at most the field order `q`. Exact affine
inertia counting gives the recurrence `p(r+1) <= q*(s(r)+p(r))`, where
`s(r)` counts classes of the symplectic group on `2r` coordinates and
`p(r)` counts classes of its nonzero-vector stabilizer; the base satisfies
`p(1) <= q`
([`CFSGSymplecticPointClassRecurrence`](SymmetricSubgroupAsymptotics/CFSGSymplecticPointClassRecurrence.lean)).
In characteristic two, a constructive norm lift proves that two
fixed-point-free elements of the literal polar-preserver group are
conjugate there whenever they are conjugate in the general linear group
([`BilinearFixedFreeConjugacyFusion`](SymmetricSubgroupAsymptotics/BilinearFixedFreeConjugacyFusion.lean)).
The actual symplectic characteristic polynomial is self-reciprocal, and
its values on `2r` coordinates have cardinality at most `q^r`
([`SymplecticSelfReciprocalCode`](SymmetricSubgroupAsymptotics/SymplecticSelfReciprocalCode.lean)).
The module multiplicity count is now proved by a finite primary code:
for each actual polynomial, partitions of its primary multiplicities
have at most `2^(N-1)` values when the total exponent mass is at most
`N`. Equality of codes gives actual general-linear conjugacy. On the
binary fixed-free branch every irreducible factor has degree at least
two, so `N = r` suffices. Combining this with the point-stabilizer
recurrence proves `k(Sp6(2)) <= 96`, `k(Sp8(2)) <= 448`, and
`k(Sp4(4)) <= 192`, without a class table or a new class-count premise
([`CFSGSymplecticSmallClassBounds`](SymmetricSubgroupAsymptotics/CFSGSymplecticSmallClassBounds.lean)).
The same original primitive actions and all socle factors therefore
satisfy the required class-cube estimate in the former `B3(2)`,
`C3(2)` and `C2(4)` cases
([`PrimitiveSocleSymplecticSmallPrimaryClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleSymplecticSmallPrimaryClassBound.lean)).
The binary rank-four nonzero-vector stabilizer also has class count at
most `320`. Literal coordinates transport the sum `448 + 320 = 768`
to both the split and twisted eight-dimensional quadratic isometry
groups. The proved indices of the actual elementary images then give
class counts at most `1536` and `3072` for the original split and
twisted projective models. Their outer bounds and actual proper-index
lower bounds close both former rank-four binary cases
([`PrimitiveSocleOrthogonalBinaryRankFourClassBound`](SymmetricSubgroupAsymptotics/PrimitiveSocleOrthogonalBinaryRankFourClassBound.lean)).
The twenty-seven finite primitive models listed above and the remaining
imprimitive assembly are still open; the general published class-count
input is retained.

The ordinary-generator half-degree theorem is now proved for every
finite nilpotent permutation group, uniformly in the degree:
`PermutationNilpotentOrdinaryGenerators.exists_half_degree_generators`
constructs a finite generating set `S` with `2*S.card <= Nat.card X`
([`PermutationNilpotentOrdinaryGenerators`](SymmetricSubgroupAsymptotics/PermutationNilpotentOrdinaryGenerators.lean)).
The proof applies the prime-character rank bound and actual Burnside lifts
to each literal Sylow subgroup, then shares generators across the coprime
normal factors of the same group. It does not assume McIver--Neumann.
Independently, every actual transitive 2-group of degree `2^k` now has
ordinary generator rank at most
`sum_(j<k) choose(j, floor(j/2)) <= 2^k/sqrt(k)` for `k >= 1`.
Prime-index covers construct each binary block step on the original
point-stabilizer lattice; the actual top remains a 2-group. This proves
the retained coarse Tracey ceiling on the whole transitive 2-group branch,
without a Tracey, McIver--Neumann or supplied-chain premise
([`TransitiveBinaryGroupOrdinaryRecurrence`](SymmetricSubgroupAsymptotics/TransitiveBinaryGroupOrdinaryRecurrence.lean)).
The independent generator route also constructs a finite local-chief
compression trace on the original block action. Elementary layers pay
their proved least induced capacities; nonabelian layers pay the genuine
ordinary rank of a selected internal simple factor. The trace exists by
decreasing local-component order, and its successive quotients preserve
the actual correlated source. An unconditional finite enumeration supplies
the initial state, avoiding a circular use of the Tracey input. The proved
coarse aggregate is `2^(2*cost) <= |local component|^(number of blocks)`;
the elementary prime-power product also divides the actual local order.
On a prime-power top degree only its own characteristic receives the
growing binomial charge; other elementary characteristics cost at most
their actual dimensions. The literal affine translation head and the
complement's faithful general-linear embedding are retained separately;
the sharper numerical aggregate needed for general Tracey remains open
([`ActualWreathOrdinaryChiefRecurrence`](SymmetricSubgroupAsymptotics/ActualWreathOrdinaryChiefRecurrence.lean),
[`OriginalBlockOrdinaryCompressionState`](SymmetricSubgroupAsymptotics/OriginalBlockOrdinaryCompressionState.lean)).
The complete primitive-affine branch of the sharp ordinary-generator
induction is also proved, including every small degree, in
[`PrimitiveAffineOrdinaryInduction`](SymmetricSubgroupAsymptotics/PrimitiveAffineOrdinaryInduction.lean).
Its only induction premise is the literal sharp theorem at strictly
smaller degrees, with the full degree-three symmetric-group exception
preserved. The complement acts faithfully on nonidentity translations;
for odd characteristic, its action on inverse pairs has a kernel of
order at most two. The four-point base uses the actual three-point
complement and two proved generators of S4. No affine census is assumed.
This closes the affine branch, not the complete McIver--Neumann theorem.

The full intransitive branch is proved from the same strictly smaller-degree
induction premise
([`IntransitiveOrdinaryGeneratorInduction`](SymmetricSubgroupAsymptotics/IntransitiveOrdinaryGeneratorInduction.lean)).
A shared three-point fibre argument handles the symmetric-group exception.
The complete binary- and ternary-block branches are proved as well
([`BinaryBlockOrdinaryGeneratorInduction`](SymmetricSubgroupAsymptotics/BinaryBlockOrdinaryGeneratorInduction.lean),
[`TernaryBlockOrdinaryGeneratorInduction`](SymmetricSubgroupAsymptotics/TernaryBlockOrdinaryGeneratorInduction.lean)).
For binary blocks the actual kernel is a permutation module. For ternary
blocks the sign-compressed quotient acts faithfully on twice the number
of blocks, and its actual kernel is a monomial module over F3. A single
polynomial-orbit theorem bounds generators of every invariant subspace,
including coordinate-dependent scalar signs in arbitrary characteristic.
The remaining general imprimitive and nonaffine primitive branches are
still required for the global induction.
The prime-affine block branch is also complete for every odd prime and
every top action
([`PrimeAffineBlockOrdinaryGeneratorInduction`](SymmetricSubgroupAsymptotics/PrimeAffineBlockOrdinaryGeneratorInduction.lean)).
Its actual scalar quotient acts on `p-1` points per block, and the correlated
prime-field translation kernel uses the same monomial bound. The component
coordinates are constructed from the original affine profile.
The same branch is now proved for affine components of every odd prime-power
degree, using the actual inverse-pair quotient, its central binary sign
kernel and the prime-field translation module
([`OddAffineBlockOrdinaryGeneratorInduction`](SymmetricSubgroupAsymptotics/OddAffineBlockOrdinaryGeneratorInduction.lean)).
The shared vector-valued monomial theorem retains arbitrary invertible
local linear transport and bounds generators by the fiber dimension times
half the number of blocks. No extension-field module generator is counted
as a prime-field group generator without restriction of scalars.
For four-point blocks, actual affine coordinates and the literal
translation kernel also give the sharp ordinary-generator induction
when the displayed cubic kernel is zero or has at least two distinct
local kernel classes. For a single nonzero class, the actual scalar
centralizer and its one-or-two-orbit alternative give the required
kernel-generator bound. The two-block case uses an actual cyclic seed
and a proper/top subspace argument, keeping the larger group only as a
binary action. The three states are exhausted in
[`FourPointBlockOrdinaryGeneratorInduction`](SymmetricSubgroupAsymptotics/FourPointBlockOrdinaryGeneratorInduction.lean):
the full four-point imprimitive step is proved from the strictly smaller
ordinary-action induction hypothesis. This does not establish the
global generator input; other block types and the nonaffine primitive
branch remain.
The odd-block induction now also includes a three-point top whenever
the actual top image is proper, retaining the precise symmetric-group
exception. A separate actual-component-order argument proves the whole
binary-affine block tail in dimensions at least seven (fibre size at
least 128), including a full symmetric-group top on three points. The
finite binary-affine block degrees still open on this sharp half-degree track
are 16, 32 and 64
([`BinaryAffineBlockOrderTailOrdinaryGenerators`](SymmetricSubgroupAsymptotics/BinaryAffineBlockOrderTailOrdinaryGenerators.lean)).
An independent coarse-generator induction now pays **every binary-affine
block dimension and every actual top degree**. The original group, its
point degree and actual chief-order coefficients are retained; the top
need not be a 2-group. Its only generator premise is the coarse ceiling
for that genuinely smaller top action
([`OriginalBinaryAffineArbitraryTopOrdinaryStep`](SymmetricSubgroupAsymptotics/OriginalBinaryAffineArbitraryTopOrdinaryStep.lean)).
The shared bound `d(G) <= Omega(|G|)` charges the nonabelian chief factors.
Weighted costs from literal prime-power divisors and exact linear-order
divisibility pay the infinite ranges. Shared complementary-factor and
small-primary estimates reduce the remaining six dimensions to a finite
arithmetic exhaustion, now fully proved. No fitted aggregate, solvability
or small-group census remains in this binary-affine step.
A faithful-transitive coordinate transport derives its top premise from
ordinary generators of literal transitive subgroups in strictly smaller
degrees, then installs the result on the original block action
([`TraceyStrictlySmallerTransitiveActions`](SymmetricSubgroupAsymptotics/TraceyStrictlySmallerTransitiveActions.lean),
[`OriginalBinaryAffineCoarseDegreeInduction`](SymmetricSubgroupAsymptotics/OriginalBinaryAffineCoarseDegreeInduction.lean)).
This closes the binary-affine imprimitive branch of the independent
coarse induction. The odd-affine branch is also proved for every actual
local degree at least `11`
([`OriginalOddAffineLargeLocalOrdinaryStep`](SymmetricSubgroupAsymptotics/OriginalOddAffineLargeLocalOrdinaryStep.lean)).
Its actual translation head and complement quotient are charged
separately; faithful affine order bounds, uniform numerical bands and
a prime-power dimension exhaustion pay every top degree from the strictly
smaller transitive IH. The entire original degree-three block branch is
also proved by one correlated local-order-dividing-six recurrence,
using the same actual chief trace for both prime contributions
([`OriginalTernaryCoarseOrdinaryStep`](SymmetricSubgroupAsymptotics/OriginalTernaryCoarseOrdinaryStep.lean)).
The remaining local degrees `5`, `7` and `9` are now paid by one shared
literal-order multiplicity argument: the actual component orders divide
`20`, `42` and `432`. A uniform two-rate bound covers large primary
divisors, and exact arithmetic on the nontrivial divisors of `420` covers
the remaining scalar degrees. The resulting dispatcher closes the entire
original affine imprimitive branch for every prime, translation dimension
and top action, using only strictly smaller transitive cases
([`OriginalAffineArbitraryTopOrdinaryStep`](SymmetricSubgroupAsymptotics/OriginalAffineArbitraryTopOrdinaryStep.lean)).
The primitive-affine tail is also proved independently at every degree
`n>=1024`: the actual complement gives ordinary rank at most
`log_2(n)^2+1`, which a uniform dyadic estimate pays
([`PrimitiveAffineCoarseOrdinaryTail`](SymmetricSubgroupAsymptotics/PrimitiveAffineCoarseOrdinaryTail.lean)).
One checked table of 21 prime/dimension pairs pays every composite affine
degree below 1024 except binary dimensions two through five. These are
scalar order certificates, not action representatives or a group census
([`PrimitiveAffineCoarseBoundedParameters`](SymmetricSubgroupAsymptotics/PrimitiveAffineCoarseBoundedParameters.lean)).
The actual prime, four-point and eight-point bases are assembled with
these estimates. The last degrees `16` and `32` are now proved independently:
the original complement embeds faithfully in binary GL4 or GL5. An actual
order-four element saves one generator over the prime-multiplicity bound.
For GL4, proved simplicity, subgroup-order arithmetic and a 64-tuple
unitriangular certificate give complement rank at most seven. The original
affine groups therefore have rank at most eight and fifteen respectively.
The assembled theorem closes the entire primitive-affine coarse branch,
without a finite primitive catalogue
([`PrimitiveAffineSixteenOrdinaryGenerators`](SymmetricSubgroupAsymptotics/PrimitiveAffineSixteenOrdinaryGenerators.lean),
[`PrimitiveAffineThirtyTwoOrdinaryGenerators`](SymmetricSubgroupAsymptotics/PrimitiveAffineThirtyTwoOrdinaryGenerators.lean),
[`PrimitiveAffineCoarseOrdinaryComplete`](SymmetricSubgroupAsymptotics/PrimitiveAffineCoarseOrdinaryComplete.lean)).
The nonaffine primitive cases and global coarse-generator assembly remain open.
These proofs do not use the global Tracey or McIver--Neumann conclusion
to establish their own premise.
The simultaneous characteristic-primary and prime-to-characteristic
capacity fields also yield logarithmic coefficient `1`: the coupled
quadratic lcm entropy gives the squared budget `2/3+1/3=1`
([`TraceyQuadraticLcmEntropy`](SymmetricSubgroupAsymptotics/TraceyQuadraticLcmEntropy.lean),
[`InducedMinimumUnitLogarithmic`](SymmetricSubgroupAsymptotics/InducedMinimumUnitLogarithmic.lean)).
It is bound to the same actual chief trace with ordinary prime-multiplicity
costs, then to the original affine quotient; the resulting coefficient is
`d+Omega(|Component/V|)`. Literal linear-order divisibility proves these
costs, including `Omega(GL(3,3))=9`
([`OriginalAffineUnitMultiplicityCost`](SymmetricSubgroupAsymptotics/OriginalAffineUnitMultiplicityCost.lean),
[`OriginalAffineQuotientPrimeMultiplicity`](SymmetricSubgroupAsymptotics/OriginalAffineQuotientPrimeMultiplicity.lean)).
The nonaffine structural continuation now compresses the same original
full socle to cost at most `2*d(T)+d(G/socle(G))`, independently of its
factor count. It proves the actual one/two-minimal-normal cover first,
retains each supported factor's original coordinate and marks the actual
quotient lifts. The faithful least-index coset action supplies `d(T)`
from the strictly smaller transitive IH when that degree is smaller;
the almost-simple minimum-degree case remains explicit
([`PrimitiveSocleIsotypicOrdinaryCompression`](SymmetricSubgroupAsymptotics/PrimitiveSocleIsotypicOrdinaryCompression.lean),
[`SimpleLeastIndexStrictOrdinaryGenerators`](SymmetricSubgroupAsymptotics/SimpleLeastIndexStrictOrdinaryGenerators.lean)).
No simple two-generation or global generator bound is assumed in these
structural theorems.
The same actual quotient recurrence now pays primitive actions with at
least two socle factors and degree at least 1024, once that same simple
factor supplies its index-square and outer-order budgets
([`PrimitiveSocleMultipleFactorOrdinaryTail`](SymmetricSubgroupAsymptotics/PrimitiveSocleMultipleFactorOrdinaryTail.lean)).
This is an action-level installer; it does not remove those model-level
premises from the global endpoint. Independently, a literal prime-field
basis and the actual simple-root parameter homomorphisms give at most
`2*r*f` ordinary generators in the canonical quadratic elementary group
and its original norm-two projection. The pinned-field adapter retains
the actual Cartan equality; it does not identify the pinned natural PSL
model with a Serre model by name
([`CFSGNormTwoPrimePowerOrdinaryGenerators`](SymmetricSubgroupAsymptotics/CFSGNormTwoPrimePowerOrdinaryGenerators.lean)).
For a one-factor primitive group, a shared displayed-pair recurrence gives
ordinary rank at most `log_2(n)+5`. The actual pairs and local outer budgets
are now supplied internally for every valid untwisted classical A/B/C/D
model and the whole Suzuki family. A sharper dyadic estimate pays every
degree `n>=32`. The type-D rank-four outer budget stays in its proved
sufficient form; no stronger sharp bound is assumed
([`PrimitiveSocleClassicalABCOneFactorOrdinaryTail`](SymmetricSubgroupAsymptotics/PrimitiveSocleClassicalABCOneFactorOrdinaryTail.lean),
[`PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail`](SymmetricSubgroupAsymptotics/PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail.lean),
[`PrimitiveSocleSuzukiOneFactorOrdinaryTail`](SymmetricSubgroupAsymptotics/PrimitiveSocleSuzukiOneFactorOrdinaryTail.lean)).
These family results introduce no global simple two-generation assumption.
Integral outer prime multiplicity now removes the small-degree cutoff
for every displayed pair with the proved sufficient outer budget. Thus
every valid original A/B/C/D and Suzuki model, and every alternating
model, satisfies the one-factor coarse bound at all degrees. The rank-four
D case retains its sufficient outer bound throughout. The shared small-range proof uses integer-power logarithm
certificates, without an action census
([`PrimitiveSocleSharpPairFamiliesAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleSharpPairFamiliesAllDegreeOrdinary.lean),
[`PrimitiveSocleSufficientPairAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleSufficientPairAllDegreeOrdinary.lean)).
The original unitary one-factor branch is now proved for every admissible
rank, field and action degree. The large-degree estimate uses the actual
selected Sylow in the original derived fixed source. The bounded estimate
uses a common radical parameter map whose kernel lies in the actual
Frattini subgroup. Lifting through this map costs only the dimension of
its image. A genuine middle transvection supplies the missing coordinate
in binary ranks three and four. The resulting actual model heads are 4,
7 and 12 in binary ranks three, four and five; the rank-two head is at
most `2*f+1`. Scalar field-exponent bands pay all remaining degrees. Here
`TwistedA r` denotes the projective unitary model on `r+1` coordinates.
No action census or generating-pair premise is used
([`FrattiniSurjectiveOrdinaryGenerators`](SymmetricSubgroupAsymptotics/FrattiniSurjectiveOrdinaryGenerators.lean),
[`FrattiniThreeCoordinateShearOrdinaryGenerators`](SymmetricSubgroupAsymptotics/FrattiniThreeCoordinateShearOrdinaryGenerators.lean),
[`PrimitiveSocleUnitaryCompleteOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleUnitaryCompleteOrdinary.lean)).
The nonsplit-D, F4, G2, triality and positive-parameter Ree one-factor
branches are also complete at every degree. Their actual root-Sylow
orders, original outer bounds and genuine proper indices pay uniform
field-exponent bands, followed by the already proved infinite tails.
The exceptional E6/E7/E8 and twisted-E6 indices exclude their entire
bounded range internally
([`PrimitiveSocleTwistedDAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleTwistedDAllDegreeOrdinary.lean),
[`PrimitiveSocleFFourAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleFFourAllDegreeOrdinary.lean),
[`PrimitiveSocleGTwoAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleGTwoAllDegreeOrdinary.lean),
[`PrimitiveSocleTrialityAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleTrialityAllDegreeOrdinary.lean),
[`PrimitiveSocleReeFFourAllDegreeOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleReeFFourAllDegreeOrdinary.lean)).
The complete primitive-affine branch, every multifactor branch, and all
alternating/Lie models are now assembled on the original primitive
permutation action. Only literal Tits/sporadic factors remain. The
multifactor bounded proof uses the strictly smaller faithful simple coset
action, without a global simple two-generation premise
([`PrimitiveOrdinaryLieCFSGReduction`](SymmetricSubgroupAsymptotics/PrimitiveOrdinaryLieCFSGReduction.lean)).
The original nonaffine imprimitive step is likewise complete for every
alternating/Lie component, every local degree and every actual top. The
last binary unitary block uses its actual Frattini head 4. The installer
retains the same full socle quotient and chief trace; its only induction
calls concern strictly smaller transitive actions
([`OriginalNonaffineOrdinaryLieCFSGReduction`](SymmetricSubgroupAsymptotics/OriginalNonaffineOrdinaryLieCFSGReduction.lean)).
These steps are assembled for every transitive original permutation
action. A least-counterexample argument now proves that either the
coarse published input holds, or there is an actual least-degree failed
transitive action carrying a Tits/sporadic factor in its primitive
structure or its actual minimal-block component. No smaller-degree
induction or finite-model callback is a premise of this final disjunction
([`TraceyOrdinaryGlobalFiniteModelCounterexample`](SymmetricSubgroupAsymptotics/TraceyOrdinaryGlobalFiniteModelCounterexample.lean)).
Using the numerical callback already retained by the optional endpoint
above eliminates primitive multifactor failures and nonaffine block
failures of fibre degree at least 32. The displayed generating pairs
of twenty sporadic models now pay **every primitive degree and every
original block component/top**, including small actions. The remaining
primitive possibilities are Fi22/Fi23/Fi24' and the Baby Monster
below degree 64, Tits below degree 128, and the Monster. The primitive
J4 branch is now paid at every degree: its literal order-23 witness
excludes smaller actions, and bounding the actual outer order before
its logarithm pays the remaining degree-23 through degree-31 band
([`PrimitiveSocleJFourCompleteOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleJFourCompleteOrdinary.lean)).
The four Y-section presentations supply at most ten generators, and
the actual proved Tits order upper bound supplies at most 26; these
pay their respective tails. Thus **only the Monster remains in the
primitive branch from degree 128**. Original block fibres below 32
also exclude J4. Its actual order-23 witness forces one socle factor
and degree at least 23 in that band. One uniform three-generator-head
estimate, with at most five actual outer prime factors, pays every
inherited top. Both branches therefore retain just six tags: Tits,
Fi22, Fi23, Fi24′, Baby and Monster
([`OriginalNonaffineJFourSmallBlockOrdinaryStep`](SymmetricSubgroupAsymptotics/OriginalNonaffineJFourSmallBlockOrdinaryStep.lean)).
No known J4 order formula or action catalogue is assumed. The same numerical callback is
retained throughout, with no new rank hypothesis
([`TraceyOrdinarySevenModelResidual`](SymmetricSubgroupAsymptotics/TraceyOrdinarySevenModelResidual.lean),
[`CFSGJ4TwentyThreeDivisor`](SymmetricSubgroupAsymptotics/CFSGJ4TwentyThreeDivisor.lean)).
The original Y presentations now have a shared four-generator proof:
the central involution and three complete arm products recover every
individual generator by stripping one arm at a time. Actual arm periods
and coprime-product recovery improve the full-group heads to 3/2/3/3,
and their derived/full-centre heads to **4/2/4/4** for Fi22, Fi23, Fi24′
and Baby, respectively. No finite-model identification or order formula
is used
([`CFSGYCoprimeOrdinaryGenerators`](SymmetricSubgroupAsymptotics/CFSGYCoprimeOrdinaryGenerators.lean)).
The newest conditional refinement retains the same numerical callback
and failed action. The actual Fi23 pair now pays **every primitive degree
and every original block degree/top**. Fi22, Fi24′ and Baby remain only
below primitive degree 12 and original local degree 18. The actual seven-generator Tits head
and its order divisor leave primitive degrees 14 through 127 and local
degrees 14 through 17. Monster is unchanged. These are degree guards
on the retained witnesses, not a proof of the remaining finite-model
bounds or of the coarse input. The retained tags are therefore Tits,
Fi22, Fi24′, Baby and Monster
([`FischerTwentyThreeOrdinaryClosure`](SymmetricSubgroupAsymptotics/FischerTwentyThreeOrdinaryClosure.lean),
[`PrimitiveSocleYSectionOrdinaryFromTwelve`](SymmetricSubgroupAsymptotics/PrimitiveSocleYSectionOrdinaryFromTwelve.lean),
[`TraceyOrdinaryBoundedHeadModelResidual`](SymmetricSubgroupAsymptotics/TraceyOrdinaryBoundedHeadModelResidual.lean)).
The actual Tits four-generator theorem and proved outer bound now pay
**every primitive action and every original block row**, with only
strictly smaller transitive induction. Its least index is at least 14;
below local degree 32 there is one socle factor and at most two outer
prime factors, so one uniform four-head estimate pays the entire band.
The cumulative coarse residual therefore retains only **Fi22, Fi24′,
Baby and Monster**. The first three still require primitive degree below
12 or original local degree below 18; Monster is unrestricted. This
refinement takes only the existing sporadic numerical callback and CFSG,
and retains the same socle and action witnesses
([`PrimitiveSocleTitsCompleteOrdinary`](SymmetricSubgroupAsymptotics/PrimitiveSocleTitsCompleteOrdinary.lean),
[`OriginalNonaffineTitsCompleteOrdinaryStep`](SymmetricSubgroupAsymptotics/OriginalNonaffineTitsCompleteOrdinaryStep.lean),
[`TraceyOrdinaryFourSporadicResidual`](SymmetricSubgroupAsymptotics/TraceyOrdinaryFourSporadicResidual.lean)).
The finite-model estimates remain before the coarse input can be removed.
The separate small-degree sharp fields of the published bundle also
remain; T1's explicit assumptions have not changed.
Tits is now removed from the bounded sharp frontier too. The actual
four-generator and outer-multiplicity bounds give at most six generators
in every primitive Tits action of degree at most 21; its least index is
at least 14, which pays the exact sharp floor. The cumulative original
action reduction retains only sporadic witnesses. It preserves the
twelve exclusions on actual affine tops, the eleven on independent
global small-action witnesses, and the degree-eight witness behind the
primitive affine degree-16 case. Those distinct witnesses remain
explicit; no bounded-sharp input is inferred from the coarse ceiling
([`PrimitiveSocleTitsBoundedSharp`](SymmetricSubgroupAsymptotics/PrimitiveSocleTitsBoundedSharp.lean),
[`BoundedSharpTitsCompleteActualResidual`](SymmetricSubgroupAsymptotics/BoundedSharpTitsCompleteActualResidual.lean)).
The degree-eight affine block is now complete independently: every
actual subnormal subgroup of its primitive local component has ordinary
generator rank at most three. Literal translation charts absorb the
actual linear conjugator, and the checked models of orders 7, 21 and
168 supply the inherited action and irreducibility. The resulting block
installer uses only the strictly smaller-degree induction premise
([`PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators`](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators.lean)).
There is also a shared-dependency reduction: the unchanged coarse Tracey
permutation input pays the sharp ordinary bound in every transitive
degree at least 22 and in every even degree at least 16. Strong induction
and the proved intransitive step reduce the full McIver--Neumann input
to transitive degrees below 16 or equal to 17, 19 or 21
([`McIverNeumannFromTraceyBounded`](SymmetricSubgroupAsymptotics/McIverNeumannFromTraceyBounded.lean)).
Under that unchanged coarse input, the unpaid imprimitive possibilities
have nonaffine fibre/top degrees `(6,2)`, `(5,3)` and `(7,3)`; the latter
two require the actual full symmetric three-point top. This degree list
is not a classification of its actions. The bounded primitive nonaffine
branch for this sharper bound also remains open.
The separately defined published-2018 bundle above pays these remaining
cases through its sharper floor field. That consolidates published
inputs; proving the bundle from CFSG remains a separate obligation.

Two further shared ordinary-generation lemmas are proved. A group
actually generated by a Sylow subgroup and one conjugate needs at most
one generator beyond that Sylow subgroup; an odd-prime good-Sylow witness
therefore pays the half-degree bound from degree six. For an original
index-form product action with at least two socle factors, an existing
component **order** cube pays the half-degree bound for every subgroup,
including the full factorial cost
([`GoodSylowPermutationOrdinaryGenerators`](SymmetricSubgroupAsymptotics/GoodSylowPermutationOrdinaryGenerators.lean),
[`PrimitiveSocleProductOrdinaryGenerators`](SymmetricSubgroupAsymptotics/PrimitiveSocleProductOrdinaryGenerators.lean)).
The general nonnilpotent ordinary-generator input is still retained.

For a homogeneous minimal normal subgroup, ordinary generators of one
literal coordinate factor and lifts of generators of the ambient quotient
generate the original group
([`MinimalNormalPowerOrdinaryGenerators`](SymmetricSubgroupAsymptotics/MinimalNormalPowerOrdinaryGenerators.lean)).
The proof retains the factor's internal normality and its full ambient
normal closure. It does not identify normal generation with ordinary
generation for an arbitrary perfect kernel.

The original F4 integral Serre lattice is now proved equal to the Z-span
of the displayed 52 divided-power vectors
([`CFSGFFourOriginalIntegralSpan`](SymmetricSubgroupAsymptotics/CFSGFFourOriginalIntegralSpan.lean)).
A shared sparse induction proves every signed source action from the
original Serre relations. Integer half-square coefficients and cubic
nilpotence then prove stability under every divided power, so the defining
minimality of the same original lattice gives spanning. Genuine integer
root and Cartan coordinates now give a left inverse for the actual matrix
images. The resulting split injection survives scalar extension over every
commutative ring, proving faithfulness of the original image representation
over every field
([`CFSGFFourOriginalBaseChangeFaithful`](SymmetricSubgroupAsymptotics/CFSGFFourOriginalBaseChangeFaithful.lean)).
In characteristic two, the original model is now identified with the
literal folded matrix group, whose center is proved trivial. The
exceptional automorphism transfers along this equivalence with its exact
signed root parameters and its square equal to field Frobenius
([`CFSGFFourOriginalExceptionalModel`](SymmetricSubgroupAsymptotics/CFSGFFourOriginalExceptionalModel.lean)).
This argument does not assume simplicity of an ambient ordinary F4
group. The later original ReeF4 results below discharge that family's
model callbacks. The Tits index square, two-Sylow generation and
outer-order budget are also proved below.
For every ReeF4 parameter, including the Tits value, the actual positive
intersection with the derived fixed source is now Sylow there. A bound
on the same abelian image gives intersection order at least `q^9`;
disjoint opposed images in the full derived-centre quotient give actual
model order at least `q^18`, hence Tits order at least 262144. A literal
surviving positive 2-subgroup, with the stronger binary saving proved
below, now proves that **2048 divides the Tits order**. Since 2048 does
not divide `13!`, every faithful Tits action has degree at least 14;
the same obstruction excludes a Tits simple socle factor on at most
thirteen points
([`PrimitiveSocleThirteenPointTitsExclusion`](SymmetricSubgroupAsymptotics/PrimitiveSocleThirteenPointTitsExclusion.lean)). A literal
middle root/Weyl word also has order five in the derived fixed source
and now in its **actual full-centre quotient**, including Tits. A checked
single-vector action detects noncommutation with an element of that
same derived source, proving noncentrality before quotienting. Its
conjugation action also has order five on a literal normal graded
2-kernel and on that kernel's faithful image in the full-centre
quotient. A generic finite 2-group argument proves that its fixed
subgroup has index at least 16 in this kernel. This is an internal
centralizer bound, not a bound for arbitrary point stabilizers in the
whole Tits group. The later parabolic argument proves the Tits index
square; the later generation argument closes its good-Sylow case, and the
finite retained-word argument below proves its outer-order budget
([`CFSGReeFFourAllParameterOrderLower`](SymmetricSubgroupAsymptotics/CFSGReeFFourAllParameterOrderLower.lean),
[`CFSGReeFFourMiddleDerivedFiveSurvival`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleDerivedFiveSurvival.lean),
[`CFSGReeFFourMiddleFiveFixedIndex`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleFiveFixedIndex.lean)).
At field order two, the literal middle parabolic has a normal 2-kernel
and an actual graded image of order at most 20. Its displayed generators
satisfy `r^5 = y^4 = 1` and `y*r*y^-1 = r^2`, proving that image soluble.
The parabolic, its actual derived intersection and its full-centre
quotient image are therefore soluble
([`CFSGReeFFourBinaryMiddleParabolicSolvable`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryMiddleParabolicSolvable.lean)).
For the same positive subgroup `S <= U` with order at least 512 and
normalized by `U`, the actual Bruhat cover now puts its normalizer in
**one of the two original minimal parabolics**. Exact full positive
intersections exclude the short Weyl words of weight at least four;
the literal squares exclude both length-two words. Subgroup-union
containment selects a parabolic. The outer parabolic is now also
proved soluble: its normal graded 2-kernel has an actual associated
image of order at most six, contained in the raw image of the literal
soluble constant subgroup. Applying the cover to the actual `U ∩ D`
and descending its normalizer through the full derived-centre quotient
therefore constructs **an actual Tits Sylow 2-subgroup with soluble
normalizer, with no hypotheses**. Further generation and numerical
steps retain that same actual Sylow and full quotient
([`CFSGReeFFourBinarySylowNormalizerSolvable`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinarySylowNormalizerSolvable.lean)).
A checked literal selected-root commutator now puts the square of the
displayed middle order-four element in the actual derived subgroup,
with the same original fixed-model words. At field order two, every
abelian image consequently has at most four elements
([`CFSGReeFFourMiddleSquareCommutator`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleSquareCommutator.lean),
[`CFSGReeFFourBinaryMiddleSquareSaving`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryMiddleSquareSaving.lean)).
A second whole-block identity now puts the original outer involution
in the derived subgroup. Its proof replays two finite root words and
compares their common literal normal form before returning through
the faithful original fixed-group map. Only whole fixed blocks and
their derived square corrections are used. The abelianization now has
at most two elements, and the actual positive-derived intersection
and its faithful Tits image each have at least 2048 elements
([`CFSGReeFFourInnerBracketCommutator`](SymmetricSubgroupAsymptotics/CFSGReeFFourInnerBracketCommutator.lean),
[`CFSGReeFFourBinaryOuterSaving`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryOuterSaving.lean)).
Restricting the actual middle parabolic to the derived group and
mapping it through the full central quotient gives index at most
1755. Its soluble image is proper under inherited nonabelian
simplicity. The opposed derived Sylows give order at least `2048^2`,
and `1755^2 < 2048^2` proves the Tits least-index square. No containment
of the whole quotient kernel in that parabolic is assumed. The
outer-automorphism bound remains separate
([`CFSGTitsOriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGTitsOriginalIndexSquare.lean)).
This is threaded through both T1 and AllTargets: the Tits numerical
payload now asks only for its outer-order budget. The four published
bundles, CFSG, the remaining good-Sylow cases and the sporadic numerical
payloads remain explicit
([`CFSGSevenTargetsTitsIndexSquare`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsTitsIndexSquare.lean)).
The two actual opposed derived Sylows now generate the whole derived
fixed group. A generic Schreier argument retains the positive-derived
intersection and the two Weyl involutions; the odd three- and five-product
relations recover both involutions from the positive and negative
intersections. Sylow conjugacy supplies an internal conjugator without
assuming that ambient opposition belongs to the derived group. The soluble
normalizer and generation descend through the **full** central quotient,
proving the actual Tits good-Sylow witness. The newest T1 and AllTargets
exports therefore remove Tits from that callback
([`CFSGReeFFourBinaryDerivedOppositeGeneration`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryDerivedOppositeGeneration.lean),
[`CFSGReeFFourBinaryConditionalGoodSylow`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryConditionalGoodSylow.lean),
[`CFSGSevenTargetsTitsGoodSylow`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsTitsGoodSylow.lean)).
A separate generic Schreier count bounds the derived group's ordinary
generator number by `2*d+1` when the original group is generated by `d`
derived elements and one element whose square is derived. Applying it
to the three actual derived generators and the displayed order-four
element gives seven ordinary generators for the actual Tits model,
through the full central quotient. The whole-word relations below sharpen
this to **four ordinary generators**. The generator count alone does not
bound its outer quotient
([`DerivedOneCosetOrdinaryGenerators`](SymmetricSubgroupAsymptotics/DerivedOneCosetOrdinaryGenerators.lean),
[`CFSGTitsSevenOrdinaryGenerators`](SymmetricSubgroupAsymptotics/CFSGTitsSevenOrdinaryGenerators.lean)).
The separate outer-bound route now proves that disjoint actual derived
Sylow pairs can be aligned by conjugation in the **full fixed group**.
Every non-opposite relative position has a nontrivial derived intersection;
the exceptional next-to-longest position retains the whole original outer
involution. The aligning element is not asserted to lie in the derived
group. Actual quotient Sylows are lifted separately through the full centre,
and their images are aligned without lifting an automorphism. The resulting
count proves `|Out(Tits)| <= 2*|pairStabilizer|`. The actual least index is
at least 14. The finite coordinate certificate below now proves
`|pairStabilizer| <= 3`, hence `|Out(Tits)| <= 6` and the full sufficient
outer budget; no pair-stabilizer hypothesis is retained
([`CFSGReeFFourBinaryDerivedPairAlignment`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryDerivedPairAlignment.lean),
[`CFSGTitsAmbientPairAlignment`](SymmetricSubgroupAsymptotics/CFSGTitsAmbientPairAlignment.lean),
[`CFSGTitsPairStabilizerOuterBound`](SymmetricSubgroupAsymptotics/CFSGTitsPairStabilizerOuterBound.lean)).
The coordinate proof of this finite bound has an actual
twelve-Boolean ordered cover, literal matrix-prefix semantics and
proved global commutator entries. Three literal probe words cut their
common centralizer in the actual positive group down to at most two
elements: commuting forces eleven of the twelve ordered coordinates
to vanish. All probes belong to the actual positive-derived intersection.
Its centre therefore has order exactly two, and this equality descends
through the full central quotient to the actual Tits Sylow subgroup.
The same literal Bruhat intersections, together with the checked
2048-element lower bound, identify the normalizer of the derived-positive
intersection in the full fixed group with the whole positive group.
After passage to the derived group and its full central quotient, the
actual Tits Sylow subgroup is self-normalizing.
The two intrinsic opposed centre involutions also recover an actual
reflection: their product has order five, and the odd-dihedral word
recovers the same element in the full derived-centre quotient. Every
actual pair stabilizer fixes this reflection. Its conjugate Sylow
intersection is identified inside the original derived group, without
declaring the ambient cyclic-four subgroup characteristic or lifting
an automorphism to it
([`CFSGTitsCentralReflection`](SymmetricSubgroupAsymptotics/CFSGTitsCentralReflection.lean),
[`CFSGReeFFourBinaryReflectionMiddleFlag`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryReflectionMiddleFlag.lean)).
The two intrinsic quotient flags embed back into the corresponding
original middle cyclic-four subgroups. Their unique involutions are
fixed without asserting that those ambient groups are characteristic.
A second order-five recovery then fixes the actual middle Weyl element
and opposition element
([`CFSGTitsIntrinsicMiddleSquare`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicMiddleSquare.lean),
[`CFSGTitsOpposedMiddleSquare`](SymmetricSubgroupAsymptotics/CFSGTitsOpposedMiddleSquare.lean),
[`CFSGTitsMiddleWeylRecovery`](SymmetricSubgroupAsymptotics/CFSGTitsMiddleWeylRecovery.lean)).
The actual intersection `R = P ∩ w_m⁻¹ P w_m` is now identified with
the image of the same original positive graded-kernel intersection.
It is an invariant normal 2-subgroup of the intrinsic carrier
`M = ⟨P,w_m⟩`. No equality with the full 2-core or a prescribed
elementary-abelian head is assumed
([`CFSGReeFFourMiddlePositiveKernelIntersection`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddlePositiveKernelIntersection.lean),
[`CFSGTitsIntrinsicMiddleRadical`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicMiddleRadical.lean)).
The actual order-five element of `M` now acts faithfully on this same
`R`. A first-layer homomorphism is constructed through the faithful
source intersection; its kernel contains commutators and squares.
The final finite count uses these containments directly; it requires
neither reverse inclusion, characteristicity of this kernel, nor a
prescribed Frattini-head dimension
([`CFSGTitsIntrinsicFiveFaithful`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicFiveFaithful.lean),
[`CFSGTitsIntrinsicFirstLayer`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicFirstLayer.lean)).
The whole middle commutator now has the same second graded layer as its
literal `D*E` correction. Dividing by that whole correction leaves an
actual element of this same `R` whose matrix entries vanish through
height two. The whole middle difference and the two middle squares
also lie in `R`; this does not assert that the unsquared middle blocks
lie there, or that their squares are squares of elements of `R`
([`CFSGReeFFourMiddleTailCommutatorSecondLayer`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleTailCommutatorSecondLayer.lean),
[`CFSGTitsIntrinsicThirdCorrection`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicThirdCorrection.lean),
[`CFSGTitsIntrinsicMiddleCorrections`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicMiddleCorrections.lean)).
The actual radical has between 512 and 1024 elements. Literal root and
wedge-coordinate actions also prove the whole-word relation
`y*x*y⁻¹ = r*x*r⁻¹`, retaining every higher matrix term. These results
constrain the next generation and automorphism steps without specifying
a Frattini-head dimension
([`CFSGTitsIntrinsicRadicalCardinalityBounds`](SymmetricSubgroupAsymptotics/CFSGTitsIntrinsicRadicalCardinalityBounds.lean),
[`CFSGReeFFourWholeOuterMiddleRelation`](SymmetricSubgroupAsymptotics/CFSGReeFFourWholeOuterMiddleRelation.lean)).
The middle element also commutes with the negative outer root, by twelve
actual E6 root pairings. This recovers the remaining Schreier conjugate
and proves that `x, w_o, w_m, y^2` generate the actual derived group and
Tits. Intrinsic opposition recovers `w_o` from `x`; the other two generators
are already fixed by the pair stabilizer. Evaluation at the actual outer
root therefore determines such an automorphism. Self-normalization also
puts the full central quotient kernel inside the positive Sylow, where
the quotient is injective. The derived centre is consequently trivial.
Under the existing simple-model hypothesis, the genuine 26-dimensional
representation is faithful because it is nontrivial on the outer root
([`CFSGTitsFourOrdinaryGenerators`](SymmetricSubgroupAsymptotics/CFSGTitsFourOrdinaryGenerators.lean),
[`CFSGTitsPairStabilizerOuterEvaluation`](SymmetricSubgroupAsymptotics/CFSGTitsPairStabilizerOuterEvaluation.lean),
[`CFSGTitsDerivedCentralQuotientEquivalence`](SymmetricSubgroupAsymptotics/CFSGTitsDerivedCentralQuotientEquivalence.lean),
[`CFSGTitsSimpleNormFaithfulness`](SymmetricSubgroupAsymptotics/CFSGTitsSimpleNormFaithfulness.lean)).
The exact ordered cover gives ten free bits for each possible outer-root
image. Its original involution, retained-centralizer and opposed-product
relations transfer to the proved faithful norm action. A kernel-checked
compact binary-matrix certificate classifies all 1024 masks: exactly
`64, 512, 864` satisfy the necessary conditions. The literal source word
and the proved evaluation injection give at most three elements in the
actual opposed-pair stabilizer, hence `|Out(Tits)| <= 6`. This proves
the Tits outer budget and removes Tits from the
optional T1 and AllTargets numerical callback
([`CFSGReeFFourPackedTailClassification`](SymmetricSubgroupAsymptotics/CFSGReeFFourPackedTailClassification.lean),
[`CFSGTitsCompleteOuterBudget`](SymmetricSubgroupAsymptotics/CFSGTitsCompleteOuterBudget.lean),
[`CFSGSevenTargetsTitsComplete`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsTitsComplete.lean)).
The original-group coordinate and centralizer ingredients are proved in
([`CFSGReeFFourBinaryOrderedBooleanParameters`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryOrderedBooleanParameters.lean),
[`CFSGReeFFourBinaryOrderedPrefixMatrices`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryOrderedPrefixMatrices.lean),
[`CFSGReeFFourBinaryFirstGlobalEntry`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryFirstGlobalEntry.lean),
[`CFSGReeFFourDerivedPositiveFourProbes`](SymmetricSubgroupAsymptotics/CFSGReeFFourDerivedPositiveFourProbes.lean),
[`CFSGReeFFourBinaryPositiveCommonCentralizer`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryPositiveCommonCentralizer.lean),
[`CFSGReeFFourBinaryPositiveCentre`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryPositiveCentre.lean),
[`CFSGReeFFourBinaryExactPositiveNormalizer`](SymmetricSubgroupAsymptotics/CFSGReeFFourBinaryExactPositiveNormalizer.lean),
[`CFSGTitsPositiveSelfNormalizer`](SymmetricSubgroupAsymptotics/CFSGTitsPositiveSelfNormalizer.lean)).
The pinned ReeF4 and Tits definitions are now bound to the literal fixed
group of this automorphism, retaining the actual derived subgroup and
its full-center quotient
([`CFSGReeFFourFixedModelEquivalence`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedModelEquivalence.lean)).
Actual collected middle-root words now construct a subgroup of order
`q^2` inside that literal fixed group, with injective parameters and
proved multiplication and inverse laws. This bounded subgroup is not
asserted to be the whole positive group or its derived-center quotient
([`CFSGReeFFourMiddleFixedSubgroup`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleFixedSubgroup.lean)).


Actual relative Weyl words now conjugate the literal fixed positive
subgroup onto the fixed negative subgroup, including the exact pinned
transport. A constructed fixed-positive element has all six ambient
simple-root leading coordinates equal to one
([`CFSGReeFFourOppositionFixedPositiveNegative`](SymmetricSubgroupAsymptotics/CFSGReeFFourOppositionFixedPositiveNegative.lean),
[`CFSGReeFFourRegularFixedPositive`](SymmetricSubgroupAsymptotics/CFSGReeFFourRegularFixedPositive.lean)).
The literal fixed-positive subgroup is also proved Sylow in the full
fixed group, with soluble normalizer, by its faithful ambient preimage
and that regular element
([`CFSGReeFFourFixedPositiveSylow`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedPositiveSylow.lean)).
For Ree field order `q >= 8`, an actual torus commutator constructs a
regular positive element in the derived subgroup itself. Its preimage
gives a Sylow subgroup with soluble normalizer in the pinned original
Ree model. Disjoint opposed Sylows prove that the positive subgroup
injects through the full-center quotient
([`CFSGReeFFourOriginalPositiveSylow`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalPositiveSylow.lean),
[`CFSGReeFFourPositiveCentralQuotient`](SymmetricSubgroupAsymptotics/CFSGReeFFourPositiveCentralQuotient.lean)).
Whole-positive stability under the exceptional automorphism and the
original Bruhat-cell cover are also proved, without assuming that four
simple root charts generate the whole positive group. Generation of
the full fixed group and passage to the original derived-centre model
are now proved below for `m > 0`; the Tits field-order-two case remains separate.
The word action in every actual fixed Bruhat cell is now generated by
the two paired words. The proof uses three- and six-step inversion drops
and preserves the actual reversed-letter action. Equal word actions
leave a literal diagonal-normalizer residual. Unique positive/inversion
and positive/diagonal coordinates descend fixedness to the original
factors. The retained original diagonal group is now proved to equal
the constructed four-unit torus in characteristic two. Its exceptional
fixed elements are exactly the constructed two-unit torus words. The
proof matches the actual simple-root scalars through the integral
inverse of the relative Cartan map and proves their action faithful;
it uses no ordinary-F4 simplicity input. The outer Weyl and torus words
lie in the group generated by the two opposite unipotent groups.
The fixed diagonal has exactly `(2^(2*m+1)-1)^2` elements. It normalizes
both literal opposite unipotent groups, and the actual middle Weyl word
inverts the middle torus. Surjectivity of squaring in this characteristic-two
torus then reduces its membership to middle Weyl membership. A constant
middle Weyl identity has now been checked on all 26 coordinates of the
faithful norm model and transported to the same original F4 model.
Its conjugated factor lies in the actual negative subgroup, proved from
the root-degree cone. Together with the fixed Bruhat cover, this proves
`fixedPositive m ⊔ fixedNegative m = ⊤` for every `m`, including zero
([`CFSGReeFFourFixedWordClassification`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedWordClassification.lean),
[`CFSGReeFFourUniqueInversionCells`](SymmetricSubgroupAsymptotics/CFSGReeFFourUniqueInversionCells.lean),
[`CFSGReeFFourFixedDiagonalTorus`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedDiagonalTorus.lean),
[`CFSGReeFFourFixedDiagonalCardinality`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedDiagonalCardinality.lean),
[`CFSGReeFFourMiddleTorusSquareReduction`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleTorusSquareReduction.lean),
[`CFSGReeFFourMiddleTorusInversion`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleTorusInversion.lean),
[`CFSGReeFFourFixedOppositeGeneration`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedOppositeGeneration.lean)).
For `m > 0`, actual torus conjugation acts diagonally on each literal
positive height quotient, and every root character is proved nontrivial,
including a checked field-order-eight base. One common finite odd torus
average constructs a genuine product of commutators with the same entire
coordinate vector. Peeling the exact kernels proves that the full
positive subgroup lies in the derived subgroup. Consequently the fixed
group is perfect and the good-Sylow data descends through its full-centre
quotient to the original Ree model
([`CFSGReeFFourPositiveDerived`](SymmetricSubgroupAsymptotics/CFSGReeFFourPositiveDerived.lean),
[`CFSGReeFFourOriginalGoodSylow`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalGoodSylow.lean)).
The field-order-two Tits derived subgroup remains separate.
The actual outer and middle fixed inversion blocks have now been counted:
their cardinalities are `q` and `q^2`. The equalities hold inside the
original fixed group for every parameter, including field order two
([`CFSGReeFFourOuterFixedInversion`](SymmetricSubgroupAsymptotics/CFSGReeFFourOuterFixedInversion.lean),
[`CFSGReeFFourMiddleFixedInversion`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleFixedInversion.lean)).
Eight genuine opposed-subgroup peels now count the whole positive group:
`|U| = q^12`. Every recursive residual retains all earlier intersection
conditions; the actual final opposition makes the terminal residual trivial
([`CFSGReeFFourFixedPositiveCardinality`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedPositiveCardinality.lean)).
The sixteen short paired-word actions give a cover retaining the actual
fixed diagonal residual. Its right-factor costs sum to
`(1+q)*(1+q^2)*(1+q^3)*(1+q^6)`. Together with the exact diagonal order
`(q-1)^2`, the weighted cover proves an order ceiling `q^26` for the full
fixed group and its original derived-center quotient, including at field
order two. This uses no simplicity or perfectness premise
([`CFSGReeFFourWeightedFixedOrderUpper`](SymmetricSubgroupAsymptotics/CFSGReeFFourWeightedFixedOrderUpper.lean)).
For positive parameters, the two opposed Sylows also give
`q^24 <= |ReeF4(q)|` in the original full-center quotient. The proved
central p-element argument preserves their mutual disjointness there
([`CFSGReeFFourOriginalOrderLower`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalOrderLower.lean)).
The later signed-root argument below proves the ReeF4 outer-order bound.
The whole positive-parameter primitive class-count branch is closed as
recorded above; Tits two-Sylow generation and its outer-order budget are
also proved above.
An actual outer-root translation and its square-scalar torus action now
give `q <= [S : H]` for every proper subgroup of the original simple ReeF4
model, for `m > 0`
([`CFSGReeFFourPermutationDegree`](SymmetricSubgroupAsymptotics/CFSGReeFFourPermutationDegree.lean)).
An actual proper middle parabolic, transported with the full quotient
kernel retained, now gives least proper index at most
`(1+q)*(1+q^3)*(1+q^6)`. Its square is strictly below the original-model
order lower bound `q^24`, proving the required least-index square
([`CFSGReeFFourOriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalIndexSquare.lean)).
For the outer-order proof below, every automorphism of the original ReeF4
quotient can now be adjusted by an inner automorphism to preserve the
literal positive and negative Sylow images
([`CFSGReeFFourOriginalPairAlignment`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalPairAlignment.lean)).
Their normalizers intersect in the actual fixed diagonal subgroup.
The two simple paired Weyl elements also give an exhaustive, distinct
minimal-parabolic family above the actual Borel
([`CFSGReeFFourMinimalParabolics`](SymmetricSubgroupAsymptotics/CFSGReeFFourMinimalParabolics.lean)).
Intersecting the original Sylows with the opposite minimal parabolics
recovers both signed simple root blocks intrinsically. Their orders `q`
and `q^2` distinguish the two labels. Thus the adjusted automorphism
preserves all four literal signed blocks
([`CFSGReeFFourOriginalSignedRootAction`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalSignedRootAction.lean)).
The actual middle block is also identified with the existing Suzuki
unipotent coordinate group, and reversing the eight actual peels proves
that the two positive blocks together with the two simple Weyl elements
generate the positive Sylow. These statements identify the unipotent
coordinates, not the whole Suzuki rank-one group
([`CFSGReeFFourMiddleSuzukiCoordinates`](SymmetricSubgroupAsymptotics/CFSGReeFFourMiddleSuzukiCoordinates.lean),
[`CFSGReeFFourSimpleBlockPeelingGeneration`](SymmetricSubgroupAsymptotics/CFSGReeFFourSimpleBlockPeelingGeneration.lean)).
The four signed simple blocks now generate the same original quotient,
so agreement on them implies equality of original homomorphisms or
automorphisms
([`CFSGReeFFourOriginalSignedBlockGeneration`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalSignedBlockGeneration.lean)).
The positive outer-root action and the first coordinate of the actual
Suzuki middle block are now proved semilinear. Surjectivity of the
actual pair of torus scalars adjusts both scalar coefficients to one by
one original inner automorphism
([`CFSGReeFFourOriginalPositiveNormalization`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalPositiveNormalization.lean)).
The adjusted action is now proved to use one common field automorphism
on the positive outer-root block and the middle first coordinate
([`CFSGReeFFourOriginalCommonPositiveField`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalCommonPositiveField.lean)).
The coupling uses the actual outer Weyl image in its diagonal coset,
faithful original torus scalar coordinates, and the generic
shear-reflection rigidity theorem. No field-coupling hypothesis remains
in this result.
The full positive middle action is also proved to be entrywise application
of this same field automorphism, by the faithful first-coordinate
normalizer map
([`CFSGReeFFourOriginalCommonPositiveActions`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalCommonPositiveActions.lean)).
For the outer pair, the actual three-factor Weyl identity forces the
negative parameter at one, and Weyl conjugation then proves the same
field action on the entire negative outer block
([`CFSGReeFFourOriginalSignedOuterField`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalSignedOuterField.lean)).
Unique actual Bruhat factors and the proved trivial positive torus
centralizer also identify every fixed diagonal-normalizing element as
a diagonal times a genuine paired Weyl word
([`CFSGReeFFourFixedDiagonalNormalizer`](SymmetricSubgroupAsymptotics/CFSGReeFFourFixedDiagonalNormalizer.lean)).
The actual negative middle block is also identified with the native
Suzuki unipotent group. Its induced action normalizes the literal torus
and is proved to act by a scalar times a field automorphism on its first
coordinate
([`CFSGReeFFourOriginalNegativeMiddleSemilinear`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalNegativeMiddleSemilinear.lean)).
Its field is now proved equal to the common positive field, using the
actual negative torus character, the exact original torus field action
and surjectivity of the literal middle scalar on the slice `T(1,b)`
([`CFSGReeFFourOriginalNegativeMiddleField`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalNegativeMiddleField.lean)).
The remaining negative middle scalar is now proved equal to one
([`CFSGReeFFourOriginalSignedMiddleField`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalSignedMiddleField.lean)).
The image of the actual middle Weyl element lies in its diagonal coset.
A genuine residual word therefore belongs to the original diagonal,
whose off-diagonal matrix entry is zero. The same entry is proved to be
`c+c^2` by 68 kernel-checked sparse polynomial transitions. Since `c`
is a unit in characteristic two, this forces `c=1`.
All four signed root blocks consequently have the same full field
map, and they generate the original group. Counting actual inner-normalized
automorphisms by that map proves `|Out| <= 2*m+1`
([`CFSGReeFFourOriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGReeFFourOriginalOuterBound.lean)).
The original proper-index lower bound then gives the full outer budget,
now threaded through T1 and AllTargets
([`CFSGSevenTargetsReeFFourOuter`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsReeFFourOuter.lean)).
No automorphism lift to the ambient F4 group is assumed. The Tits
outer-order budget is proved by the finite retained-word argument above.

For the original simple G2 model over every finite field with `q >= 3`,
the natural root group is now proved equivalent to that same model.
Its literal singular-ray action gives `ell < 3*q^5`, and the actual
long-node torus gives `q <= ell` for every least proper index `ell`
([`CFSGGTwoIndexPointUpper`](SymmetricSubgroupAsymptotics/CFSGGTwoIndexPointUpper.lean),
[`CFSGGTwoPermutationDegree`](SymmetricSubgroupAsymptotics/CFSGGTwoPermutationDegree.lean)).
The natural-image kernel and natural centre are both discharged, including
characteristics two and three. Disjoint actual Sylow images with six
independent field parameters also give `q^12 <= |G|` on the same original
model, proving `ell^2 < |G|`, including `q=3`
([`CFSGGTwoOriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGGTwoOriginalIndexSquare.lean)).
The actual signed-root stabilizer now has one common field automorphism
and reciprocal scalars. Counting its parameters modulo the original
product torus gives `|Out| <= 2*f` for `q = p^f`, including characteristic
three with its possible root swap
([`CFSGGTwoD4GeckOriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGGTwoD4GeckOriginalOuterBound.lean)).
Together with `q <= ell`, this proves the full outer-order budget.
Both bounds are threaded through the optional T1 endpoint, removing G2
from its residual model callbacks. No abstract automorphism lift or
model-recognition input is retained.

The Ree continuation now has proved Frobenius parameter arithmetic on
the original field, together with the corresponding scalar tuples
([`CFSGReeGTwoFieldParameters`](SymmetricSubgroupAsymptotics/CFSGReeGTwoFieldParameters.lean),
[`CFSGReeGTwoFixedScalarTuples`](SymmetricSubgroupAsymptotics/CFSGReeGTwoFixedScalarTuples.lean)).
On the original rational G2 Serre quotient, fourteen explicit integral
vectors span the entire Lie algebra
([`CFSGGTwoOriginalFourteenFamily`](SymmetricSubgroupAsymptotics/CFSGGTwoOriginalFourteenFamily.lean)).
The integral divided-power equations also prove the required vanishing
on the second root-string vector after characteristic-three base change
([`CFSGGTwoOriginalCharacteristicThreeString`](SymmetricSubgroupAsymptotics/CFSGGTwoOriginalCharacteristicThreeString.lean)).
Fourteen unit-entry matrix coordinates now prove a complete integral
basis and its base change in every field. The same original tensor
action is faithful, giving an unconditional equivalence of the original
G2 group with its native matrix group and, for field order at least
three, its projective version
([`CFSGGTwoOriginalIntegralBasis`](SymmetricSubgroupAsymptotics/CFSGGTwoOriginalIntegralBasis.lean),
[`CFSGGTwoOriginalFieldBasis`](SymmetricSubgroupAsymptotics/CFSGGTwoOriginalFieldBasis.lean),
[`CFSGGTwoOriginalProjectiveNaturalEquivalence`](SymmetricSubgroupAsymptotics/CFSGGTwoOriginalProjectiveNaturalEquivalence.lean)).
This bridge does not assume simplicity of the ordinary G2 model.
All signed divided-power coefficients now prove the actual exceptional
root covariance on this original tensor space. Its seven-dimensional
quotient yields an automorphism of the whole original G2 group. Composing
it with the field automorphism gives the exact involution prescribed by
the pinned ReeG2 model, whose literal twist graph is proved to be the
graph of that involution
([`CFSGReeGTwoOriginalAutomorphism`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalAutomorphism.lean),
[`CFSGReeGTwoOriginalGraph`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalGraph.lean)).
The signed six-root collecting law now binds the division-free
three-parameter chart to a genuine subgroup of the same original fixed
group. Its order is exactly `q^3`, and it is a 3-group
([`CFSGReeGTwoOriginalPositiveSubgroup`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalPositiveSubgroup.lean)).
The actual fixed torus has order `q-1`. Its three root characters show
that a unit different from 1 and -1 has no nonidentity positive fixed
point. A reusable finite Lang-map argument therefore places the whole
positive subgroup in the original derived subgroup for `m >= 1`
([`CFSGReeGTwoOriginalTorus`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalTorus.lean),
[`CFSGReeGTwoPositiveDerived`](SymmetricSubgroupAsymptotics/CFSGReeGTwoPositiveDerived.lean)).
The literal longest Weyl word is also a genuine fixed opposition
involution. It inverts this torus, so torus squares belong to the derived
group. A regular such square excludes every nonidentity positive element
from the full centre of the derived group. The positive 3-group therefore
embeds faithfully in the actual pinned Ree group, still with order `q^3`
([`CFSGReeGTwoPositiveCentralQuotient`](SymmetricSubgroupAsymptotics/CFSGReeGTwoPositiveCentralQuotient.lean)).
The full original fixed Bruhat decomposition is now proved by unique
native-flag factorization, without assuming fixed-point lifting. It gives
the exact fixed-group order `q^3*(q-1)*(q^3+1)`, proves that the positive
group is Sylow, and identifies its normalizer with the soluble Borel
([`CFSGReeGTwoFixedFactorDescent`](SymmetricSubgroupAsymptotics/CFSGReeGTwoFixedFactorDescent.lean),
[`CFSGReeGTwoFixedCardinalitySylow`](SymmetricSubgroupAsymptotics/CFSGReeGTwoFixedCardinalitySylow.lean)).
The two-root subgroup is normal in the full fixed group and contained in
its derived subgroup. Its nontrivial normal image in the actual simple
pinned derived/central quotient is therefore the whole quotient. This
proves the original good-Sylow theorem without asserting perfectness or
simplicity of the full fixed group
([`CFSGReeGTwoOriginalGoodSylow`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalGoodSylow.lean)).
The Borel point action has degree `q^3+1`, the derived index in the fixed
group is at most four, and the full derived centre is trivial. These actual
bounds prove `ell^2 < |ReeG2(q)|` for the least proper subgroup index
([`CFSGReeGTwoOriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalIndexSquare.lean)).
The actual central root line and square torus prove `q <= ell` for
every proper permutation degree. The positive subgroup's intrinsic
characteristic layers and its cubing map show that an automorphism
fixing the central axis and commuting with the square torus is trivial.
The opposed-pair stabilizer restricts faithfully to that positive subgroup.
Its central action embeds in the square-scalar normalizer; charging the
same actual inner derived torus gives `|Out(ReeG2(3^(2*m+1)))| <= 2*(2*m+1)`
([`CFSGReeGTwoOriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalOuterBound.lean)).
The proof does not identify the derived torus with the full fixed torus
or assume that the full fixed group is perfect. The numerical outer
budget and the complete T1 integration are checked, so ReeG2 no longer
occurs in either residual callback.
The actual positive subgroup and torus also form a faithful soluble
semidirect product of order `q^3*(q-1)` in the original fixed group.
The positive centre is exactly its last free coordinate, of order `q`;
the torus acts faithfully on this additive field axis through all
nonzero scalars
([`CFSGReeGTwoOriginalBorel`](SymmetricSubgroupAsymptotics/CFSGReeGTwoOriginalBorel.lean),
[`CFSGReeGTwoPositiveCentre`](SymmetricSubgroupAsymptotics/CFSGReeGTwoPositiveCentre.lean)).

For the ReeF4 and Tits continuation, characteristic two now supplies
two actual 26-dimensional actions of the same folded F4 group on its
E6 Geck module: the image of `1+P`, and the quotient
`Fix(P)/range(1+P)` for the actual diagram involution. Explicit bases
and their root-label bijection are checked. This is representation
infrastructure. Exceptional covariance for all four positive simple
root generators is proved on these same two actions, with the field
parameter squared exactly on the short-root side
([`CFSGFFourE6NormQuotientSelectedCovariance`](SymmetricSubgroupAsymptotics/CFSGFFourE6NormQuotientSelectedCovariance.lean),
[`CFSGFFourE6NormQuotientOuterCovariance`](SymmetricSubgroupAsymptotics/CFSGFFourE6NormQuotientOuterCovariance.lean)).
Actual integral opposition transports these identities to all four
negative generators, giving all eight signed identities
([`CFSGFFourE6NormQuotientNegativeCovariance`](SymmetricSubgroupAsymptotics/CFSGFFourE6NormQuotientNegativeCovariance.lean)).
The norm action is now proved faithful: its kernel lies in the actual
diagonal pair normalizer, its simple-root scalars are one, and a checked
26-edge propagation through the remaining coordinates kills the kernel
([`CFSGFFourE6NormActionFaithful`](SymmetricSubgroupAsymptotics/CFSGFFourE6NormActionFaithful.lean)).
The equal norm and transported quotient action ranges then give an actual
exceptional automorphism of this same folded group, whose square sends
root parameters to their squares
([`CFSGFFourE6ExceptionalFoldedAutomorphism`](SymmetricSubgroupAsymptotics/CFSGFFourE6ExceptionalFoldedAutomorphism.lean)).
Unconditional correspondence with the original F4 source still requires proof
([`CFSGFFourE6CharacteristicTwoNormBasis`](SymmetricSubgroupAsymptotics/CFSGFFourE6CharacteristicTwoNormBasis.lean),
[`CFSGFFourE6CharacteristicTwoQuotientAction`](SymmetricSubgroupAsymptotics/CFSGFFourE6CharacteristicTwoQuotientAction.lean)).
The original source now has a checked family of 24 positive integral
divided-power paths, their negative partners and four Cartan vectors
([`CFSGFFourOriginalFiftyTwoFamily`](SymmetricSubgroupAsymptotics/CFSGFFourOriginalFiftyTwoFamily.lean)).
Source identities are proved from Serre relations, Jacobi and local
nilpotence; selected integral matrix coordinates are checked separately.
This is a family construction and initial source verification, not yet
an integral basis or an all-characteristic source-faithfulness theorem.

The original twisted E6 good-Sylow theorem is
[`CFSGTwistedE6OriginalGoodSylow.typeTwistedE6_goodSylowPrime`](SymmetricSubgroupAsymptotics/CFSGTwistedE6OriginalGoodSylow.lean).
Its only parameters are the prime power and simplicity of the original
pinned model. The proof retains the original derived fixed source and
its same action image. Whole fixed-upper preimages and explicit source
opposition words identify that image with the subgroup generated by the
two fixed p-subgroups. A relative Bruhat cover keeps central differences
in an abelian diagonal factor, without identifying that factor with the
literal torus or assuming arbitrary fixed-point lifts. The checked
soluble Sylow normalizer and original projective equivalence complete
the transfer. The original outer-order theorem now proves `|Out| <= 6*f`
for `q = p^f`
([`CFSGTwistedE6CompleteOuterBudget`](SymmetricSubgroupAsymptotics/CFSGTwistedE6CompleteOuterBudget.lean)).
The actual paired torus gives `q^2 <= ell`; together these prove every
required logarithmic and small-degree clause. Both twisted E6 model
callbacks are discharged in the endpoint above.

The original F4 and twisted E6 least-index squares use one shared count
([`CFSGFFourE6OriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGFFourE6OriginalIndexSquare.lean),
[`CFSGTwistedE6GeckOriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGTwistedE6GeckOriginalIndexSquare.lean)).
A literal relative-root menu has at most 512 seeds. Nine independent
base-field parameters in each retained centralizer absorb this menu,
including at q=2. The base-field factors centralize the full extension-field
root line before their semilinear fixedness is used. The fixed-upper
cardinal stays symbolic, and strictness comes from its proved square being
less than the original group order. No supplied order formula, root-family
recognition, or centralizer-capacity hypothesis remains in these theorems.
Their complete outer-order budgets are now proved and threaded into the
optional endpoint above.

The complete unitary geometry is checked on the original action.
[`CFSGTwistedAUnitarySemilinearPieces`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitarySemilinearPieces.lean)
constructs representatives on every singular subspace of dimension at
least three. The shared maximal-space exchange and connected gallery
propagate their common-plane field agreement, giving one common field
component on all maximal spaces when the Witt rank is at least three
([`CFSGTwistedAUnitaryGlobalFieldComponent`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryGlobalFieldComponent.lean)).
The global reconstruction uses these representatives together with the
actual opposed-space extension and normalized point determination. Independently,
[`CFSGHermitianTwoByTwoCentroid`](SymmetricSubgroupAsymptotics/CFSGHermitianTwoByTwoCentroid.lean)
proves the all-characteristic additive rank-one-cone scalar theorem
without assuming fixed-field linearity; its actual automorphism and
semilinear reconstruction applications are being installed separately.
The actual intrinsic root star is now exactly the literal Hermitian
coefficient group
([`CFSGTwistedAUnitaryProjectiveStarParameters`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryProjectiveStarParameters.lean)),
and arbitrary original plane-stabilizing automorphisms transport its
fixed scalar action
([`CFSGTwistedAUnitaryStarScalarTransport`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryStarScalarTransport.lean)).
Every resulting base-field automorphism extends to the same original
quadratic extension by a proved Frobenius power
([`CFSGTwistedAFixedFieldAutomorphismLift`](SymmetricSubgroupAsymptotics/CFSGTwistedAFixedFieldAutomorphismLift.lean)).
The same coefficients now give actual semilinear maps on every point
of a canonical two-dimensional star, including the smallest fields
([`CFSGTwistedAUnitaryStarPointSemilinearity`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryStarPointSemilinearity.lean)).
Original inner actions agree with the literal natural matrices, so
actual maximal-plane normalization transports these maps to every
maximal singular plane in ranks three and four
([`CFSGTwistedAUnitaryPlaneSemilinearity`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryPlaneSemilinearity.lean)).
Constructed common-opposite planes now propagate the same field component
to all these low-rank maximal planes, including the smallest fields
([`CFSGTwistedAUnitaryLowRankGlobalField`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryLowRankGlobalField.lean)).
The literal opposed coordinate halves, their middle-coordinate
decomposition and their nondegenerate cross-pairing are also proved
([`CFSGTwistedAUnitaryHalfDecomposition`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryHalfDecomposition.lean),
[`CFSGTwistedAUnitaryOpposedPairing`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryOpposedPairing.lean)).
In every odd vector dimension, actual outside-point connectivity and local
pieces determine a common norm-one middle multiplier
([`CFSGTwistedAUnitaryOddMiddleDetermination`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitaryOddMiddleDetermination.lean)).
The signed middle norm is retained and cancelled only after proving it nonzero.
The even-dimensional kernel is proved separately in all ranks. The resulting
[`CFSGTwistedAUnitarySemilinearFactorization`](SymmetricSubgroupAsymptotics/CFSGTwistedAUnitarySemilinearFactorization.lean)
constructs a field automorphism and an actual ambient similitude for every
original automorphism, with no geometric callback. Scalar-kernel cancellation
bounds the projective similitude image by the original natural fixed group;
counting its field factor gives `|Out| <= 2*(r+1)*f`.
[`CFSGUnitaryCompleteOuterBudget`](SymmetricSubgroupAsymptotics/CFSGUnitaryCompleteOuterBudget.lean)
combines this with `q^r <= ell` to discharge the outer budget for every
classifier-admissible unitary tag, including higher-rank fields of order two.

For twisted D,
[`CFSGTwistedDRelativeUnipotentCenter`](SymmetricSubgroupAsymptotics/CFSGTwistedDRelativeUnipotentCenter.lean)
identifies the actual Sylow centre with the fixed-field additive group,
and
[`CFSGTwistedDProjectiveRootFamily`](SymmetricSubgroupAsymptotics/CFSGTwistedDProjectiveRootFamily.lean)
proves that arbitrary original projective automorphisms preserve its
conjugate root family. The actual fixed-field singular pair frames are
constructed in
[`CFSGTwistedDSingularPairOrbit`](SymmetricSubgroupAsymptotics/CFSGTwistedDSingularPairOrbit.lean).
Exact fixed-field plane labels and faithfulness of the original
automorphism action are now proved
([`CFSGTwistedDPlaneActionFaithful`](SymmetricSubgroupAsymptotics/CFSGTwistedDPlaneActionFaithful.lean)).
Actual root products now characterize fixed-field plane adjacency,
and common-neighbour counts recognize the additional plane-intersection
relation, including the nonsplit rank-four case
([`CFSGTwistedDR11Recognition`](SymmetricSubgroupAsymptotics/CFSGTwistedDR11Recognition.lean)).
Actual quadratic shell and star bridges then reconstruct the original
singular-point action. It is faithful and preserves quadratic
orthogonality in every characteristic
([`CFSGTwistedDPointAction`](SymmetricSubgroupAsymptotics/CFSGTwistedDPointAction.lean),
[`CFSGTwistedDPointOrthogonality`](SymmetricSubgroupAsymptotics/CFSGTwistedDPointOrthogonality.lean)).
The actual nonsplit maximal gallery also gives one common field component
on all maximal singular spaces
([`CFSGTwistedDGlobalFieldComponent`](SymmetricSubgroupAsymptotics/CFSGTwistedDGlobalFieldComponent.lean)).
One actual relative-root word simultaneously aligns every opposed maximal
pair, retaining the anisotropic tail
([`CFSGTwistedDOpposedPairAlignment`](SymmetricSubgroupAsymptotics/CFSGTwistedDOpposedPairAlignment.lean)).
Global reconstruction now realizes every original automorphism by one
actual field automorphism and linear quadratic similitude
([`CFSGTwistedDAutomorphismGeometry`](SymmetricSubgroupAsymptotics/CFSGTwistedDAutomorphismGeometry.lean)).
A direct elimination of full fixed-field isometries gives index at most
four over the literal relative-root group
([`CFSGTwistedDFixedIsometryIndex`](SymmetricSubgroupAsymptotics/CFSGTwistedDFixedIsometryIndex.lean)).
Scalar-kernel cancellation and the original central quotient then prove
`|Out| <= 8f`, and `|Out| <= 4f` in characteristic two. Together with the
proved root-star degree lower bound, the exact prime logarithm proves the
required outer budget in every admissible rank and field. No global
reconstruction, isometry-recognition or degree-lower-bound premise remains.

For triality,
[`CFSGTrialityGeckFixedDerivedMatrixLift`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckFixedDerivedMatrixLift.lean)
constructs actual fixed matrix lifts of derived fixed actions. This uses
the checked central kernel and a general central-difference argument;
it does not assert fixed lifts for arbitrary fixed elements.
[`CFSGTrialityGeckFixedPositiveSylow`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckFixedPositiveSylow.lean)
constructs a Sylow subgroup with soluble normalizer in the actual matrix
fixed group, including characteristics two and three. The proof uses
actual Bruhat uniqueness for an element with nonzero simple leading
coordinates. The original projective transfer is now proved in
[`CFSGTrialityGeckDerivedProjectiveImage`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckDerivedProjectiveImage.lean):
the same original triality model has a Sylow subgroup with soluble
normalizer, conditional only on its original simplicity. Generation by
two conjugate Sylows is now proved in
[`CFSGTrialityGeckGoodSylow`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckGoodSylow.lean).
The actual Borel is twist-stable,
block Bruhat permutations are unique even on the nontrivial Cartan
block, and every fixed element has a triality-stable Bruhat cell
([`CFSGTrialityGeckFixedBruhatCell`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckFixedBruhatCell.lean)).
The continuation retains commutator membership in the full preimage of
the fixed action range. For centrally twisted cells, uniqueness makes
the root factors fixed and retains the actual central difference in the
diagonal factor. Actual opposition words then identify the generated
root action with the original derived action. This removes triality
from the optional good-Sylow callback above; it asserts no triality
outer-order bound.

The original triality least-index square is now also proved
([`CFSGTrialityGeckOriginalIndexSquare`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckOriginalIndexSquare.lean)).
The full fixed-matrix long-root family satisfies `M*q^3 <= 6*q^12`:
each of six signed root-line orbits retains a literal q-cubed centralizer.
Opposite disjoint Sylows give `q^24 <= |G|` through the actual central
quotient. The original q-element root subgroup is nontrivial and proper;
its conjugate family is a cardinality factor of the counted matrix family.
Thus `ell^2 < |G|` in every field, including `q=2`, without a supplied
exceptional group-order formula. Its complete outer-order budget is
proved below.

The actual fixed positive group's commutator subgroup is also now identified
with the kernel of its original four simple leading coordinates
([`CFSGTrialityGeckFixedPositiveDerivedKernel`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckFixedPositiveDerivedKernel.lean)).
The proof constructs fixed words for every middle-layer tensor coordinate
and actual commutators for the seven raised coordinates. Fixed long-root
commutators supply the remaining highest-root kernel. This includes `q=2`
and characteristic three, without assuming that fixed points surject onto
a fixed quotient. It supplies the outer-order proof below.

The original triality Sylow normalizer now has exactly two minimal strict
overgroups, the two literal relative simple parabolics
([`CFSGTrialityGeckOriginalMinimalParabolics`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckOriginalMinimalParabolics.lean)).
The central-kernel transfer is proved on the subgroup generated by the
actual signed fixed root groups. It assumes no automorphism lift to that
source.

The literal cubic norm also gives every pair of scalar coordinates
`(c^2/a, a^2/Norm(c))` over the actual cubic extension and its fixed field
([`CFSGTrialityNormTorusScalars`](SymmetricSubgroupAsymptotics/CFSGTrialityNormTorusScalars.lean)).
The proof retains a norm-one square correction and works at `q=2`.
The literal torus words now realize all these scalar pairs inside the
same generated group
([`CFSGTrialityGeckRelativeScalarTorus`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckRelativeScalarTorus.lean)).
Their square-scalar action on the injective original short-root chart
also proves `q^3 <= 2*ell` for every proper subgroup index `ell`
([`CFSGTrialityGeckPermutationDegree`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckPermutationDegree.lean)).
Actual cubic norm surjectivity couples the two field components, and the
four signed simple charts determine the original automorphism. Counting
inner-normalized representatives proves `|Out| <= 3*f` for `q = p^f`,
including `q=2`
([`CFSGTrialityGeckOriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGTrialityGeckOriginalOuterBound.lean)).
Together with the proved degree lower bound this discharges the complete
outer budget and removes triality from both T1 model callbacks.


The shared folded-root continuation proves that the same generated Geck Lie
algebra is spanned by its own homogeneous elements. Integer norm bounds and
its invariant Gram form yield cubic adjoint vanishing for two orthogonal
root degrees. This discharges all short-root fourth-coefficient constraints
on the original F4 image, in every characteristic
([`CFSGFFourFullRootAction`](SymmetricSubgroupAsymptotics/CFSGFFourFullRootAction.lean)).
It proves the literal full-root action and equality of actual action ranges.
The continuation now proves the original F4 good-Sylow theorem
([`CFSGFFourOriginalGoodSylow`](SymmetricSubgroupAsymptotics/CFSGFFourOriginalGoodSylow.lean)).
The signed folded p-subgroups generate the literal matrix group. Their
regular element lies in a unique ambient E6 Sylow, whose intersection
gives an F4 Sylow with soluble normalizer. The checked original action
range transfers generation and the Sylow data to the original model.
No externally named matrix-group recognition is assumed. F4's least-index
square and complete outer-order budget are now proved.
The two kernels from the same literal folded group are now proved central:
first its restricted action on the original F4 image, then its projection
to the original simple projective model
([`CFSGFFourE6ActionCentralKernel`](SymmetricSubgroupAsymptotics/CFSGFFourE6ActionCentralKernel.lean),
[`CFSGFFourE6OriginalCentralKernel`](SymmetricSubgroupAsymptotics/CFSGFFourE6OriginalCentralKernel.lean)).
Actual strict upper overgroups supply simple Weyl words, while positive
injectivity and disjoint opposed images exclude a noncentral kernel.
The proof does not assume faithfulness of the restricted representation.
This central kernel now transfers the four minimal simple parabolics and
their opposite root intersections to the original F4 model. An arbitrary
original automorphism can be adjusted by an inner automorphism to preserve
the opposed Sylows and permute these four actual root charts
([`CFSGFFourE6OriginalRootAction`](SymmetricSubgroupAsymptotics/CFSGFFourE6OriginalRootAction.lean)).
The statement allows root-length interchange in characteristic two.
The actual signed root commutation graph restricts the label permutation
to identity or path reversal. Its kernel acts by one common field
automorphism and four scalars; the literal product torus realizes every
scalar tuple because the relative Cartan matrix has an integral inverse.
The signed parameters determine the original automorphism, so counting
modulo actual inner tori proves `|Out(F4(q))| <= 2*f` for `q=p^f`
([`CFSGFFourE6OriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGFFourE6OriginalOuterBound.lean)).
The same torus gives `q <= ell`; together these discharge the complete
budget and remove original F4 from both T1 model callbacks, without a
field-action or automorphism-reconstruction hypothesis.
For three orthogonal roots the integral operator formula retains its genuine
cubic coefficient, with three independent parameters
([`CFSGNormTwoCoordinateOriginalParameterizedTriple`](SymmetricSubgroupAsymptotics/CFSGNormTwoCoordinateOriginalParameterizedTriple.lean)).
Rational-to-integral transfer and the actual image submodule prove this on
the original source in every characteristic, including three, without
dividing by a factorial or assuming representation faithfulness.

For the original twisted E6 group, the positive Sylow normalizer has exactly
four minimal strict overgroups, given by the literal folded simple parabolics
([`CFSGTwistedE6GeckOriginalMinimalParabolics`](SymmetricSubgroupAsymptotics/CFSGTwistedE6GeckOriginalMinimalParabolics.lean)).
Integral grading flags prove the matrix-group minimality. A proved central
kernel and the surjective subgroup correspondence transport it to the
original projective model. This correspondence does not assume that an
automorphism of the original group lifts to the matrix source.
For an original automorphism preserving both opposed Sylow subgroups,
the two induced permutations of the positive and negative simple root
charts agree
([`CFSGTwistedE6GeckOriginalSignedRootAction`](SymmetricSubgroupAsymptotics/CFSGTwistedE6GeckOriginalSignedRootAction.lean)).
Distinct-label cross commutation and actual same-label rank-one words
prove the agreement in every characteristic. The paired and singleton
field components now agree on the actual fixed coefficient field
([`CFSGTwistedE6GeckOriginalFieldAgreement`](SymmetricSubgroupAsymptotics/CFSGTwistedE6GeckOriginalFieldAgreement.lean)).
The actual signed simple charts generate the whole root-generated group;
surjectivity to the original model then proves that its pair stabilizer
acts faithfully on the positive simple parameters
([`CFSGTwistedE6GeckOriginalParameterFaithful`](SymmetricSubgroupAsymptotics/CFSGTwistedE6GeckOriginalParameterFaithful.lean)).
The compatible Cartan scalar image now has proved index at most three,
realized by literal inner torus words. Counting one extension-field
automorphism factor therefore gives `|Out| <= 3*|Aut(F_(q^2))| = 6*f`
([`CFSGTwistedE6OriginalOuterBound`](SymmetricSubgroupAsymptotics/CFSGTwistedE6OriginalOuterBound.lean)).
The complete budget and T1 splice above retain no twisted E6 callback.

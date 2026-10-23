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

The type-D intrinsic infrastructure (`CFSGOrthogonalDIndexUnipotentCenter.lean`, `CFSGOrthogonalDIndexUnipotentFixedSpace.lean`) identifies the centre of the actual flag-unitriangular subgroup with its highest paired-root line and the additive group of the same field, in every characteristic. Its fixed vectors are exactly the first natural line. The proof preserves the actual split quadratic form, excluding the spurious diagonal shear in characteristic two. The continuation (`CFSGOrthogonalDIndexOddSylow.lean`) proves that this same subgroup is Sylow in odd characteristic, using its actual partial-flag normalizer and middle two-plane action. The all-characteristic continuation is now proved in `CFSGOrthogonalDIndexSylow.lean`: parity of three maximal singular-space distances excludes the final-pair swap from the actual unipotent normalizer. Subsequent polar/triality automorphism reconstruction remains open.

The odd-B intrinsic packet (`CFSGOrthogonalBProjectiveLongRoots.lean`) now proves that the literal flag-unitriangular subgroup is Sylow, its normalizer is the actual flag Borel, and its centre is exactly the highest long-root field line. Actual projective automorphisms preserve the conjugate root lines (`CFSGOrthogonalBProjectiveRootLines.lean`). Each line has a well-defined natural two-plane label, recovered as range(x-I) from any nonidentity root element. All statements retain the same original matrix subgroup and projective quotient. The continuation `CFSGOrthogonalBSingularPlaneAction.lean` now proves coverage of all totally singular two-planes and the exact projective automorphism action on them, using actual pair normalization and the literal tail embedding. The polar-point action, semilinear realization and odd-B outer bound are now proved by the continuation below.

`CFSGPrimitiveSublinearBounds.lean` proves that those estimates are uniformly sublinear across all actual primitive actions. Its first applications are an eventual c=1 relative-character tail and an eventual three-tenths primitive chief-weight tail. The statements retain only the displayed simple-index/Out and, where used, simple-two-generation inputs; they do not invoke the sharp primitive inputs. These are infinite-tail replacements with a uniform eventual threshold, not proofs of the existing cutoffs 34/45 or of the intervening bounded ranges. The public T1 premises are unchanged.

The original untwisted F₄ parity branch is now proved (`CFSGFFourEvenOrderRefinement.lean`). The actual E₆ fold satisfies the pinned F₄ Serre relations; a long-root Weyl word has fourth power one and is noncentral on the same original image, in every characteristic. This removes precisely F₄ from the optional parity residual. F₄ generation and outer-automorphism bounds, twisted exceptional parity, and the public seven-input boundary remain unchanged.

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
greater than q^12. Rank two and the unitary outer-order budget remain open;
the whole unitary simple-index callback is not discharged yet.

The original twisted-D derived image also has a defining-characteristic
Sylow subgroup with soluble normalizer
([`CFSGTwistedDDerivedSylowNormalizer`](SymmetricSubgroupAsymptotics/CFSGTwistedDDerivedSylowNormalizer.lean)).
Its whole natural preimage is literally fixed by the twist
([`CFSGTwistedDDerivedFixed`](SymmetricSubgroupAsymptotics/CFSGTwistedDDerivedFixed.lean)).
Fixed-chain parameters, literal paired-root tori, and the complete
nonzero singular-vector normalization are proved in that same derived image
([`CFSGTwistedDSingularVectorNormalization`](SymmetricSubgroupAsymptotics/CFSGTwistedDSingularVectorNormalization.lean)).
The projective transport is also proved on this actual derived image;
companion normalization and relative generation remain open. The twisted-D callback is not
discharged by these prerequisites alone.

[`CFSGSevenTargetsUnitaryExceptionalE`](SymmetricSubgroupAsymptotics/CFSGSevenTargetsUnitaryExceptionalE.lean)
threads these completed model cases, including the entire unitary branch
and the sufficient E6/E7/E8 simple-index bounds, into T1 and AllTargets.
Its parameters are CFSG, five published inputs (general class count, the
two Tracey inputs, labelled transitive count, and ordinary permutation
rank), and **two still-unproved model callbacks**: the remaining good-Sylow
cases and the remaining sufficient simple-index/outer bounds. E6/E7/E8
are absent from both callbacks, and all twisted-A tags are absent from the
good-Sylow callback. The current family and endpoint audits use only
`propext`, `Classical.choice`, and `Quot.sound`. This residual
interface is not a theorem from CFSG alone; the canonical public endpoint
continues to have seven published inputs.


The shared folded-root continuation proves that the same generated Geck Lie
algebra is spanned by its own homogeneous elements. Integer norm bounds and
its invariant Gram form yield cubic adjoint vanishing for two orthogonal
root degrees. This discharges all short-root fourth-coefficient constraints
on the original F4 image, in every characteristic
([`CFSGFFourFullRootAction`](SymmetricSubgroupAsymptotics/CFSGFFourFullRootAction.lean)).
It proves the literal full-root action and equality of actual action ranges;
it does not supply F4 group recognition, a good-Sylow theorem, or an outer
bound. Those family obligations remain explicit.

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
`--root SymmetricSubgroupAsymptotics.MarkedC4PublishedTenTargets`.
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
| `SymmetricSubgroupAsymptotics/CFSGSerreDividedPowers.lean` | Binomial multiplication on the literal integral Serre lattice, preserved by base change. Uniform finite-type nilpotence remains open. |
| `SymmetricSubgroupAsymptotics/CFSGSerreRootOperatorInvertible.lean` | Every original root operator has an actual invertible lift, proved through pointwise divided-power nilpotence in every characteristic. This supplies neither additive root parameters nor cross-root relations. |
| `SymmetricSubgroupAsymptotics/CFSGSerreOrdinaryTwistModels.lean` | Original diagram/Frobenius graph identifications for twisted A, D, E6 and triality, built on the same integral lattice and its scalar extension. Exceptional long-short isogenies are separate. |
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
any of the published inputs in the T1 facade below.

## Explicit input boundary

The final exports are
[T1_of_ten_published_inputs](SymmetricSubgroupAsymptotics/MarkedC4PublishedTenTargets.lean)
and `allTargets_of_ten_published_inputs`. Their **10 named inputs** are listed
below. The character bundle has one published general class-number field. Both
abelian-quotient statements are now supplied by checked proofs. These are explicit theorem parameters,
not new Lean axioms. The kernel audit of both exports uses only `propext`,
`Classical.choice`, and `Quot.sound` in addition to the stated parameters.

Twenty-nine formerly external requirements are now discharged by checked proofs
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
| The actual small-affine consumers in degrees 16 and 27. | [Actual finite data](SymmetricSubgroupAsymptotics/PrimitiveAffineActualFiniteDataConstruction.lean) and [the actual consumer assembly](SymmetricSubgroupAsymptotics/PrimitiveAffineActualConsumerAssembly.lean) use the full original translation kernel at degree 16, the proved linear structure at degree 27, and the retained composition-length theorem. No primitive-16 or small-affine carrier correspondence is assumed or asserted as proved. |
| The actual semisimple primitive-component compression. | [`primitiveComponentExhaustion_without_composition`](SymmetricSubgroupAsymptotics/PrimitiveComponentExhaustionWithoutComposition.lean) retains the actual full socle, quotient and block system with the sufficient margin `3q ≤ 2r`. Actual semisimple sources replace the bounded 116-row correspondence and the stronger unused degree-six/twelve classifiers. |


| Exact binary excess classification, including all degree bounds and proper-normal restrictions. | [`publishedProposition53Binary_proved`](SymmetricSubgroupAsymptotics/BinaryExcessProposition53Proof.lean) has no hypotheses. It retains the original pair kernels, joint parity and square carries, and proves the full abelianization and proper-normal consequences. |
| Full binary normal-F quotient theorem, including the exceptional degree-eight case. | [`publishedTheorem57Binary_proved`](SymmetricSubgroupAsymptotics/BinaryNormalFTheorem57Proof.lean) has no hypotheses. All original actions, normal denominators, ambient commutators `[F,Q]`, centralizers and excess/rank alternatives are retained. The degree-32 critical cases use actual joint capacities and annihilator-aware invariant intervals, with selected cocycle lifts proved internally. |
| Primitive ternary chief weight and the 3/10 weight bound, without bounded primitive correspondence. | [Chief weight](SymmetricSubgroupAsymptotics/PrimitiveChiefWeightWithoutCatalogue.lean) and [the 3/10 bound](SymmetricSubgroupAsymptotics/PrimitiveThreeTenthsWeightWithoutCatalogue.lean) follow from actual linear/socle structure, the retained composition-length theorem and simple-index bound. The same structural route proves [Dixon's order bound](SymmetricSubgroupAsymptotics/ElementaryDixonOrderWithoutCatalogue.lean). No 336-row coverage premise is used. |
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
[`FaithfulSimpleGeneratorFromTwoGeneration`](SymmetricSubgroupAsymptotics/FaithfulSimpleGeneratorFromTwoGeneration.lean)
derives the faithful-simple logarithmic generator bound from the still
retained `hSimpleGen`. Finite-simple two-generation remains an explicit
published input.

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
At degree 81, the retained composition-length theorem bounds the soluble
complement's number of prime factors by eleven; its order divides
`|GL₄(F₃)| = 24261120`, and the checked divisor budget gives `|R| ≤ 81³`.
These consumer replacements do not assert the general Halasi–Maróti theorem.

Two further input reductions use weaker or already retained results.
[`publishedProposition62_of_retained_inputs`](SymmetricSubgroupAsymptotics/LargeOrbitGeneratorConsequencesFinal.lean)
derives the large-orbit soluble generator theorem from `hPrimitiveGen`,
`hcomp`, and the internally proved refined induced-module theorem. Its stronger checked estimate is
`d(G) ≤ 128 ∑ n_i / sqrt(log₂ n_i)` on the actual nontrivial orbits.
The proof keeps correlated orbit actions in the whole quotient, uses ordinary
lifting only across actual abelian kernels, and charges each literal local
chief series through the primitive composition theorem. No generic soluble
normal-closure-to-ordinary-generation step is used.

The Pyber representative input is unnecessary for the final marked moment.
[`index_eventually_exp_bound`](SymmetricSubgroupAsymptotics/LMMSubquadraticSolubleContainers.lean)
derives a subquadratic literal container-menu count from the retained `hLMM`.
Fibre sizes m_i pay only ∑m_i² ≤ n²; partition labels and the fixed local
coefficient are negligible on that scale. The [alternate global assembly](SymmetricSubgroupAsymptotics/MarkedC4SubquadraticContainersGlobal.lean)
retains the original character restrictions and the same bounded-source
moment. This removes `h86` without claiming a formal proof of its stronger
`2^(13n)` conjugacy-class estimate. The final [catalogue adapter](SymmetricSubgroupAsymptotics/T1CatalogueFromMarkedMoment.lean)
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
[`BoundedCoreSubquadraticContainersGlobal.marked_bound`](SymmetricSubgroupAsymptotics/BoundedCoreSubquadraticContainersGlobal.lean)
keeps that original source and orbit cutoff; only the fixed tuple-control
constant increases. This removes `hseven` without asserting the sharper
unrestricted `4L*sqrt M` theorem. No new hypothesis replaces it.

The coarse ordinary bound is now supplied by
[`ordinarySubgroupUpper_of_retained_inputs`](SymmetricSubgroupAsymptotics/CFSGOrdinarySubgroupUpperProof.lean).
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
all-subgroup upper bound is proved from `hAG`, `hPrimitiveGen` and `hcomp`.

| Lean parameter and definition | Mathematical input | Published source or correspondence |
|---|---|---|
| [lit : PreE7CharacterPublishedInputs](SymmetricSubgroupAsymptotics/CharacterLiteratureProvedBinary.lean) | One field: permutation class number ≤5^((b−1)/3) for b≥4. | Garonzi–Maróti, Theorem1.1. The two abelian-quotient fields and nilpotent class-number field of the older internal API are proved and filled internally. |
| [hcomp : PrimitiveCompositionLengthInput](SymmetricSubgroupAsymptotics/PrimitiveCompositionLengthInput.lean) | Every actual composition series of primitive degree r≥2 has length ≤(8/3)log₂r−4/3. | GPRV Thm1.3. |
| [hAG : PublishedAschbacherGuralnickSolubleGeneration](SymmetricSubgroupAsymptotics/MarkedC4AschbacherGuralnickSolubleGeneration.lean) | Every finite group generated by a soluble subgroup and one element. | Aschbacher–Guralnick, J.Algebra77 (1982),189–201; RDT Thm8.4 p32. Ambient-recovery field internal. |
| [hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput](SymmetricSubgroupAsymptotics/TraceyCorollaryThreeTwelveRaw.lean) | Exceptional degree3·2^m action has actual soluble subgroup and full binomial orbit partition, Mersenne exponent≥3. | TR Cor3.12 p17 PLUS preceding nonabelian PSL₂(p) construction Thm1.8/Cor3.11 excluding p=3. Cor3.12 alone is insufficient for exponent≥3. |
| [hPrimitiveGen : PrimitiveNormalGeneratorInput](SymmetricSubgroupAsymptotics/C1PrimitiveTail.lean) | Normal subgroup of primitive degree w≥4 has ordinary rank≤floor(log₂w). | HRD Thm1.1 normal specialization, sole degree3 exception excluded. |
| [hLMM : LucchiniMenegazzoMorigiTransitiveCountInput](SymmetricSubgroupAsymptotics/Non2PreE7MenuMassAggregation.lean) | Labelled transitive subgroup count is subquadratic-exponential. | Lucchini–Menegazzo–Morigi, BLMS32 (2000),191–195; exact labelled2^(Cn²/√logn) statement is sourced through RDT introductionp2. ID LIT-TRANSITIVE-COUNT. |
| [hTraceyPerm : TraceyPermutationGeneratorInput](SymmetricSubgroupAsymptotics/TraceyAffineInducedModuleInput.lean) | Transitive degree w≥2 group generated by≤ceil(w/√log₂w). | weakening; TR Thm1.1(1), constantc<1. Not the sharper2021 √3/2 bound. |
| [hSimpleGen : FiniteSimpleTwoGeneratorBound](SymmetricSubgroupAsymptotics/ActualWreathSemisimpleCoefficient.lean) | Every finite centerless simple group has≤2 generators. | Guralnick–Kantor, Journal of Algebra 234 (2000), Theorem I, p.744 and Corollary p.745; LIT-SIMPLE-2GEN. |
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
and the final exported-declaration axiom audit, passed on 21 October 2026.
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
| Final composition | [T1RelativeClosure](SymmetricSubgroupAsymptotics/T1RelativeClosure.lean), [MarkedC4PublishedTenTargets](SymmetricSubgroupAsymptotics/MarkedC4PublishedTenTargets.lean) | Complete remainder estimate and final T1/AllTargets exports. |
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

On 21 October 2026, recursive verification of the public import closure
matched its current sources,
compiled objects, direct dependency fingerprints, and pinned toolchain
against successful check receipts. Matching historical receipts were reused
with explicit relocation evidence; stale consumers were checked serially.
All sources in this closure are tracked in the main checkout and match the
audited bytes. Optional modules outside this public closure are not covered
by this release claim.

A fresh axiom audit of `T1_of_ten_published_inputs`,
`allTargets_of_ten_published_inputs`, `T2_of_T1`, `T3_of_T1`,
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

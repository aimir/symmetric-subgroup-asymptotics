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
`--root SymmetricSubgroupAsymptotics.MarkedC4PublishedGeometricTargets`.
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
| `SymmetricSubgroupAsymptotics/External/` | Selected Apache-licensed proof ports and mathlib backports, with preserved notices and pinned provenance. |
| `SymmetricSubgroupAsymptotics.lean` | Public import of the final proof facade and shared-threshold formulations. Optional certificate modules have their own imports. |
| `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` | Pinned compiler, package configuration, and exact dependencies. |
| `../scripts/check_lean.py` | Serialized compiler runner with memory, RSS, and wall-time limits. |
| `../scripts/check_lean_closure.py` | Dependency-order planning and conservative serial resume for a local module closure. |
| `../computations/python/` | Reproducible producers for the retained finite certificates. |

Build logs, receipts, scratch proofs, and research status records are kept
outside the publication repository.

## Explicit input boundary

The final exports are
[T1_of_published_inputs](SymmetricSubgroupAsymptotics/MarkedC4PublishedGeometricTargets.lean)
and `allTargets_of_published_inputs`. Their **25 named inputs** are listed
below. The character bundle has one published general class-number field. Both
abelian-quotient statements are now supplied by checked proofs. These are explicit theorem parameters,
not new Lean axioms. The kernel audit of both exports uses only `propext`,
`Classical.choice`, and `Quot.sound` in addition to the stated parameters.

Seventeen formerly external facts are now supplied by checked proofs on the
same pinned toolchain:

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
| Every abelian p-group quotient of a faithful degree-n action has order at most p^(floor(n/p)); in particular every binary abelian quotient has order at most 2^(n/2). | [`abelian_pQuotient_card_le`](SymmetricSubgroupAsymptotics/PermutationAbelianQuotientOrderBound.lean), from full abelianization-order induction on actual central-prime blocks and complementary orbits, followed by actual Sylow restriction. Higher prime-power cyclic factors are retained. |
| A transitive binary eight-point group of excess two is the actual Heisenberg group E8; a nonabelian normal quotient has trivial denominator and center/derived orders two. | [`publishedDegreeEightExceptional`](SymmetricSubgroupAsymptotics/RDTDegreeEightExceptionalProof.lean), from unconditional coverage of all 26 binary actions, short ambient normal-generation words for the other 25 actions, and the intrinsic E8 center/derived structure. |
| Every abelian quotient of a faithful degree-n action has order at most 3^(n/3). | [`kovacsPraegerAbelianizationBound`](SymmetricSubgroupAsymptotics/KovacsPraegerAbelianizationProof.lean), using an actual nilpotent supplement, coprime support compression, and full p-group abelianization orders. |
| t ambient normal generators of the actual socle yield t jointly faithful finite irreducible complex representations. | [`zmudFaithfulCharacterTupleInput_proved`](SymmetricSubgroupAsymptotics/ZmudFaithfulCharacterProof.lean), through primary semisimple duality, coinduction and injected irreducible constituents. The empty tuple and arbitrary nonsoluble groups are included. |
| The bounded-factor ordinary epimorphism estimate retains every actual normal target F and the original derived-normal projection kernel. | [`rdtTheorem46BinaryInput_proved`](SymmetricSubgroupAsymptotics/RDTBoundedFactorEpimorphismProof.lean), from short adapted tuples and joint kernel incidence; its constants depend only on the factor-order bound. |
| A nilpotent permutation group of faithful degree-n has at most (38/25)^n conjugacy classes. | [`nilpotentConjugacyClassInput`](SymmetricSubgroupAsymptotics/NilpotentConjugacyClassProof.lean), using proved binary, ternary and large-prime fourth-power bounds and actual disjoint coprime supports. All sharp character consumers are unchanged. |
| If N is normal in a transitive binary permutation group and N≤G′, its ambient normal-generator number is at most floor(n/4). | [`publishedDerivedNormalQuarterBinary_proved`](SymmetricSubgroupAsymptotics/BinaryDerivedNormalQuarterProof.lean), by original-degree induction through actual central-pair kernels and faithful top images. The nonelementary top has a proved quarter-module bound; an elementary top kills the derived image. No excess classification is assumed. |
| O'Nan–Scott structure: a finite faithful primitive action is affine, or its full socle is T^k with the exact degree alternatives and a faithful original quotient embedding into Out(T) ≀ S_k. | [`publishedONanScottStructure`](SymmetricSubgroupAsymptotics/PrimitiveSocleRawONanScottProof.lean), from actual minimal normals, the proved Scott subdirect theorem, point-stabilizer maximality, coordinate automorphisms and the exact inner kernel. Both minimal normals are retained in the two-regular case. No simple-group classification is assumed for this structural theorem. |

These proved results, both final exports, the T1-to-T2/T3 transfers and the
definition checks have standard-only axiom audits. Historical lower-level
constructors still accept the corresponding interface types; these are
filled internally in the final exports and are no longer assumptions there.
Selected upstream proofs and backports live in `External/`; exact revisions,
authorship, licenses and changes are recorded in
[`External/NOTICE`](SymmetricSubgroupAsymptotics/External/NOTICE).

Three other formerly separate parameters are now proved consequences of
stronger inputs retained below. [`TraceyRefinedInputConsequences`](SymmetricSubgroupAsymptotics/TraceyRefinedInputConsequences.lean)
derives both the half-dimension and logarithmic induced-module statements
from `hTraceyRefined`. [`FaithfulSimpleGeneratorFromTwoGeneration`](SymmetricSubgroupAsymptotics/FaithfulSimpleGeneratorFromTwoGeneration.lean)
derives the faithful-simple logarithmic generator bound from `hSimpleGen`,
using the elementary obstruction to a faithful small-degree simple action.
These implications remove redundant parameters; they do **not** formalize
the stronger refined Tracey or finite-simple two-generation theorems.

Four more separate inputs are now checked consequences of stronger inputs:

| Derived result | Retained premise and checked proof |
|---|---|
| Primitive degree-nine order list, including the natural `A₉`/`S₉` branches. | `compositionCatalogue`, through [`primitiveDegreeNineClassification_of_compositionCatalogue`](SymmetricSubgroupAsymptotics/PrimitiveDegreeNineFromCompositionCatalogue.lean). Only the literal degree-nine numerical rows are evaluated. |
| Primitive degree-six types `A₅`, `S₅`, `A₆`, `S₆`. | The same `compositionCatalogue`, through [`publishedPrimitiveDegreeSixClassification_of_compositionCatalogue`](SymmetricSubgroupAsymptotics/PrimitiveDegreeSixCatalogueClassification.lean). Actual maximal-overgroup coset actions and the degree-twelve order list prove the order-60 recognition step. |
| Binary transitive permutation-submodule head formula. | `hTraceyRefined`, through [`TraceyRefinedInducedModuleInput.binaryFormula`](SymmetricSubgroupAsymptotics/TraceyPermutationFormulaConsequences.lean), using the actual stabilizer induction and the prime-to/prime-power bounds. |
| Uniform soluble transitive permutation-module generator formula. | `hTraceySoluble`, through [`TraceySolubleOrbitInducedModuleInput.permutationFormulaRaw`](SymmetricSubgroupAsymptotics/TraceySolublePermutationConsequences.lean). A single explicit integer cap handles all subrepresentations. |

These reductions do not prove the broader retained catalogue or induced-module
theorems. The auxiliary [`exists_isTwoComplement_of_isSolvable`](SymmetricSubgroupAsymptotics/SolubleOddHall.lean)
is proved without an additional hypothesis: induction on a finite soluble
group's order and mathlib's Schur–Zassenhaus theorem construct its actual odd
Hall subgroup. [`PermutationStabilizerInduced`](SymmetricSubgroupAsymptotics/PermutationStabilizerInduced.lean)
proves the module transport used by both Tracey specializations, including
the empty and singleton point-set endpoints. The repeated standalone
Kovács–Praeger parameter is now filled by the proved full abelianization
theorem.

The separate Dixon order input is also removed. [`dixonOrder_of_primitive_inputs`](SymmetricSubgroupAsymptotics/SolublePermutationOrderBound.lean)
derives `|G| ≤ 24^(n/3)` from the retained `compositionCatalogue` and
`hSolubleBase`, together with the now-proved O'Nan–Scott structure. The primitive step proves the stronger
integer inequality `|G|³ ≤ 24^(n−1)`: bounded rows are checked numerically,
while large soluble affine actions have `|G| ≤ n⁴`. Actual minimal-block
wreath embeddings and orbit images complete the induction. This is a
proved dependency reduction; the two broader published inputs remain
explicit. It does not claim a formal proof of Halasi–Maróti.

Two further input reductions use weaker or already retained results.
[`publishedProposition62_of_retained_inputs`](SymmetricSubgroupAsymptotics/LargeOrbitGeneratorConsequencesFinal.lean)
derives the large-orbit soluble generator theorem from `hPrimitiveGen`,
`hTraceyRefined`, and `hcomp`. Its stronger checked estimate is
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

RDT means Roney-Dougal–Tracey, arXiv:2503.05416v1. TR means Tracey's
2018 transitive-generation paper, with page locators referring to its linked
author manuscript. HRD means Holt–Roney-Dougal (2013); GPRV means
Glasby–Praeger–Rosa–Verret (2018). PRIM means the published primitive
classifications and pinned PrimGrp 3.4.4; TRANS means the published
transitive classifications and pinned TransGrp 3.6.5. CLASS means the
Garonzi–Maróti general class-number theorem and the now-proved Maróti
nilpotent bound. Full titles, links, and
version conventions appear in the [literature register](../provenance/LITERATURE.md).

Finite correspondence inputs identify the **actual pinned representatives**.
The strict-head and bounded-socle correspondences additionally retain their
stated normal-subgroup/socle structure; they are not merely point-conjugacy
locators. None supplies a project head, capacity, marked moment, complete
source, or asymptotic target bound. The ordinary coarse subgroup upper bound
and labelled transitive-count theorem are retained published counting inputs.

| Lean parameter and definition | Mathematical input | Published source or correspondence |
|---|---|---|
| [lit : PreE7CharacterPublishedInputs](SymmetricSubgroupAsymptotics/CharacterLiteratureProvedBinary.lean) | One field: permutation class number ≤5^((b−1)/3) for b≥4. | Garonzi–Maróti, Theorem1.1. The two abelian-quotient fields and nilpotent class-number field of the older internal API are proved and filled internally. |
| [hcomp : PrimitiveCompositionLengthInput](SymmetricSubgroupAsymptotics/PrimitiveCompositionLengthInput.lean) | Every actual composition series of primitive degree r≥2 has length ≤(8/3)log₂r−4/3. | GPRV Thm1.3. |
| [hseven : PublishedTheoremSeven](SymmetricSubgroupAsymptotics/MarkedC4PublishedOrdinaryNilpotentGeneration.lean) | Soluble G with socle length ≤L and abelian-section prime-factor length ≤M is generated by a nilpotent subgroup plus ≤4L√M elements. | RDT Thm7 p3, proofpp32–33. |
| [h55 : PublishedTheorem55Binary](SymmetricSubgroupAsymptotics/MarkedC4RDTOriginalWordStructure.lean) | Actual bounded binary subdirect word, dependent/tail degrees: normal-generation bounds3x/8+y/2,5x/16+y/2,x/4+y/2 with exact excess exclusions. | RDT Thm5.5(ii) p17. |
| [h53 : ActualCaseIITargetStructure.PublishedProposition53Binary](SymmetricSubgroupAsymptotics/MarkedC4ActualCaseIITargetStructure.lean) | Binary excess classification: excess1/2, degree≤32; exact excess2 degrees and excess1 normal restrictions. | RDT Prop5.3(i) p16. |
| [h57 : RDTExcessStructure.PublishedTheorem57Binary](SymmetricSubgroupAsymptotics/MarkedC4RDTExcessStructure.lean) | Actual nonabelian normal quotient admits normal F with logcard([F,Q])+e logcard(C_Q(F))≤n/2 and centralizer log≤n/4, exact branch e and generator equality. | RDT Thm5.7 pp18–19. |
| [hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper](SymmetricSubgroupAsymptotics/MarkedC4OrdinarySubgroupUpper.lean) | ∃β, s_n≤2^(n²/16+βn√n), n>1. | RDT Thm1 p1. Strong quantitative coarse bound, not merely an asymptotic main term. |
| [hAG : PublishedAschbacherGuralnickSolubleGeneration](SymmetricSubgroupAsymptotics/MarkedC4AschbacherGuralnickSolubleGeneration.lean) | Every finite group generated by a soluble subgroup and one element. | Aschbacher–Guralnick, J.Algebra77 (1982),189–201; RDT Thm8.4 p32. Ambient-recovery field internal. |
| [hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput](SymmetricSubgroupAsymptotics/TraceyCorollaryThreeTwelveRaw.lean) | Exceptional degree3·2^m action has actual soluble subgroup and full binomial orbit partition, Mersenne exponent≥3. | TR Cor3.12 p17 PLUS preceding nonabelian PSL₂(p) construction Thm1.8/Cor3.11 excluding p=3. Cor3.12 alone is insufficient for exponent≥3. |
| [compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence](SymmetricSubgroupAsymptotics/PrimitiveTernaryThreeTenthsPublished.lean) | Faithful primitive degree<45 matches336 pinned rows; exact degree and order, or natural A_n/S_n identification. | PRIM degrees2–44. No ternary inequality field. |
| [hPrimitiveGen : PrimitiveNormalGeneratorInput](SymmetricSubgroupAsymptotics/C1PrimitiveTail.lean) | Normal subgroup of primitive degree w≥4 has ordinary rank≤floor(log₂w). | HRD Thm1.1 normal specialization, sole degree3 exception excluded. |
| [strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence](SymmetricSubgroupAsymptotics/PrimitiveTernaryStrictHeadPublished.lean) | Primitive degree<34 matches253 rows with actual normal minimal self-centralizing E and exact card(G/E). | plus standard primitive structure; PRIM degrees2–33. `PrimitiveStrictHeadSocleMatch` supplies E/minimality/selfCentralizing, not only a row index; document this enriched structural correspondence. No head capacity field. |
| [hLMM : LucchiniMenegazzoMorigiTransitiveCountInput](SymmetricSubgroupAsymptotics/Non2PreE7MenuMassAggregation.lean) | Labelled transitive subgroup count is subquadratic-exponential. | Lucchini–Menegazzo–Morigi, BLMS32 (2000),191–195; exact labelled2^(Cn²/√logn) statement is sourced through RDT introductionp2. ID LIT-TRANSITIVE-COUNT. |
| [hTraceyRefined : TraceyRefinedInducedModuleInput](SymmetricSubgroupAsymptotics/TraceyRefinedAffineInput.lean) | One generating-tuple length simultaneously satisfies half, logarithmic, prime-to-characteristic, primary-square-root and soluble prime-power binomial ceilings. | numerical specialization; TR Def1.5/Thm1.6 and Cor4.26–4.27. Exact per-field source locators should be added; this is stronger than citing just the coarse logarithmic corollary. |
| [hTraceyPerm : TraceyPermutationGeneratorInput](SymmetricSubgroupAsymptotics/TraceyAffineInducedModuleInput.lean) | Transitive degree w≥2 group generated by≤ceil(w/√log₂w). | weakening; TR Thm1.1(1), constantc<1. Not the sharper2021 √3/2 bound. |
| [hSimpleGen : FiniteSimpleTwoGeneratorBound](SymmetricSubgroupAsymptotics/ActualWreathSemisimpleCoefficient.lean) | Every finite centerless simple group has≤2 generators. | Guralnick–Kantor, Journal of Algebra 234 (2000), Theorem I, p.744 and Corollary p.745; LIT-SIMPLE-2GEN. |
| [smallAffineCatalogue : SmallAffineCatalogueDegreeEightConsequences.PublishedRemainingClassification](SymmetricSubgroupAsymptotics/SmallAffineCatalogueDegreeEightConsequences.lean) | Actual affine complement in degree16/27 is isomorphic to one of the fixed31 named carriers. Degree8 is proved internally from complete GL(3,2) subgroup coverage. | Roney-Dougal–Unger2003 plus pinned PrimGrp3.4.4. Solvability/chief-saving and exact maxima are constructed, not supplied. |
| [hSolubleBase : HalasiMarotiSolubleIrreducibleCubeBound](SymmetricSubgroupAsymptotics/PrimitiveAffinePublishedSmallStructuralInput.lean) | Faithful irreducible soluble linear G on V over prime field has card(G)≤card(V)³. | corollary; Halasi–Maróti, ProcAMS144 (2016),3231–3242, Thm1.1 authorp2 strong-base≤3. LIT-AFFINE-BASE. |
| [hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds](SymmetricSubgroupAsymptotics/PrimitiveSocleRawSimpleIndex.lean) | For the actual least proper subgroup index ℓ of a finite nonabelian simple T: ℓ² < card(T) and card(Out(T)) ≤ 3 log₂ ℓ. | Ballester-Bolinches–Esteban-Romero–Jiménez-Seral, Theorem A(4), p.4 of arXiv:2203.16976v2; LIT-SIMPLE-INDEX. The bound ℓ ≥ 5 and all profile deductions are internal. |
| [catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence](SymmetricSubgroupAsymptotics/PrimitiveCatalogueClassificationPublished.lean) | Bare faithful primitive degree5–29 correspondence, actual group/socle exact orders and one-factor structural match. | PRIM degree5–29 pinned116 retained rows; inequality2outer≤degree kernel-checked internally. |
| [hTraceySoluble : TraceySolubleOrbitInducedModuleInput](SymmetricSubgroupAsymptotics/TraceySolubleOrbitInducedInput.lean) | Actual soluble subgroup, actual2-complement, local dual nonzero-orbit count and all actual N-orbit E_sol bounds give induced submodule generators. | specialization; TR Thm4.24(ii)(b), Cor4.25(ii)(b), H₁=H,F₂. Keep both exact locators; this is not merely Thm1.6 coarse formula. |
| [hMN : McIverNeumannPermutationGeneratorBound](SymmetricSubgroupAsymptotics/McIverNeumannPermutationSection.lean) | Every subgroup of S_s except literally fullS3 has≤floor(s/2) generators. | Blackburn–Neumann–Venkataraman, Enumeration of Finite Groups (2007), Lemma 5.2; proof reference Cameron–Solomon–Turull, Journal of Algebra 127 (1989), §4; LIT-MCIVER-NEUMANN. |
| [published8 : DegreeEightCanonicalCatalogue.PublishedClassification](SymmetricSubgroupAsymptotics/PrimitiveAffineEightCanonicalCatalogue.lean) | Every actual transitive nonbinary subgroup of S8 is point-conjugate to one of24 pinned canonical actions. | Butler–McKay 1983, degree-eight classification; official TransGrp manual, with the 26 binary actions excluded from the 50-action list. |
| [published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification](SymmetricSubgroupAsymptotics/PrimitiveAffineSixteenCanonicalCatalogue.lean) | Every primitive subgroup of S16 point-conjugate to one of22 canonical actions:20 affine +naturalA16/S16. | PRIM degree16. NOT an all1954 transitive16 or527 semantic-source assumption. |
| [publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification](SymmetricSubgroupAsymptotics/DegreeTwelveCanonicalCatalogueLocator.lean) | Every transitive subgroup of S12 point-conjugate to one of fixed301 literal tops. | Royle, Journal of Symbolic Computation 4(2) (1987), 255–268, degree-twelve classification of 301 actions; official TransGrp manual. |

The degree-eight affine-complement branch is also a checked theorem: the
finite adjunction-closure proof covers all15 actual GL(3,2) subgroup classes,
nonzero invariant vector/dual flags exclude12, and literal linear
intertwiners identify the three survivors with the fixed canonical groups.
The small-affine parameter therefore retains only degrees16 and27; it has
31 remaining rows. This is a scope reduction, not a claim that the full
eight-point transitive-action classification is proved.

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
and the final exported-declaration axiom audit, passed on 20 October 2026.
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
| Final composition | [T1RelativeClosure](SymmetricSubgroupAsymptotics/T1RelativeClosure.lean), [MarkedC4PublishedGeometricTargets](SymmetricSubgroupAsymptotics/MarkedC4PublishedGeometricTargets.lean) | Complete remainder estimate and final T1/AllTargets exports. |
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

The public import closure contains **5,872 project modules**. On
20 October 2026, recursive verification matched their current sources,
compiled objects, direct dependency fingerprints, and pinned toolchain
against successful check receipts. Matching historical receipts were reused
with explicit relocation evidence; stale consumers were checked serially.
All sources in this closure are tracked in the main checkout and match the
audited bytes. Optional modules outside this public closure are not covered
by this release claim.

A fresh axiom audit of `T1_of_published_inputs`,
`allTargets_of_published_inputs`, `T2_of_T1`, `T3_of_T1`,
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

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
| `SymmetricSubgroupAsymptotics.lean` | Root import module. Individual theorem modules can be checked separately. |
| `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` | Pinned compiler, package configuration, and exact dependencies. |
| `../scripts/check_lean.py` | Serialized compiler runner with memory, RSS, and wall-time limits. |
| `../scripts/check_lean_closure.py` | Dependency-order planning and conservative serial resume for a local module closure. |
| `../computations/python/` | Reproducible producers for the retained finite certificates. |

Build logs, receipts, scratch proofs, and research status records are kept
outside the publication repository.

## Explicit input boundary

The final exports are
[T1_of_published_inputs](SymmetricSubgroupAsymptotics/MarkedC4PublishedGeometricTargets.lean)
and `allTargets_of_published_inputs`. Their **50 named inputs** are listed
below. The character bundle has four fields; ordinary abelianization is
also passed separately as `hKP`. These are explicit theorem parameters,
not new Lean axioms. The kernel audit of both exports uses only `propext`,
`Classical.choice`, and `Quot.sound` in addition to the stated parameters.

RDT means Roney-Dougal–Tracey, arXiv:2503.05416v1. TR means Tracey's
2018 transitive-generation paper, with page locators referring to its linked
author manuscript. HRD means Holt–Roney-Dougal (2013); GPRV means
Glasby–Praeger–Rosa–Verret (2018). PRIM means the published primitive
classifications and pinned PrimGrp 3.4.4; TRANS means the published
transitive classifications and pinned TransGrp 3.6.5. CLASS means the
Garonzi–Maróti and Maróti class-number theorems. Full titles, links, and
version conventions appear in the [literature register](../provenance/LITERATURE.md).

Finite correspondence inputs identify the **actual pinned representatives**.
The strict-head and bounded-socle correspondences additionally retain their
stated normal-subgroup/socle structure; they are not merely point-conjugacy
locators. None supplies a project head, capacity, marked moment, complete
source, or asymptotic target bound. The ordinary coarse subgroup upper bound
and labelled transitive-count theorem are retained published counting inputs.

| Lean parameter and definition | Mathematical input | Published source or correspondence |
|---|---|---|
| [lit : PreE7CharacterLiterature](SymmetricSubgroupAsymptotics/Non2PreE7CharacterCertificateTemplate.lean) | Four fields: permutation class number ≤5^((b−1)/3) for b≥4; abelianization ≤3^(b/3); every abelian binary quotient ≤2^(b/2); nilpotent permutation class number ≤(38/25)^b. | CLASS and KP. Small b and uniform weakenings internal. |
| [hZmud : ZmudFaithfulCharacterTupleInput](SymmetricSubgroupAsymptotics/ZmudFaithfulCharacterInput.lean) | t normal generators of the actual socle give t jointly faithful finite irreducible complex representations of any finite G. | Steinberg, arXiv:2201.09129v1, Corollary 2.25 (Zmud′), printed p.19; relative Theorem 2.24, p.18. Specialize to complex characteristic zero; the trivial-group/empty-tuple seam is elementary. |
| [hClifford : CliffordRawRestriction.Input](SymmetricSubgroupAsymptotics/CliffordRawRestrictionInput.lean) | Restriction of an irreducible finite-dimensional representation to an actual normal subgroup is semisimple; irreducible constituent types are conjugate. | Tracey thesis2017 printedp14, Thm2.3.1(i),(ii), Remark2.3.4, citing Curtis–Reiner Thm49.7. Actual retained faithfulness is proved internally. |
| [hcomp : PrimitiveCompositionLengthInput](SymmetricSubgroupAsymptotics/PrimitiveCompositionLengthInput.lean) | Every actual composition series of primitive degree r≥2 has length ≤(8/3)log₂r−4/3. | GPRV Thm1.3. |
| [hsub : PublishedSolubleSubdirectHeight](SymmetricSubgroupAsymptotics/MarkedC4PublishedOrdinaryNilpotentGeneration.lean) | Soluble subdirect product socle length ≤maximum factor socle length. | RDT Lemma8.5 p33. |
| [hseven : PublishedTheoremSeven](SymmetricSubgroupAsymptotics/MarkedC4PublishedOrdinaryNilpotentGeneration.lean) | Soluble G with socle length ≤L and abelian-section prime-factor length ≤M is generated by a nilpotent subgroup plus ≤4L√M elements. | RDT Thm7 p3, proofpp32–33. |
| [h55 : PublishedTheorem55Binary](SymmetricSubgroupAsymptotics/MarkedC4RDTOriginalWordStructure.lean) | Actual bounded binary subdirect word, dependent/tail degrees: normal-generation bounds3x/8+y/2,5x/16+y/2,x/4+y/2 with exact excess exclusions. | RDT Thm5.5(ii) p17. |
| [h53 : ActualCaseIITargetStructure.PublishedProposition53Binary](SymmetricSubgroupAsymptotics/MarkedC4ActualCaseIITargetStructure.lean) | Binary excess classification: excess1/2, degree≤32; exact excess2 degrees and excess1 normal restrictions. | RDT Prop5.3(i) p16. |
| [h57 : RDTExcessStructure.PublishedTheorem57Binary](SymmetricSubgroupAsymptotics/MarkedC4RDTExcessStructure.lean) | Actual nonabelian normal quotient admits normal F with logcard([F,Q])+e logcard(C_Q(F))≤n/2 and centralizer log≤n/4, exact branch e and generator equality. | RDT Thm5.7 pp18–19. |
| [h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional](SymmetricSubgroupAsymptotics/MarkedC4RDTDegreeEightExceptional.lean) | Degree8/excess2 nonabelian quotient: denominator trivial, center log1, derived-plus-three-center log4. | RDT Thm5.7(i) p18 and Prop7.4 CaseIIa p25. This includes the forcing consequence, not merely the displayed theorem inequality. |
| [hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary](SymmetricSubgroupAsymptotics/MarkedC4RDTDerivedNormalQuarter.lean) | Nonabelian transitive binary G, degree n>2, normal N≤G′: d_G(N)≤n/4. | RDT Prop5.3(i), used in Thm5.5(iii) proofp17. |
| [rdt46 : RDTTheorem46BinaryInput](SymmetricSubgroupAsymptotics/MarkedC4RDTNormalFInterface.lean) | Bounded-factor binary epimorphism theorem with arbitrary actual normal F, centralizer/commutator and original derived-normal projection-kernel generation bound. | RDT Thm4.6 pp12–13. No marked count is imported. |
| [hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper](SymmetricSubgroupAsymptotics/MarkedC4OrdinarySubgroupUpper.lean) | ∃β, s_n≤2^(n²/16+βn√n), n>1. | RDT Thm1 p1. Strong quantitative coarse bound, not merely an asymptotic main term. |
| [h62 : PublishedProposition62](SymmetricSubgroupAsymptotics/MarkedC4LargeOrbitOrdinaryGeneration.lean) | For any positive rate, sufficiently large nontrivial-orbit cutoff makes soluble permutation generator number ≤rate×degree. | RDT Prop6.2 p21. |
| [h86 : PublishedTheorem86Representatives](SymmetricSubgroupAsymptotics/MarkedC4SolubleContainerCount.lean) | At most2^(13n) actual conjugacy representatives cover maximal transitive soluble subgroups. | RDT Thm8.6(i) p34, citing Pyber Lemma3.2; weakened numerical menu form. |
| [hDixon : PublishedDixonOrder](SymmetricSubgroupAsymptotics/MarkedC4SolubleContainerOrder.lean) | Soluble H≤S_n has card(H)≤24^(n/3). | Dixon bound as RDT Thm8.6(ii) p34. Original Dixon paper/locator not yet registered separately. |
| [hAG : PublishedAschbacherGuralnickSolubleGeneration](SymmetricSubgroupAsymptotics/MarkedC4AschbacherGuralnickSolubleGeneration.lean) | Every finite group generated by a soluble subgroup and one element. | Aschbacher–Guralnick, J.Algebra77 (1982),189–201; RDT Thm8.4 p32. Ambient-recovery field internal. |
| [hTracey : TraceyBinaryFormulaInput](SymmetricSubgroupAsymptotics/TraceyBinaryFormulaInput.lean) | Invariant head of every binary transitive permutation submodule satisfies exact E_sol binary-part/binomial bounds OR E largest-prime-power bound. | specialization; TR Def1.5/Thm1.6 pp2–3, a=1/trivial stabilizer module. No5/16 field. |
| [hSolubleFormula : TraceySolublePermutationFormulaRawInput](SymmetricSubgroupAsymptotics/TraceySolublePermutationFormulaRaw.lean) | Uniform module generators in the soluble transitive permutation specialization satisfy exact E_sol formula. | specialization; TR Def1.5/Thm1.6 pp2–3. |
| [hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput](SymmetricSubgroupAsymptotics/TraceyCorollaryThreeTwelveRaw.lean) | Exceptional degree3·2^m action has actual soluble subgroup and full binomial orbit partition, Mersenne exponent≥3. | TR Cor3.12 p17 PLUS preceding nonabelian PSL₂(p) construction Thm1.8/Cor3.11 excluding p=3. Cor3.12 alone is insufficient for exponent≥3. |
| [compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence](SymmetricSubgroupAsymptotics/PrimitiveTernaryThreeTenthsPublished.lean) | Faithful primitive degree<45 matches336 pinned rows; exact degree and order, or natural A_n/S_n identification. | PRIM degrees2–44. No ternary inequality field. |
| [hDegreeNine : PublishedPrimitiveDegreeNineClassification](SymmetricSubgroupAsymptotics/PrimitiveTernaryChiefWeightPublished.lean) | Primitive degree9 has one of seven distinct orders (36,72,144,216,432,504,1512) or is natural A9/S9. | PRIM degree9 eleven-row slice; order coincidences deliberately merged. |
| [hPrimitiveGen : PrimitiveNormalGeneratorInput](SymmetricSubgroupAsymptotics/C1PrimitiveTail.lean) | Normal subgroup of primitive degree w≥4 has ordinary rank≤floor(log₂w). | HRD Thm1.1 normal specialization, sole degree3 exception excluded. |
| [strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence](SymmetricSubgroupAsymptotics/PrimitiveTernaryStrictHeadPublished.lean) | Primitive degree<34 matches253 rows with actual normal minimal self-centralizing E and exact card(G/E). | plus standard primitive structure; PRIM degrees2–33. `PrimitiveStrictHeadSocleMatch` supplies E/minimality/selfCentralizing, not only a row index; document this enriched structural correspondence. No head capacity field. |
| [primitiveSix : PublishedPrimitiveDegreeSixClassification](SymmetricSubgroupAsymptotics/PrimitiveDegreeSixChiefPublished.lean) | Primitive degree6 group is A5,S5,A6 orS6. | PRIM degree6 slice; abstract group identifications suffice. |
| [hKP : KovacsPraegerAbelianizationBound](SymmetricSubgroupAsymptotics/KovacsPraegerAbelianization.lean) | card(J/J′)≤3^(b/3) for J≤S_b. | Kovács–Praeger, Corollary p.284, LIT-KP. This input repeats `lit.kovacsPraeger`. |
| [hLMM : LucchiniMenegazzoMorigiTransitiveCountInput](SymmetricSubgroupAsymptotics/Non2PreE7MenuMassAggregation.lean) | Labelled transitive subgroup count is subquadratic-exponential. | Lucchini–Menegazzo–Morigi, BLMS32 (2000),191–195; exact labelled2^(Cn²/√logn) statement is sourced through RDT introductionp2. ID LIT-TRANSITIVE-COUNT. |
| [hHoltRoneyDougal : FaithfulSimplePermutationGeneratorBound](SymmetricSubgroupAsymptotics/SemisimpleOuterFactorPublished.lean) | Centerless finite simple group faithfully permuting w points generated by≤floor(log₂w). | corollary; HRD Thm1.1 by nontrivial orbit/maximal point stabilizer; S3 exception impossible. This corollary's short derivation is documented, not yet a separate raw-HRD adapter. |
| [hTraceyHalf : TraceyAffineHalfInducedModuleInput](SymmetricSubgroupAsymptotics/TraceyAffineInducedModuleInput.lean) | Every submodule of actual induction from index s≥2 is generated by≤floor(a s/2). | numerical specialization; TR Thm1.6/Cor4.27(iii). Precise half-bound lemma-to-formula derivation is not separately constructed at this boundary. |
| [hTraceyLog : TraceyAffineInducedModuleInput](SymmetricSubgroupAsymptotics/TraceyAffineInducedModuleInput.lean) | Every submodule generated by≤ceil(4as/√log₂s). | weakening; TR Cor4.27(iii), manuscriptpp30–31. |
| [hTraceyRefined : TraceyRefinedInducedModuleInput](SymmetricSubgroupAsymptotics/TraceyRefinedAffineInput.lean) | One generating-tuple length simultaneously satisfies half, logarithmic, prime-to-characteristic, primary-square-root and soluble prime-power binomial ceilings. | numerical specialization; TR Def1.5/Thm1.6 and Cor4.26–4.27. Exact per-field source locators should be added; this is stronger than citing just the coarse logarithmic corollary. |
| [hTraceyPerm : TraceyPermutationGeneratorInput](SymmetricSubgroupAsymptotics/TraceyAffineInducedModuleInput.lean) | Transitive degree w≥2 group generated by≤ceil(w/√log₂w). | weakening; TR Thm1.1(1), constantc<1. Not the sharper2021 √3/2 bound. |
| [hSimpleGen : FiniteSimpleTwoGeneratorBound](SymmetricSubgroupAsymptotics/ActualWreathSemisimpleCoefficient.lean) | Every finite centerless simple group has≤2 generators. | Guralnick–Kantor, Journal of Algebra 234 (2000), Theorem I, p.744 and Corollary p.745; LIT-SIMPLE-2GEN. |
| [smallAffineCatalogue : SmallAffineCanonicalRepresentatives.PublishedClassification](SymmetricSubgroupAsymptotics/SmallAffineCanonicalRepresentatives.lean) | Actual affine complement in degree8/16/27 is isomorphic to one of fixed34 named carriers. | Roney-Dougal–Unger2003 plus pinned PrimGrp3.4.4. Solvability/chief-saving and exact maxima are constructed, not supplied. |
| [hPSLThree : StandardThreeDimensionalLinearGroups.PublishedSimplicity](SymmetricSubgroupAsymptotics/StandardThreeDimensionalLinearGroups.lean) | PSL₃(F₂), PSL₃(F₃) are simple. | Classical projective-linear simplicity; Conrad, Simplicity of PSL_n(F), §4; LIT-CLASSICAL-PSL3. Exact GL/SL orders and determinant split are internal. |
| [hBurnside : PublishedBurnsideTwoPrimeSolvabilityInput](SymmetricSubgroupAsymptotics/PublishedBurnsideTwoPrimeSolvability.lean) | Every finite group of order p^a q^b is soluble. | Burnside, Proc. London Math. Soc. s2-1 (1904), 388–392; LIT-BURNSIDE-TWO-PRIMES. |
| [hProjectiveFive : StandardGLTwoFiveProjective.PublishedProjectiveIsomorphism](SymmetricSubgroupAsymptotics/StandardGLTwoFiveProjective.lean) | Nonempty(PGL₂(F₅)≃S5), with Mathlib PGL=GL/center. | Adler, Pacific Journal of Mathematics 155(1) (1992), Lemma 13, printed p.17; LIT-PGL2FIVE. Scalar kernel and character are internal. |
| [hSolubleBase : HalasiMarotiSolubleIrreducibleCubeBound](SymmetricSubgroupAsymptotics/PrimitiveAffinePublishedSmallStructuralInput.lean) | Faithful irreducible soluble linear G on V over prime field has card(G)≤card(V)³. | corollary; Halasi–Maróti, ProcAMS144 (2016),3231–3242, Thm1.1 authorp2 strong-base≤3. LIT-AFFINE-BASE. |
| [hAffineFive : PublishedDegreeFiveAffineClassification](SymmetricSubgroupAsymptotics/PrimitiveAffinePublishedSmallStructuralInput.lean) | Primitive affine degree5 group C5,D10 or naturalF20 with point relabelling. | Elementary degree-five specialization of affine primitive structure (Liebeck–Praeger–Saxl 1988, type I, p.390) and GL₁(F₅) ≅ C₄. No capacity estimate is supplied. |
| [hONanScott : PrimitiveSocleRawStructure.PublishedONanScottStructure](SymmetricSubgroupAsymptotics/PrimitiveSocleRawONanScott.lean) | An actual finite faithful primitive action has either a regular normal prime-power subgroup (elementary abelian by primitive affine structure), or its full socle is T^k with an actual quotient embedding into Out(T) ≀ S_k and the exact proper-index/order degree alternatives. No numerical compression bound. | Liebeck–Praeger–Saxl 1988, §1 pp.390–392 and theorem p.392; LIT-ONAN-SCOTT. Includes both minimal normals in the two-regular-socle cases. |
| [hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds](SymmetricSubgroupAsymptotics/PrimitiveSocleRawSimpleIndex.lean) | For the actual least proper subgroup index ℓ of a finite nonabelian simple T: ℓ² < card(T) and card(Out(T)) ≤ 3 log₂ ℓ. | Ballester-Bolinches–Esteban-Romero–Jiménez-Seral, Theorem A(4), p.4 of arXiv:2203.16976v2; LIT-SIMPLE-INDEX. The bound ℓ ≥ 5 and all profile deductions are internal. |
| [catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence](SymmetricSubgroupAsymptotics/PrimitiveCatalogueClassificationPublished.lean) | Bare faithful primitive degree5–29 correspondence, actual group/socle exact orders and one-factor structural match. | PRIM degree5–29 pinned116 retained rows; inequality2outer≤degree kernel-checked internally. |
| [hTraceySoluble : TraceySolubleOrbitInducedModuleInput](SymmetricSubgroupAsymptotics/TraceySolubleOrbitInducedInput.lean) | Actual soluble subgroup, actual2-complement, local dual nonzero-orbit count and all actual N-orbit E_sol bounds give induced submodule generators. | specialization; TR Thm4.24(ii)(b), Cor4.25(ii)(b), H₁=H,F₂. Keep both exact locators; this is not merely Thm1.6 coarse formula. |
| [hMN : McIverNeumannPermutationGeneratorBound](SymmetricSubgroupAsymptotics/McIverNeumannPermutationSection.lean) | Every subgroup of S_s except literally fullS3 has≤floor(s/2) generators. | Blackburn–Neumann–Venkataraman, Enumeration of Finite Groups (2007), Lemma 5.2; proof reference Cameron–Solomon–Turull, Journal of Algebra 127 (1989), §4; LIT-MCIVER-NEUMANN. |
| [publishedSix : PublishedDegreeSixThreeByTwoAffineClassification](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeSixPublishedClassification.lean) | Actual degree6 two-triple affine/nontrivial-sign cell is S3×C2,S3²,3²:C4 orS3≀C2, with actual group charts; 3²:C4 includes irreducible complement chart. | Butler–McKay, Communications in Algebra 11(8) (1983), 863–911, degree-six classification; official TransGrp manual and pinned representative numbering. The retained irreducible affine chart is structural correspondence. |
| [published8 : DegreeEightCanonicalCatalogue.PublishedClassification](SymmetricSubgroupAsymptotics/PrimitiveAffineEightCanonicalCatalogue.lean) | Every actual transitive nonbinary subgroup of S8 is point-conjugate to one of24 pinned canonical actions. | Butler–McKay 1983, degree-eight classification; official TransGrp manual, with the 26 binary actions excluded from the 50-action list. |
| [published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification](SymmetricSubgroupAsymptotics/PrimitiveAffineSixteenCanonicalCatalogue.lean) | Every primitive subgroup of S16 point-conjugate to one of22 canonical actions:20 affine +naturalA16/S16. | PRIM degree16. NOT an all1954 transitive16 or527 semantic-source assumption. |
| [publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification](SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoThreePairsRawPackage.lean) | Every actual transitive nonbinary degree6 three-pair action has one of fixed easy/central abstract group charts. | Butler–McKay 1983, degree-six classification and the official TransGrp representative correspondence. No source inequality is supplied. |
| [publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification](SymmetricSubgroupAsymptotics/DegreeTwelveCanonicalCatalogueLocator.lean) | Every transitive subgroup of S12 point-conjugate to one of fixed301 literal tops. | Royle, Journal of Symbolic Computation 4(2) (1987), 255–268, degree-twelve classification of 301 actions; official TransGrp manual. |
| [hFS : FusariSpigaBinaryNormalSubgroupInput](SymmetricSubgroupAsymptotics/Non2PreE7Sns2MenuMass.lean) | For a finite 2-group of order 2^l, #normalSubgroups(G) · 2^(−l²/4) ≤ 8 · 2^(2l). | Fusari–Spiga, Journal of Algebra 635 (2023), Theorem 1.1, p.487; LIT-ORDER-COUNT. Count normal subgroups by all subgroups and weaken the published constant to eight. |

The quantitative `PublishedPrimitiveSocleDichotomyInput` is constructed by
`PublishedONanScottStructure.toSocleDichotomy`; it is not an additional
parameter here. Likewise the complete small-affine receipt, degree-25
scalar datum and chief bound, exceptional Tracey `5/16` deduction, actual
Clifford faithfulness, all low-degree source data, marked-C₄ moment, and
`PreE7PrimitiveAffineConsumerData` are internal conclusions. The weaker
`PermutationSubgroupGeneratorBound` is derived from `hMN`, including the
full `S₃` exception.

The final facade and root import pass current checks. The independent
mathematical input audit is closed at this boundary; the full transitive
source/object receipt audit is still running. These are separate claims.

## Proof organization

The final composition follows this chain:

1. Raw published structure and formulas construct the finite affine package,
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

The final T1 and AllTargets declarations, root import, and raw-input
constructors pass current source checks. Eleven target/helper exports have
standard-only axiom audits. The remaining release task is recursive
source/object correspondence throughout the public import graph, reusing
matching evidence and rechecking stale modules serially. Logs, relocation
attestations, and status records stay outside this repository. Pinned
external Lean/mathlib objects form a separate dependency boundary.

A standard-only `#print axioms` result excludes extra Lean axioms and native
computation acceptance from that theorem. It does not prove its explicit
published hypotheses or certify stale source objects. The release claim
requires the explicit mathematical boundary above, current kernel checks,
and matching dependency provenance together.

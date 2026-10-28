# Compatibility with the completed AxiomMath CFSG formalization

The compatibility sources use [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG)
revision `69cb972f587a3ecc035e092253167ff2e303c962` and its TauCeti dependency,
revision `6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`. The upstream environment
is Lean `4.35.0-rc3` with mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`. This project's environment and
the concrete classification statement described in [CFSG_SOURCE.md](CFSG_SOURCE.md)
remain pinned independently. No proof object is imported across Lean versions.

The upstream classification concludes in TauCeti's concrete catalogue. It is
not definitionally this project's `CFSG.CFSGClassification`: the latter uses
the older concrete models. Reusing the completed classification requires an
actual common-toolchain proof and a transport of the concrete models, or a
replacement backend with the required quantitative theorems proved for its
own models. These compatibility modules do not assert that this integration
has been completed.

Selected checks in the pinned upstream toolchain now prove transports
for the actual cyclic and alternating carriers and all valid untwisted-A,
type-C and type-D carriers. The type-B rank-two and characteristic-two
route maps to a literal old type-C entry of the non-disjoint historical
catalogue. It uses the actual spin fixed-point comparison and symplectic
perfectness, followed by the proved original-C equivalence; its 18 audited
exports use only `propext`, `Classical.choice`, and `Quot.sound`.
The remaining odd-characteristic, rank-at-least-three type-B route is also
checked. It preserves the actual Frobenius fixed field, root subgroups,
quadratic frame and full-center quotients through the literal original
B-transpose projective Serre group. Its selected closure has 1,150 checked
source modules, 32 standard-axiom audit exports and 6,339 verified unique
source, object, dependency and toolchain fingerprints. It assumes no
source simplicity, order or model-recognition statement.
These selected comparisons have not yet been composed with the full
completed-classification theorem or the T1 endpoint, and no cross-version
proof object is reused.

In the publication toolchain, the original odd-characteristic B and D
projective equivalences and the actual integral/tensor Lie structures
are now proved. Their common source-spanning and doubled-coordinate
arguments require no old-model simplicity or source-recognition input.
The type-D continuation now proves the original-model equivalence over
EVERY field, using the actual intrinsic integral parity lattice, a proved
basis, centrality of the possible ambient kernel, and source perfectness.
Its 54 audited exports use only the three standard axioms above; it does
not assume original-model simplicity or source faithfulness. These results
provide the original-model side of further concrete transports. The actual
upstream type-D comparison now also passes over every valid coefficient
field: its selected closure has 1,172 checked source modules, with two
standard-axiom audit exports and current source, object, dependency and
toolchain fingerprints. It retains the actual validated constructor and
coefficient field. The other remaining family comparisons and the full
classification/T1 composition still require their own checks.

## Definition and presentation ports

`Axiom69NativeMatrixDefinitionPort.lean` retains the formulas for
`asciiWhitespace`, `decode`, and `seedMonoid` from
[`CFSG/Blueprint/NativeSporadic.lean`](https://github.com/AxiomMath/CFSG/blob/69cb972f587a3ecc035e092253167ff2e303c962/CFSG/Blueprint/NativeSporadic.lean).
Only imports, namespace packaging, and module visibility syntax are adapted.
It ports definitions, not upstream classification, order, simplicity, or
recognition proofs. The implementation is Apache-2.0, as specified by the
[upstream license](https://github.com/AxiomMath/CFSG/blob/69cb972f587a3ecc035e092253167ff2e303c962/LICENSE).

`CFSGCoTwoTauCetiPresentationCore.lean` is a narrow Apache-2.0 port of
TauCeti's `GroupTheory/Presentation/Relator.lean`,
`GroupTheory/Presentation/GroupPresentation.lean`, and
`GroupTheory/SpecificGroups/CFSG/Sporadic/Conway/Two.lean` at the revision
above. The source preserves the attribution header. It retains the relator
syntax, its interpretation and compiler correctness, the presentation
carrier, and the literal Co₂ presentation. It omits unrelated algorithms,
metadata checks, and theorems about the order and recognition of Co₂.

`CFSGJankoThreeTauCetiPresentationCore.lean` adds the literal J3 row
from TauCeti's `GroupTheory/SpecificGroups/CFSG/Sporadic/Janko/Three.lean`
at the same revision, reusing that checked presentation compiler. Its
metadata and attribution are retained. The companion
`CFSGJankoThreeTauCetiPresentationEquiv.lean` proves equality of all eight
interpreted and compiled relators and gives a generator-preserving
isomorphism from the original presentation. This is a presentation
transport, not a port of J3's order or outer-automorphism theorems.

The same checked compiler is reused by the narrow presentation cores for
J1, J4, HS, McL, He, M23 and M24. Each records the literal corresponding
TauCeti row at the same pinned revision and retains its Apache-2.0
attribution. Their companion `*TauCetiPresentationEquiv.lean` modules
prove generator-preserving equivalences to the original project
presentations, without finiteness or simplicity hypotheses. For He, the
same seven relation words have a different order; an explicit list
permutation proves equality of their defining sets. These ports do not
import the actual TauCeti package alongside duplicate local definitions,
and do not by themselves import its numerical sporadic theorems.

`CFSGCoTwoTauCetiPresentationEquiv.lean` proves equality of the interpreted
relator lists and defining sets, then constructs an equivalence from the
original project Co₂ presentation to this port of the TauCeti presentation.
It fixes both displayed generators. This equivalence does not require an
assumption identifying two groups by their conventional names or orders.

## Shared matrix bridge

`FiniteMonoidGeneratedUnitsEquivalence.lean` and
`MatrixSeedMonoidUnitsEquivalence.lean` are project proofs. In a finite
ambient monoid, the units of a submonoid generated by given seeds correspond
to the subgroup generated by units whose values are seeds. The matrix
specialization applies this to the two actual decoded matrices and retains
the underlying matrix values. It does not assume that arbitrary supplied
seeds are invertible.

A concrete application must prove equality of both decoded matrices. An
equality of filenames, file hashes, dimensions, or conventional group names
is not that proof. The existing notice concerning the provenance of the
external matrix data in [CFSG/NOTICE.md](CFSG/NOTICE.md) continues to apply;
the implementation license is not a claim of a blanket license over ATLAS
data.

## Selected finite witnesses

The Co1 positive word used in
`CFSGCoOneSelectedUpstreamPositiveWord.lean` is motivated by the literal
signed word in `Certificates/Data/CFSGNative/Co1/Data.lean` at the AxiomMath
revision above. The certificate proves the positive word's selected
period directly on the original project matrices. It does not assume the
upstream whole-word order or the intermediate inverse reductions.

The Co2 certificate uses the two explicit binary 22-dimensional seeds from
`CFSG/Blueprint/Data/Co2G1-f2r22B0.m1` and `.m2` at that revision. Every
coefficient and all ten original presentation relations are checked by
`CFSGCoTwoNativeTwentyTwoRelatorIdentities.lean` and its imported finite
certificates. The selected word is `A * B^3 * A * B * A * B^2`.
`CFSGCoTwoSelectedWordTwentyThreePrimeDivisor.lean` proves its consequence
for the original presented group from an actual homomorphism and selected
vector period, without asserting equality with the whole matrix group or
using its claimed order. The external-data notice above applies here too.

The J2 certificate uses the explicit 14-dimensional seeds over `F₅`
and the fixed 24-instruction local program in
`Certificates/Data/CFSGNative/SectionRank/J2Local.lean` at the AxiomMath
revision above. `CFSGJankoTwoSelectedMatrixIdentities.lean` retains all
five original relators and the exact Heisenberg/Singer identities through
100 checked matrix products. `CFSGJankoTwoActualHeisenbergFrame.lean`
pulls the configuration back through a nontrivial homomorphism from the
original simple presentation. It assumes no target recognition, whole
group order, or order of the normalizing element. The external-data notice
above continues to apply.

`CFSGJankoTwoBinaryRecoveryMatrixEquality.lean` reuses these same original
J2 seeds and proves a further fixed recovery word through 32 whole
14-by-14 matrix products. `CFSGJankoTwoDihedralBinaryGoodSylow.lean`
pulls this equality back to the original presentation using inherited
simplicity. Its binary dihedral subgroup and actual conjugate recover
the original second generator. This uses no additional external matrix
dataset, group-order assertion, or named-model recognition hypothesis.

`CFSGJankoOnePerm266Pilot.lean` records two permutations derived from Kenta's
[`FiniteSimpleGroups/Sporadic/J1/Permutations.lean`](https://github.com/KitaKen1/finite-simple-groups-lean/blob/7f09e33a9ceef6b59ce03e34cd4f0558c763e325/FiniteSimpleGroups/Sporadic/J1/Permutations.lean),
at revision `7f09e33a9ceef6b59ce03e34cd4f0558c763e325`, using fixed words
and an opposite-action translation. The Apache-2.0
attribution is retained. The new reflection certificates check the two
inverse tables and all five original J1 presentation relations at every
point. The induced action yields a proper point stabilizer of index at
most 266. Neither its order nor recognition as the whole J1 group is
assumed. This supplies only the stated index bound, not J1's complete
numerical callback.

## Project bridge proofs

The uniform symplectic root-coordinate, integral splitting, saturation,
and primitive-image lemmas are project proofs for the original rational
Serre quotient and its integral lattice. They do not import a source-basis
or faithfulness assertion from a similarly named matrix model.
`CFSGSymplecticOriginalFirstActionSpan.lean` proves spanning of that
actual lattice and injectivity after every commutative base change.
`CFSGSymplecticOriginalProjectiveEquivalence.lean` then identifies the
original projective Serre group with the independent natural elementary
symplectic projective group, without an old-model simplicity premise.
These checked results do not assert that the full common-toolchain CFSG
bridge has been completed.

`SolubleSylowNormalizerPrime.lean` and its semisimple and Suzuki
assemblers are also project proofs. They replace the stronger requirement
of generation by two Sylow conjugates with generation by two conjugates
of a soluble Sylow normalizer. The accompanying maximality and
two-overgroup criteria require actual Sylow normalizers and actual
overgroup data. The strongest T1 endpoint still explicitly takes the
concrete classification and the twelve remaining sporadic witnesses.

## Literal nonsplit-torus lemmas

`PSLTwoLiteralNonsplitTorusCyclic.lean` uses the actual Mathlib SL₂ and PSL₂
carriers and a norm-one quadratic-algebra embedding. It proves cyclicity
without a classification assumption.

`PSLTwoLiteralNonsplitNormalizerStructure.lean` adapts the elementary matrix
calculations in AxiomMath/CFSG's
`CFSG/CharacterTheory/PSL2Table/{Basic,Conjugacy}.lean` at the revision above,
under Apache-2.0. Imports are narrowed and the proof is adapted to this
project's Mathlib APIs and literal torus. Its normalizer statement retains
the explicit noncentral torus-element hypothesis. It does not assume a
classification of PSL₂ subgroups or import the full CFSG proof.

## Reusable original ADE source proofs

The publication toolchain checks the original norm-two source construction,
its signed involution, primitive-image induction and weight support. The
seven-module continuation ending in
`CFSGNormTwoNativePositiveSourceStability.lean` and
`CFSGNormTwoSignedSourceSpan.lean` has 26 audited exports with only the
standard three axioms. It derives the source action and spanning statements
from an actual target basis and primitive image data; it assumes neither
source faithfulness nor an action table. Concrete exceptional installers
and the final common-toolchain group comparisons remain separate checks.

A selected common-toolchain check also proves equality of both literal
original Co3 matrices with the actual native decoder outputs, giving the
matrix-group equivalence with four audited exports using the standard three
axioms. This identifies the actual native matrix carrier, not yet the
classified TauCeti presentation. No order, simplicity or model-recognition
premise enters the matrix equivalence, and no T1 callback is removed by it.

## Internal extended-catalogue assembly

`CFSGCatalogueWithAxiomMonster.lean` defines an internal construction target:
historical non-Monster carriers together with the actual raw Y443-derived
carrier. It does not construct classification or identify the historical
Monster with that carrier. The checked
`ExtendedCatalogueSolubleNormalizerGeneration.lean` derives its soluble
normalizer assembly from this internal target and the unchanged twelve-case
callback, using internally derived odd-order solvability and the already
proved literal binary-model certificates. Its five new modules have 24
standard-axiom audit exports. No public T1 assumption is discharged by this
conditional internal assembly.

`CFSGSerreLiteralSupportBaseChange.lean` and
`CFSGSerreQuadraticImageFaithfulness.lean` supply checked generic support and
perfect-source central-kernel tools for the remaining exceptional-family
comparisons. Literal integer zero entries survive base change without
field-eigenvalue separation in small characteristic. The three-module
prerequisite packet has six standard-axiom audit exports; the concrete E6
installer still needs its own checks.

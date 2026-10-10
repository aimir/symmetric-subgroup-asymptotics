import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29NormalCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop8GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop9GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop10GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop13GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop15GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop16GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop17GeneratedData

/-!
# Reuse of the twenty-four degree-eight pair tops

The count-sixteen paired branch uses the twenty-four transitive groups of
degree eight.  Twenty of these tops already occur in the degree-four
shared-top proof.  This file reuses their checked Cayley/normal-word data
directly and installs the actual natural eight-coordinate permutation
module.  The four tops excluded by the older local-quotient eligibility
condition are supplied semantically: the two solvable literal actions are
given by their pinned generators, and the final two are natural `A_8` and
`S_8`.

Thus `interface` is a concrete `Fin 24` family of complete pair-top
interfaces.  No normal or module census flag is assumed.  The remaining
row work is the profile/relative-character theorem on these interfaces.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

private noncomputable def generatedInterface
    (T : GeneratedTopData) : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    T.conjugacyCover T.ambient T.stateGenerators T.topRegistry.data
    T.literalAction T.actionModelEquiv.symm

noncomputable def top1 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow0TopCertificate.Source :=
    PrimitiveAffineEightFrameRow0TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow0NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow0NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow0NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow0NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators))
    PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv

noncomputable def top2 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow1TopCertificate.Source :=
    PrimitiveAffineEightFrameRow1TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow1NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow1NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow1NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow1NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators))
    PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv

noncomputable def top3 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow2TopCertificate.Source :=
    PrimitiveAffineEightFrameRow2TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow2NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow2NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow2NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow2NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow2TopCertificate.generators))
    PrimitiveAffineEightFrameRow2TopCertificate.originalEquiv

noncomputable def top4 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow3TopCertificate.Source :=
    PrimitiveAffineEightFrameRow3TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow3NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow3NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow3NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow3NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow3TopCertificate.generators))
    PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv

noncomputable def top5 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow4TopCertificate.Source :=
    PrimitiveAffineEightFrameRow4TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow4NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow4NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow4NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow4NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow4TopCertificate.generators))
    PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv

noncomputable def top6 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow8TopCertificate.Source :=
    PrimitiveAffineEightFrameRow8TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow8NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow8NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow8NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow8NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow8TopCertificate.generators))
    PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv

noncomputable def top7 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow9TopCertificate.Source :=
    PrimitiveAffineEightFrameRow9TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow9NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow9NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow9NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow9NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow9TopCertificate.generators))
    PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv

noncomputable def top8 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop8GeneratedData.topData

noncomputable def top9 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop9GeneratedData.topData

noncomputable def top10 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop10GeneratedData.topData

noncomputable def top11 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow20TopCertificate.Source :=
    PrimitiveAffineEightFrameRow20TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow20NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow20NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow20NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow20NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow20TopCertificate.generators))
    PrimitiveAffineEightFrameRow20TopCertificate.originalEquiv

noncomputable def top12 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow21TopCertificate.Source :=
    PrimitiveAffineEightFrameRow21TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow21NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow21NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow21NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow21NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow21TopCertificate.generators))
    PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv

noncomputable def top13 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop13GeneratedData.topData

noncomputable def top14 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow23TopCertificate.Source :=
    PrimitiveAffineEightFrameRow23TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow23NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow23NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow23NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow23NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow23TopCertificate.generators))
    PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv

noncomputable def top15 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop15GeneratedData.topData

noncomputable def top16 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop16GeneratedData.topData

noncomputable def top17 : DegreeTwoPairTopFiniteInterface 8 :=
  generatedInterface PrimitiveAffineEightFrameTop17GeneratedData.topData

private def top18Generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 6, 1, 7, 2, 4, 3, 5] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 4, 6, 5, 7, 1, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def sharedInvolution : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top18Generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![top18Generator0, sharedInvolution]

abbrev Top18 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top18Generators)

noncomputable def top18 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top18

noncomputable def top19 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow27TopCertificate.Source :=
    PrimitiveAffineEightFrameRow27TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow27NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow27NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow27NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow27NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow27TopCertificate.generators))
    PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv

private def top20Generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top20Generators : Fin 3 → Equiv.Perm (Fin 8) :=
  ![top18Generator0, top20Generator1, sharedInvolution]

abbrev Top20 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top20Generators)

noncomputable def top20 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top20

noncomputable def top21 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow28TopCertificate.Source :=
    PrimitiveAffineEightFrameRow28TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow28NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow28NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow28NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow28TopCertificate.generators))
    PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv

noncomputable def top22 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow29TopCertificate.Source :=
    PrimitiveAffineEightFrameRow29TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow29NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow29NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow29NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow29NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators))
    PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv

/-! The final two tops retain their small published generator tuples even
though their normal lattices are handled structurally.  This lets the
selected module and coupled-head emitters work on the generators without
enumerating either full permutation group. -/

private def top23Generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 0, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[6, 0, 1, 2, 3, 4, 5, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top23Generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 1, 2, 3, 4, 6, 7, 5] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 7, 5, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top23Generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![top23Generator0, top23Generator1]

abbrev Top23 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top23Generators)

/-- The retained row-23 tuple is the natural alternating top. -/
theorem top23_eq_alternating :
    Top23 = alternatingGroup (Fin 8) := by
  native_decide

private def top24Generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 0, 1, 2, 3, 4, 5, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top24Generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 0, 2, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[1, 0, 2, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top24Generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![top24Generator0, top24Generator1]

abbrev Top24 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top24Generators)

/-- The retained row-24 tuple is the full natural symmetric top. -/
theorem top24_eq_top :
    Top24 = (⊤ : Subgroup (Equiv.Perm (Fin 8))) := by
  native_decide

noncomputable def top23 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top23

noncomputable def top24 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top24

/-- The complete ordered family `paired8-1` through `paired8-24`. -/
noncomputable def interface : Fin 24 → DegreeTwoPairTopFiniteInterface 8 :=
  Fin.cases top1 <| Fin.cases top2 <| Fin.cases top3 <| Fin.cases top4 <|
  Fin.cases top5 <| Fin.cases top6 <| Fin.cases top7 <| Fin.cases top8 <|
  Fin.cases top9 <| Fin.cases top10 <| Fin.cases top11 <| Fin.cases top12 <|
  Fin.cases top13 <| Fin.cases top14 <| Fin.cases top15 <| Fin.cases top16 <|
  Fin.cases top17 <| Fin.cases top18 <| Fin.cases top19 <| Fin.cases top20 <|
  Fin.cases top21 <| Fin.cases top22 <| Fin.cases top23 <|
  Fin.cases top24 Fin.elim0

/-- Fill the paired-eight field of the count-sixteen catalogue with the
reused complete interfaces.  Only the three genuinely degree-sixteen
families remain to be supplied by the width-16 producer. -/
noncomputable def sixteenCatalogue
    (zero16 : Fin 29 → DegreeTwoPairTopFiniteInterface 16)
    (twoAffine16 : Fin 15 → DegreeTwoPairTopFiniteInterface 16)
    (primitive16 : Fin 20 → DegreeTwoPairTopFiniteInterface 16) :
    DegreeTwoSixteenPairTopFiniteCatalogue where
  paired8 := interface
  zero16 := zero16
  twoAffine16 := twoAffine16
  primitive16 := primitive16

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

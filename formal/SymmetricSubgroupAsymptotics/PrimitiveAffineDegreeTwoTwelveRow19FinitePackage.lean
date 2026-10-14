import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! The complete original-quotient row-19 package. Its actual translation
times four-cycle is a twelve-cycle, and its top is an explicit epi image
of the row-131 affine model. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow19FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def first : Row19Top :=
  ⟨row19Generators 0, Subgroup.subset_closure (Set.mem_range_self 0)⟩

def second : Row19Top :=
  ⟨row19Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩

def witness : LiteralCyclicOrbitWitness Row19Top 1 where
  element := first * second
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 7, 10, 5, 8, 3, 6, 1, 4, 11, 2, 9]
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row19Interface.top (Fin 12)) 1 :=
  witness.uniform _

def finiteData : DegreeTwoTwelveJointFiniteRowData row19Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles.row19TopSocle
  natural := natural

def resolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (18 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (18 : Fin 301)).finite
      (catalogue.row (18 : Fin 301)).expectedProfiles p := by
  let lift := finiteData.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow19FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

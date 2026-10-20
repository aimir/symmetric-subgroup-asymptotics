import SymmetricSubgroupAsymptotics.Row181OriginalQuotientSocles
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def naturalWitness : LiteralCyclicOrbitWitness Row181Top 2 where
  element := (closureGenerators row181Generators 1) * (closureGenerators row181Generators 2)
  representative := ![0,2]
  orbitIndex := ![0,0,1,0,0,1,0,0,0,1,1,0]
  exponent := ![0,3,0,7,6,1,2,5,4,3,2,1]
  point_eq := by decide +kernel

theorem natural_two : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row181Interface.top (Fin 12)) 2 :=
  naturalWitness.uniform _

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row181Interface 2 2 where
  topSocle := quotientFamily socle catalogue
  natural := natural_two

def flexibleData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row181Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (jointData socle catalogue) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel

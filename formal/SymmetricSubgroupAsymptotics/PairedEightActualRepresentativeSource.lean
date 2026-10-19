import SymmetricSubgroupAsymptotics.PairedEightActualKernelSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoResidualAssembly

/-! Endpoint adapters for the physical all-eight-pair source. These consume
no degree-sixteen action table or 527-entry locator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PairedEightActualRepresentativeSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def representativeSource
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoEightPairRepresentativeSource :=
  fun p => PairedEightActualKernelSource.source published hZmud lit p

def residualSource
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoEightPairResidualSource :=
  degreeTwoEightPairResidualSource_of_representative
    (representativeSource published hZmud lit)

end SymmetricSubgroupAsymptotics.PairedEightActualRepresentativeSource

import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveInstalledSocleExtraction
import SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveSocleOneProfile

/-! Filter already proved original-normal families by their capacity index.
The stored index is used only after extracting the actual family theorem;
no bound is inferred from catalogue metadata alone. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneSixPairSource
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def indices : Finset (Fin 301) :=
  DegreeTwoTwelveInstalledJoint.installedSocles.filter fun j => (catalogue.row j).kappa=1

/-- Every selected original top has an actual all-normal family at one. -/
def family (j : Fin 301) (hj : j ∈ indices) :
    (catalogue.row j).finite.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  DegreeTwoTwelveInstalledSocleExtraction.family_one j
    (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2

/-- Exact width12 source, transported along the recovered original group
isomorphism. No width24 counting conclusion enters this construction. -/
def source (hZmud : ZmudFaithfulCharacterTupleInput)
    (j : Fin 301) (hj : j ∈ indices) (p : PreE7PairActionClass 6)
    (e : (catalogue.row j).finite.top ≃* preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairSourceOfTwelveSocleOneProfile.source (catalogue.row j).finite (family j hj)
    p e (Classical.choice p.2) hZmud

end SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneSixPairSource

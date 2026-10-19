import SymmetricSubgroupAsymptotics.Row272OriginalElevenCycleNatural
import SymmetricSubgroupAsymptotics.CyclicPointStabilizerPrimitivity
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row272OriginalPrimitiveCertificate
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row272OriginalElevenCycleNatural
private theorem cycle_fixed : cycleElement • pointChart 11=pointChart 11 := by decide +kernel
private theorem cycle_cover : ∀ x : Fin 12,x≠pointChart 11 →
    ∃ j : Fin 11,cycleElement^j.val • pointChart 0=x := by decide +kernel
instance primitive : MulAction.IsPreprimitive Row272Top (Fin 12) := by
  apply primitive_of_cyclic_stabilizer_and_mover cycleElement
    (closureGenerators row272Generators 0) (pointChart 11) (pointChart 0) cycle_fixed
  · intro x hx
    obtain ⟨j,hj⟩ := cycle_cover x hx
    exact ⟨j.val,hj⟩
  · decide +kernel
end SymmetricSubgroupAsymptotics.Row272OriginalPrimitiveCertificate

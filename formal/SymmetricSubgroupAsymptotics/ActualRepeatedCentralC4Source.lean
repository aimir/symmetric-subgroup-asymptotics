import SymmetricSubgroupAsymptotics.ActualRepeatedAlternatingCentralC4Coordinates
import SymmetricSubgroupAsymptotics.ActualRepeatedSymmetricCentralC4Coordinates
import SymmetricSubgroupAsymptotics.BinaryPlaneLinearSymmetricEquiv
import SymmetricSubgroupAsymptotics.CyclicThreeRegularPermutation
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4ActualSource
import SymmetricSubgroupAsymptotics.MixedKernelRankTailPublishedSource

/-! Actual synchronized local actions provide complete source data.
The central coordinate witness is on the exact original kernel; no literal
family is identified by order, and no splitting or capacity is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualRepeatedCentralC4Source
open Non2UnipotentPrefixFiniteMenu
variable {U : PreE7NonPairActionClass 16} {c d : ℕ}
  (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)

def alternatingData
    (u : preE7NonPairAction 16 U →* (Fin d → NaturalA4ScalarFourHead.G)) (j₀ : Fin d)
    (hcommon : ∀ g j, NaturalA4ScalarFourHead.top (u g j)=NaturalA4ScalarFourHead.top (u g j₀))
    (htop : Function.Surjective (ActualRepeatedAlternatingCentralC4Coordinates.top u j₀))
    (hcentral : ∀ z : u.ker, ∀ g : preE7NonPairAction 16 U, (z : preE7NonPairAction 16 U)*g=g*(z : preE7NonPairAction 16 U))
    (z : u.ker →* (Fin c → Multiplicative (ZMod 4))) (hz : Function.Injective z)
    (hc : c≤3) (hd : d≤3) : MixedKernelRankTailResidual.Data 16 U :=
  ScalarFourCentralC4TopCoordinates.cubicActualSourceData hZmud lit
    (ActualRepeatedAlternatingCentralC4Coordinates.coordinates u j₀ hcommon htop hcentral z hz)
    hc hd rfl CyclicThreeRegularPermutation.representation
    CyclicThreeRegularPermutation.representation_injective

def symmetricData
    (u : preE7NonPairAction 16 U →* (Fin d → Equiv.Perm BinaryPlanePermutationAffineEquiv.Plane)) (j₀ : Fin d)
    (hcommon : ∀ g j, BinaryPlanePermutationAffineEquiv.linearPart (u g j)=BinaryPlanePermutationAffineEquiv.linearPart (u g j₀))
    (htop : Function.Surjective (ActualRepeatedSymmetricCentralC4Coordinates.top u j₀))
    (hcentral : ∀ z : u.ker, ∀ g : preE7NonPairAction 16 U, (z : preE7NonPairAction 16 U)*g=g*(z : preE7NonPairAction 16 U))
    (z : u.ker →* (Fin c → Multiplicative (ZMod 4))) (hz : Function.Injective z)
    (hc : c≤3) (hd : d≤3) : MixedKernelRankTailResidual.Data 16 U :=
  ScalarFourCentralC4TopCoordinates.symmetricActualSourceData hZmud lit
    (ActualRepeatedSymmetricCentralC4Coordinates.coordinates u j₀ hcommon htop hcentral z hz)
    BinaryPlaneLinearSymmetricEquiv.equivalence hc hd
    BinaryPlaneLinearSymmetricEquiv.cubic_order_three

end SymmetricSubgroupAsymptotics.ActualRepeatedCentralC4Source

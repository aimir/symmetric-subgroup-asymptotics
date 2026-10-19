import SymmetricSubgroupAsymptotics.ActualRepeatedSymmetricCentralCoordinates
import SymmetricSubgroupAsymptotics.BinaryPlaneLinearSymmetricEquiv
import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricActualSource
import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricActualSourceTwo

/-! Actual synchronized local permutation coordinates yield complete sources.
The exact central kernel is an input structural witness, rather than a
numerical quotient capacity or a list of normal subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualRepeatedSymmetricCentralCoordinates
open BinaryPlanePermutationAffineEquiv
open Non2UnipotentPrefixFiniteMenu

variable {w : ℕ} {U : PreE7NonPairActionClass w} {c d : ℕ}
  (u : preE7NonPairAction w U →* (Fin d → Equiv.Perm Plane)) (j₀ : Fin d)
  (hcommon : ∀ g j, linearPart (u g j)=linearPart (u g j₀))
  (htop : Function.Surjective (top u j₀))
  (hcentral : ∀ z : u.ker, ∀ g : preE7NonPairAction w U, (z : preE7NonPairAction w U)*g=g*(z : preE7NonPairAction w U))
  (z : u.ker →* (Fin c → Multiplicative (ZMod 2))) (hz : Function.Injective z)
  (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)

def actualSourceSixteen {U : PreE7NonPairActionClass 16}
    (u : preE7NonPairAction 16 U →* (Fin d → Equiv.Perm Plane)) (j₀ : Fin d)
    (hcommon : ∀ g j, linearPart (u g j)=linearPart (u g j₀))
    (htop : Function.Surjective (top u j₀))
    (hcentral : ∀ z : u.ker, ∀ g : preE7NonPairAction 16 U, (z : preE7NonPairAction 16 U)*g=g*(z : preE7NonPairAction 16 U))
    (z : u.ker →* (Fin c → Multiplicative (ZMod 2))) (hz : Function.Injective z)
    (hc : c≤3) (hd : d≤3) : PreE7RankTailSourceOrYonedaTopData 16 U :=
  (coordinates u j₀ hcommon htop hcentral z hz).symmetricActualSource
    BinaryPlaneLinearSymmetricEquiv.equivalence hc hd
    BinaryPlaneLinearSymmetricEquiv.cubic_order_three hZmud lit

def actualSourceTwelve {U : PreE7NonPairActionClass 12}
    (u : preE7NonPairAction 12 U →* (Fin d → Equiv.Perm Plane)) (j₀ : Fin d)
    (hcommon : ∀ g j, linearPart (u g j)=linearPart (u g j₀))
    (htop : Function.Surjective (top u j₀))
    (hcentral : ∀ z : u.ker, ∀ g : preE7NonPairAction 12 U, (z : preE7NonPairAction 12 U)*g=g*(z : preE7NonPairAction 12 U))
    (z : u.ker →* (Fin c → Multiplicative (ZMod 2))) (hz : Function.Injective z)
    (hc : c≤2) (hd : d≤2) : PreE7RankTailSourceOrYonedaTopData 12 U :=
  (coordinates u j₀ hcommon htop hcentral z hz).symmetricActualSourceTwo
    BinaryPlaneLinearSymmetricEquiv.equivalence hc hd
    BinaryPlaneLinearSymmetricEquiv.cubic_order_three hZmud lit

end SymmetricSubgroupAsymptotics.ActualRepeatedSymmetricCentralCoordinates

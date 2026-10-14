import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopLiteralTowerState
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTowerCyclicPrefix
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalOriginalQuotients

/-!
# Original-quotient consumer for the two paired-six alternatives

A literal twelve-to-six pair map and a cyclic natural-module theorem
supply the three relative positions on every original quotient. The
remaining finite top theorem says that each last-top quotient has either
a normally cyclic socle or a faithful map to the binary plane. The first
top's existing normal state selects exactly these two allowed profiles.

This is a shared consumer. Its top-quotient hypothesis remains explicit;
this module does not claim that either literal paired-six top satisfies it.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairedSixCyclicAssembly

open DegreeTwoTwelveExceptionalTypewise DegreeTwoTwelveExceptionalOriginalQuotients
open DegreeTwoPairTowerCyclicPrefix

private theorem quotientSocle_iff_of_eq
    {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (h : M = N) :
    SocleNormalGeneratorBound (G ⧸ M) 1 ↔ SocleNormalGeneratorBound (G ⧸ N) 1 := by
  subst N
  rfl

variable {D : DegreeTwoPairTopFiniteInterface 12}
  {L : DegreeTwoPairTopFiniteInterface 6}
  (C : DegreeTwoPairTopLiteralTower D L)

/-- The same first-top normal state controls the last-top quotient and
therefore the prefix. The module state has no extra branch condition. -/
def kindOfState (i : D.normalRegistry.State) (_ : D.ModuleState) : ProfileKind :=
  if SocleNormalGeneratorBound
      (L.top ⧸ C.normalImage (D.normalRegistry.state i)) 1 then
    .ordinaryThree else .twoBinaryThree

/-- Close the original-quotient interface once the two genuine finite
last-top quotient alternatives have been proved. The only character
theorem used is the stated published Zmud input. -/
def certificate
    (uniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) L.top (Fin 6)) 1)
    (alternatives : ∀ N : {N : Subgroup L.top // N.Normal},
      TopAlternative (L.top ⧸ N.1)) : RowCertificate D where
  kindOfState := kindOfState C
  anchor hZmud _p R N := by
    let T := C.realization R
    have hstate : C.normalImage (D.normalRegistry.state (R.topNormalState N)) =
        T.topNormal N.1 := C.normalImage_topNormalState R N
    change DegreeTwoPairRelativeKernelAnchor _
      ((if SocleNormalGeneratorBound
        (L.top ⧸ C.normalImage (D.normalRegistry.state (R.topNormalState N))) 1
        then ProfileKind.ordinaryThree else ProfileKind.twoBinaryThree).profile)
    split_ifs with h
    · have htop : SocleNormalGeneratorBound (L.top ⧸ T.topNormal N.1) 1 := by
        exact (quotientSocle_iff_of_eq _ _ hstate).mp h
      exact (ordinary uniform T hZmud N htop).anchor
    · have htop : ¬ SocleNormalGeneratorBound (L.top ⧸ T.topNormal N.1) 1 := by
        exact fun hs ↦ h ((quotientSocle_iff_of_eq _ _ hstate).mpr hs)
      have hbinary : ∃ f : (L.top ⧸ T.topNormal N.1) →*
          DegreeTwoPairTowerCyclicPrefix.BinaryPlane,
          Function.Injective f :=
        (alternatives ⟨T.topNormal N.1, T.topNormal_normal N.1⟩).resolve_left htop
      exact (twoBinary uniform T N (Classical.choose hbinary)
        (Classical.choose_spec hbinary)).anchor

end DegreeTwoTwelvePairedSixCyclicAssembly
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

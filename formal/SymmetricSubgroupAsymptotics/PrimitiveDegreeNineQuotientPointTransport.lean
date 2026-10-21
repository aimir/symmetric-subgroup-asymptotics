import SymmetricSubgroupAsymptotics.PrimitiveSoclePointTransport
import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineQuotientOrderEight

/-! The degree-nine quotient bound on the original finite point type,
needed for actual minimal-block fibres. Only the point coordinates change. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem NonaffineData.degreeNine_quotient_card_le_eight_of_card
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hX : Nat.card X = 9)
    (hindex : PublishedSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 8 := by
  let e : X ≃ Fin 9 := Finite.equivFinOfCardEq hX
  letI : MulAction G (Fin 9) := MulAction.compHom (Fin 9) (labelledActionHom e)
  letI : FaithfulSMul G (Fin 9) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      labelledActionHom_injective e (Equiv.Perm.ext hab) }
  let D' : NonaffineData G (Fin 9) := D.transportPoints e
    (fun g x => (labelledActionHom_apply e g x).symm)
  exact D'.degreeNine_quotient_card_le_eight hindex

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

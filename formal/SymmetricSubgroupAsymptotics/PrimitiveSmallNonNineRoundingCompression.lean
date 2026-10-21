import SymmetricSubgroupAsymptotics.PrimitiveDegreeEightRoundingQuotient
import SymmetricSubgroupAsymptotics.PrimitiveDegreeFiveSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenElevenRoundingCompression
import SymmetricSubgroupAsymptotics.PrimitiveSoclePointTransport

/-! All small primitive nonaffine local degrees except9 admit the exact
rounding-gap comparator. Only the retained actual8-point classification
is used; the degree9 source and many-block comparator are separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

private theorem five_bound (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hX : Nat.card X=5) : Nat.card (G⧸finiteGroupSocle G)≤2 := by
  let e : X≃Fin 5 := Finite.equivFinOfCardEq hX
  letI : MulAction G (Fin 5) := MulAction.compHom (Fin 5) (labelledActionHom e)
  letI : FaithfulSMul G (Fin 5) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      labelledActionHom_injective e (Equiv.Perm.ext hab) }
  let D' : NonaffineData G (Fin 5) := D.transportPoints e
    (fun g x => (labelledActionHom_apply e g x).symm)
  exact D'.degreeFive_quotient_card_le_two hindex

private theorem six_bound (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hX : Nat.card X=6) : Nat.card (G⧸finiteGroupSocle G)≤2 := by
  let e : X≃Fin 6 := Finite.equivFinOfCardEq hX
  letI : MulAction G (Fin 6) := MulAction.compHom (Fin 6) (labelledActionHom e)
  letI : FaithfulSMul G (Fin 6) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      labelledActionHom_injective e (Equiv.Perm.ext hab) }
  let D' : NonaffineData G (Fin 6) := D.transportPoints e
    (fun g x => (labelledActionHom_apply e g x).symm)
  exact PrimitiveDegreeSixActualNormalConsumers.nonaffine_socle_quotient_card_le_two D' hindex

private def regularCompression (D : NonaffineData G X)
    (hr : Nat.card X≤1024)
    (hgap : max 2 (Nat.card (G⧸finiteGroupSocle G))+1≤evenWidth (Nat.card X)) :
    LocalSemisimpleRoundingCompressionData G (Nat.card X) where
  E := finiteGroupSocle G
  chart := D.chart
  quotientDegree := Nat.card (G⧸finiteGroupSocle G)
  quotientDegree_pos := Nat.card_pos
  quotientAction := regularAction _
  quotientAction_injective := regularAction_injective _
  degree_bound := hr
  quotientDegree_gap := hgap

def NonaffineData.smallNonNineRoundingCompression
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hf : 5≤Nat.card X) (h30 : Nat.card X<30) (hnine : Nat.card X≠9) :
    LocalSemisimpleRoundingCompressionData G (Nat.card X) := by
  by_cases h5 : Nat.card X=5
  · apply regularCompression D (by omega)
    have hq := five_bound D hindex h5
    rw [max_eq_left hq,h5]
    decide
  by_cases h6 : Nat.card X=6
  · apply regularCompression D (by omega)
    have hq := six_bound D hindex h6
    rw [max_eq_left hq,h6]
    decide
  by_cases h7 : Nat.card X=7
  · let e : X≃Fin 7 := Finite.equivFinOfCardEq h7
    letI : MulAction G (Fin 7) := MulAction.compHom (Fin 7) (labelledActionHom e)
    letI : FaithfulSMul G (Fin 7) := {
      eq_of_smul_eq_smul := fun {a b} hab =>
        labelledActionHom_injective e (Equiv.Perm.ext hab) }
    let D' : NonaffineData G (Fin 7) := D.transportPoints e
      (fun g x => (labelledActionHom_apply e g x).symm)
    simpa only [h7] using D'.degreeSeven_roundingCompression
  by_cases h8 : Nat.card X=8
  · apply regularCompression D (by omega)
    have hq := D.degreeEight_quotient_card_le_seven hindex published8 h8
    rw [h8,show evenWidth 8=8 by decide]
    omega
  by_cases h10 : Nat.card X=10
  · apply regularCompression D (by omega)
    have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by omega)
    obtain ⟨ell,_,he5,hell,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
    have hpow : 2^Nat.card (G⧸finiteGroupSocle G)≤1000 :=
      (quotientOrder_twoPow_le_cube_of_log (by omega) hlog).trans
        (by simpa using Nat.pow_le_pow_left (by omega : ell≤10) 3)
    have hq : Nat.card (G⧸finiteGroupSocle G)≤9 := by
      by_contra h
      have hh : 1024≤1000 := calc
        1024=2^10 := by decide
        _ ≤ 2^Nat.card (G⧸finiteGroupSocle G) :=
          pow_le_pow_right₀ (by decide : 1≤(2 : ℕ)) (by omega)
        _ ≤ 1000 := hpow
      omega
    rw [h10,show evenWidth 10=10 by decide]
    omega
  by_cases h11 : Nat.card X=11
  · let e : X≃Fin 11 := Finite.equivFinOfCardEq h11
    letI : MulAction G (Fin 11) := MulAction.compHom (Fin 11) (labelledActionHom e)
    let D' : NonaffineData G (Fin 11) := D.transportPoints e
      (fun g x => (labelledActionHom_apply e g x).symm)
    simpa only [h11] using D'.degreeEleven_roundingCompression hindex
  exact D.roundingCompression_twelveToFortyFour hindex (by omega) (by omega)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

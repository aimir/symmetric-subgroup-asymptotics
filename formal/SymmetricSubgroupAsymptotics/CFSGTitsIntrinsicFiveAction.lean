import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleRadical

/-! The checked order-five middle element acts on the ACTUAL intrinsic
normal 2-layer. This is an internal conjugation action; faithfulness is
proved separately with the selected original commutator witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFiveAction
open CFSGTitsIntrinsicMiddleRadical CFSGTitsMiddleWeylRecovery
open CFSGTitsIntrinsicMiddleSquare CFSGTitsAmbientPairAlignment
open CFSGReeFFourBinarySylowNormalizerSolvable CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourFixedDerivedInversionFacts CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourFixedModelEquivalence

private theorem radical_le_carrier : middleRadical≤middleCarrier :=
  inf_le_left.trans le_sup_left
private instance radicalNormal : (middleRadical.subgroupOf middleCarrier).Normal :=
  middleRadical_normal_in_carrier
private def radicalEquiv : middleRadical.subgroupOf middleCarrier≃*middleRadical :=
  Subgroup.subgroupOfEquivOfLe radical_le_carrier

def fiveElement : CFSG.Models.Tits := middleWeylRoot*middleSquareRoot

theorem fiveElement_order : orderOf fiveElement=5 := middleWeyl_square_product_order

private theorem middleSquare_mem_positive :
    middleSquareRoot∈(titsPositiveSylow : Subgroup CFSG.Models.Tits) := by
  rw [titsPositiveSylow_coe,middleSquareRoot_value]
  exact ⟨⟨(fourCycle 0)^2,square_mem_derived 0⟩,
    (middle_square_positive_derived 0).1,rfl⟩

theorem fiveElement_mem_carrier : fiveElement∈middleCarrier :=
  middleCarrier.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers middleWeylRoot))
    (Subgroup.mem_sup_left middleSquare_mem_positive)

theorem pairStabilizer_fixes_fiveElement (f : pairStabilizer) :
    f.val fiveElement=fiveElement := by
  change f.val (middleWeylRoot*middleSquareRoot)=middleWeylRoot*middleSquareRoot
  rw [map_mul,pairStabilizer_fixes_middleWeylRoot,pairStabilizer_fixes_middleSquareRoot]

def carrierConjugation : middleCarrier →* MulAut middleRadical :=
  (MulAut.congr radicalEquiv).toMonoidHom.comp
    (MulAut.conjNormal : middleCarrier →* MulAut (middleRadical.subgroupOf middleCarrier))

theorem carrierConjugation_val (g : middleCarrier) (x : middleRadical) :
    (carrierConjugation g x : CFSG.Models.Tits)=g.val*x.val*g.val⁻¹ := rfl

private def fiveInCarrier : middleCarrier := ⟨fiveElement,fiveElement_mem_carrier⟩

def fiveAction : MulAut middleRadical := carrierConjugation fiveInCarrier

theorem fiveAction_val (x : middleRadical) :
    (fiveAction x : CFSG.Models.Tits)=fiveElement*x.val*fiveElement⁻¹ :=
  carrierConjugation_val fiveInCarrier x

theorem fiveAction_pow_five : fiveAction^5=1 := by
  have hp : fiveElement^5=1 := by
    rw [←fiveElement_order]
    exact pow_orderOf_eq_one fiveElement
  have hc : fiveInCarrier^5=1 := Subtype.ext hp
  exact (map_pow carrierConjugation fiveInCarrier 5).symm.trans
    ((congrArg carrierConjugation hc).trans (map_one carrierConjugation))

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFiveAction

import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointAction
import SymmetricSubgroupAsymptotics.ScalarPlaneAxisHom

/-! Literal endpoint-axis sections determine the actual short-Weyl
action. Additivity suffices; no full-field linearity of arbitrary source
elements is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointWeyl
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
open CFSGGTwoCharacteristicThreeMiddleNormalizers
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleSourceInvolution
open CFSGGTwoCharacteristicThreeMiddleEndpointAction
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoOriginalSimpleWeylTransport
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def firstAxis (a : K) : Middle K := word K ![a,0,0,0,0]
def secondAxis (a : K) : Middle K := word K ![0,0,0,a,0]

theorem firstAxis_val (a : K) : (firstAxis K a).val = positiveModel K 1 a := by
  change middleWord K ![a,0,0,0,0] = _
  rw [middleWord_factors]
  change positiveModel K 1 a*positiveModel K 2 0*positiveModel K 3 0*
    positiveModel K 4 0*positiveModel K 5 0 = positiveModel K 1 a
  simp only [positiveModel_zero,mul_one]

theorem secondAxis_val (a : K) : (secondAxis K a).val = positiveModel K 4 a := by
  change middleWord K ![0,0,0,a,0] = _
  rw [middleWord_factors]
  change positiveModel K 1 0*positiveModel K 2 0*positiveModel K 3 0*
    positiveModel K 4 a*positiveModel K 5 0 = positiveModel K 4 a
  simp only [positiveModel_zero,one_mul,mul_one]

omit [Finite K] in
theorem firstAxis_endpoint (a : K) :
    endpointHom K (firstAxis K a) = Multiplicative.ofAdd ![a,0] :=
  endpointHom_word K _

omit [Finite K] in
theorem secondAxis_endpoint (a : K) :
    endpointHom K (secondAxis K a) = Multiplicative.ofAdd ![0,a] :=
  endpointHom_word K _

def sourceWeyl : source K := ⟨shortWord K,shortWeyl_mem_source K⟩

theorem sourceWeyl_firstAxis (a : K) :
    sourceAction K (sourceWeyl K) (Multiplicative.ofAdd ![a,0]) =
      Multiplicative.ofAdd ![0,a] := by
  have hc : (Middle K).normalizerMonoidHom (toNormalizer K (sourceWeyl K))
      (firstAxis K a) = secondAxis K a := by
    apply Subtype.ext
    change shortWord K*(firstAxis K a).val*(shortWord K)⁻¹ = (secondAxis K a).val
    rw [firstAxis_val,secondAxis_val]
    exact short_one K a
  change endpointAction K (toNormalizer K (sourceWeyl K)) _ = _
  rw [←firstAxis_endpoint K a,endpointAction_apply,hc,secondAxis_endpoint]

theorem sourceWeyl_secondAxis (a : K) :
    sourceAction K (sourceWeyl K) (Multiplicative.ofAdd ![0,a]) =
      Multiplicative.ofAdd ![-a,0] := by
  have hc : (Middle K).normalizerMonoidHom (toNormalizer K (sourceWeyl K))
      (secondAxis K a) = firstAxis K (-a) := by
    apply Subtype.ext
    change shortWord K*(secondAxis K a).val*(shortWord K)⁻¹ = (firstAxis K (-a)).val
    rw [firstAxis_val,secondAxis_val]
    exact short_four K a
  change endpointAction K (toNormalizer K (sourceWeyl K)) _ = _
  rw [←secondAxis_endpoint K a,endpointAction_apply,hc,firstAxis_endpoint]

theorem sourceWeyl_endpoint (v : Fin 2 → K) :
    sourceAction K (sourceWeyl K) (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ![-v 1,v 0] := by
  have h := ScalarPlaneAxisHom.apply_of_axis_values
    (sourceAction K (sourceWeyl K)).toMonoidHom (-1 : K) 1
    (by intro a; simpa only [one_mul] using sourceWeyl_firstAxis K a)
    (by intro a; simpa only [neg_one_mul] using sourceWeyl_secondAxis K a) v
  simpa only [neg_one_mul,one_mul] using h

theorem involution_endpoint (v : Fin 2 → K) :
    sourceAction K (involution K) (Multiplicative.ofAdd v) = Multiplicative.ofAdd (-v) := by
  have ht : involution K = sourceWeyl K*sourceWeyl K := by
    apply Subtype.ext
    exact torusPair_eq_short_square K
  rw [ht,map_mul]
  change sourceAction K (sourceWeyl K)
    (sourceAction K (sourceWeyl K) (Multiplicative.ofAdd v)) = _
  rw [sourceWeyl_endpoint,sourceWeyl_endpoint]
  apply congrArg Multiplicative.ofAdd
  funext i
  fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointWeyl

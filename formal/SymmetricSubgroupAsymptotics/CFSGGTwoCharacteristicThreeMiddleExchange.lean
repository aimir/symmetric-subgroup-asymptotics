import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerCounts
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherRootCovariance

/-! The second actual source is the image under the checked exceptional
automorphism of the SAME original Model. It centralizes the exchanged
short central parameter pointwise. No automorphism is lifted from a
projective quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleExchange
open CFSG.Models.Chevalley
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoOriginalExceptionalModel CFSGGTwoOriginalHigherRootCovariance
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleLayerCounts
open CFSGGTwoCharacteristicThreeMiddleCommutator
open CFSGGTwoPositiveSixWord CFSGGTwoPositiveWordSubgroup
open CFSGGTwoPositiveCoordinateKernels
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def exchangedSource : Subgroup (Model CartanMatrix.G₂ K) :=
  (source K).map (exceptionalModelEquiv K).toMonoidHom

def sourceEquivExchanged : source K ≃* exchangedSource K :=
  (exceptionalModelEquiv K).subgroupMap (source K)

theorem exceptional_highest (a : K) :
    exceptionalModelEquiv K (positiveModel K 5 a) = positiveModel K 3 a := by
  rw [exceptional_positiveModel]
  rfl

theorem highestElement_val : (highestElement K).val = positiveModel K 5 1 :=
  highHom_val K (Multiplicative.ofAdd (1 : K))

theorem positive_one_ne_one (j : Fin 6) : positiveModel K j 1 ≠ 1 := by
  intro he
  have hw : modelWord K (Pi.single j (1 : K)) = modelWord K (Pi.single j (0 : K)) := by
    rw [modelWord_single,modelWord_single,positiveModel_zero,he]
  have hc := congrFun (modelWord_injective K hw) j
  simp only [Pi.single_eq_same] at hc
  exact one_ne_zero hc

theorem exchangedSource_centralizes_third (a : K) : exchangedSource K ≤
    Subgroup.centralizer ({positiveModel K 3 a} : Set (Model CartanMatrix.G₂ K)) := by
  rintro x ⟨g,hg,rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (source_centralizes_high K a hg)
  have he := congrArg (exceptionalModelEquiv K) hc
  simpa only [map_mul,exceptional_highest] using he

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleExchange

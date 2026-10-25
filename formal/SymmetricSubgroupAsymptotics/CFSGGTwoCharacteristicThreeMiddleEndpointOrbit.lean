import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointWeyl
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleShortAxisConjugation
import SymmetricSubgroupAsymptotics.ScalarPlaneShearSwapOrbit
import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex
import Mathlib.Algebra.CharP.Reduced

/-! Every lower shear is realized by an actual original short root.
Together with the actual Weyl swap this gives the entire nonzero endpoint
orbit, including over the field of three elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointOrbit
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
open CFSGGTwoCharacteristicThreeMiddleEndpointAction
open CFSGGTwoCharacteristicThreeMiddleEndpointWeyl
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleShortAxisConjugation
open CFSGGTwoOriginalPositiveRootWords
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

def sourceShort (a : K) : source K := ⟨positiveModel K 0 a,positive_short_mem_source K a⟩

theorem sourceShort_firstAxis (a b : K) :
    sourceAction K (sourceShort K a) (Multiplicative.ofAdd ![b,0]) =
      Multiplicative.ofAdd ![b,a^3*b] := by
  have hc : (Middle K).normalizerMonoidHom (toNormalizer K (sourceShort K a))
      (firstAxis K b) = word K ![b,a*b,-a^2*b,a^3*b,-a^3*b^2] := by
    apply Subtype.ext
    change positiveModel K 0 a*(firstAxis K b).val*(positiveModel K 0 a)⁻¹ = _
    rw [firstAxis_val]
    exact short_conjugate_first K a b
  change endpointAction K (toNormalizer K (sourceShort K a)) _ = _
  rw [←firstAxis_endpoint K b,endpointAction_apply,hc,endpointHom_word]
  rfl

theorem sourceShort_secondAxis (a b : K) :
    sourceAction K (sourceShort K a) (Multiplicative.ofAdd ![0,b]) =
      Multiplicative.ofAdd ![0,b] := by
  have hc : (Middle K).normalizerMonoidHom (toNormalizer K (sourceShort K a))
      (secondAxis K b) = secondAxis K b := by
    apply Subtype.ext
    change positiveModel K 0 a*(secondAxis K b).val*(positiveModel K 0 a)⁻¹ = _
    rw [secondAxis_val]
    exact short_conjugate_second K a b
  change endpointAction K (toNormalizer K (sourceShort K a)) _ = _
  rw [←secondAxis_endpoint K b,endpointAction_apply,hc,secondAxis_endpoint]

theorem sourceShort_endpoint (a : K) (v : Fin 2 → K) :
    sourceAction K (sourceShort K a) (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ![v 0,a^3*v 0+v 1] := by
  have hv : Multiplicative.ofAdd v =
      Multiplicative.ofAdd ![v 0,0]*Multiplicative.ofAdd ![0,v 1] := by
    change Multiplicative.ofAdd v = Multiplicative.ofAdd (![v 0,0]+![0,v 1])
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  rw [hv,map_mul,sourceShort_firstAxis,sourceShort_secondAxis]
  change Multiplicative.ofAdd (![v 0,a^3*v 0]+![0,v 1]) = _
  apply congrArg Multiplicative.ofAdd
  funext i
  fin_cases i
  · exact add_zero _
  · rfl

theorem source_lower_shears (c : K) : ∃ g : source K, ∀ v : Fin 2 → K,
    sourceAction K g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0,c*v 0+v 1] := by
  have hf : Function.Surjective (frobenius K 3) :=
    Finite.surjective_of_injective (frobenius_inj K 3)
  obtain ⟨a,ha⟩ := hf c
  change a^3 = c at ha
  refine ⟨sourceShort K a,?_⟩
  intro v
  rw [sourceShort_endpoint,ha]

theorem source_endpoint_transitive (v w : Fin 2 → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : source K, sourceAction K g (Multiplicative.ofAdd v) = Multiplicative.ofAdd w := by
  apply ScalarPlaneShearSwapOrbit.transitive (sourceAction K)
    (source_lower_shears K) (sourceWeyl K) (-1 : K) 1
    (neg_ne_zero.mpr one_ne_zero) one_ne_zero
    (fun z => by simpa only [neg_one_mul,one_mul] using sourceWeyl_endpoint K z) v w hv hw

theorem source_endpoint_orbit_card (v : Fin 2 → K) (hv : v ≠ 0) :
    Nat.card (CentralExtensionLayerOrbitIndex.layerOrbit (sourceAction K) (Multiplicative.ofAdd v)) =
      Nat.card K^2-1 := by
  have hv1 : Multiplicative.ofAdd v ≠ (1 : Multiplicative (Fin 2 → K)) := hv
  have hs : CentralExtensionLayerOrbitIndex.layerOrbit (sourceAction K) (Multiplicative.ofAdd v) =
      {w : Multiplicative (Fin 2 → K) | w ≠ 1} := by
    ext w
    constructor
    · rintro ⟨g,rfl⟩ hw
      apply hv1
      apply (sourceAction K g).injective
      exact hw.trans (map_one (sourceAction K g)).symm
    · intro hw
      exact source_endpoint_transitive K v w.toAdd hv hw
  rw [hs]
  change Nat.card {w : Multiplicative (Fin 2 → K) // w ≠ 1} = Nat.card K^2-1
  rw [CentralExtensionLayerOrbitIndex.nonone_card]
  change Nat.card (Fin 2 → K)-1 = Nat.card K^2-1
  rw [Nat.card_fun,Nat.card_fin]

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointOrbit

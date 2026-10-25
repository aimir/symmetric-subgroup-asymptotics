import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralJoin
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCapacity
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointAction
import SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex

/-! Exact capacities of the full centre and endpoint image of ONE
literal source subgroup. The normal radical, central preimage and join
are all retained, without assuming a split extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerCounts
open CFSG.Models.Chevalley CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleCommutator
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleSourceRadical
open CFSGGTwoCharacteristicThreeMiddleCentralJoin
open CFSGGTwoCharacteristicThreeMiddleCapacity
open CFSGGTwoCharacteristicThreeMiddleEndpointAction
variable (K : Type) [Field K] [Finite K] [CharP K 3]

theorem source_finite : Finite (source K) := by
  letI : Finite (Model CartanMatrix.G₂ K) := Finite.of_injective (modelEquivNatural K)
    (modelEquivNatural K).injective
  infer_instance

local instance : Finite (source K) := source_finite K

def centralEmbedding : Multiplicative (Fin 3 → K) →* radical K :=
  (radicalEquiv K).symm.toMonoidHom.comp (centralHom K)

theorem centralEmbedding_injective : Function.Injective (centralEmbedding K) :=
  (radicalEquiv K).symm.injective.comp (centralHom_injective K)

theorem centralEmbedding_to_source (a : Multiplicative (Fin 3 → K)) :
    (centralEmbedding K a).val = sourceCentralHom K a := rfl

theorem centralEmbedding_range : (centralEmbedding K).range = (projection K).ker := by
  ext u
  constructor
  · rintro ⟨z,rfl⟩
    change endpointHom K (radicalEquiv K ((radicalEquiv K).symm (centralHom K z))) = 1
    rw [MulEquiv.apply_symm_apply]
    exact (centralHom_range K).le ⟨z,rfl⟩
  · intro hu
    have hh : radicalEquiv K u ∈ (centralHom K).range := by
      rw [centralHom_range]
      exact hu
    obtain ⟨z,hz⟩ := hh
    exact ⟨z,(congrArg (radicalEquiv K).symm hz).trans ((radicalEquiv K).symm_apply_apply u)⟩

def highestElement : source K := middleEmbedding K (highHom K (Multiplicative.ofAdd (1 : K)))

def centralLayer (M : Subgroup (source K)) : Subgroup (Multiplicative (Fin 3 → K)) :=
  M.comap (sourceCentralHom K)

def vectorLayer (M : Subgroup (source K)) : Subgroup (Multiplicative (Fin 2 → K)) :=
  (M.comap (radical K).subtype).map (projection K)

theorem central_capacity (M : Subgroup (source K)) (hM : highestElement K ∉ M) :
    3*Nat.card (centralLayer K M) ≤ Nat.card K^3 := by
  let A := M.comap (middleEmbedding K)
  have hA : highHom K (Multiplicative.ofAdd (1 : K)) ∉ A := hM
  exact central_preimage_card_mul_three_le K A hA

theorem vector_capacity (M : Subgroup (source K)) (hM : highestElement K ∉ M) :
    Nat.card (vectorLayer K M) ≤ Nat.card K := by
  let J := M.comap (radical K).subtype
  let A := M.comap (middleEmbedding K)
  have hA : highHom K (Multiplicative.ofAdd (1 : K)) ∉ A := hM
  have he : vectorLayer K M = A.map (endpointHom K) := by
    change J.map ((endpointHom K).comp (radicalEquiv K).toMonoidHom) =
      (J.comap (radicalEquiv K).symm.toMonoidHom).map (endpointHom K)
    rw [←Subgroup.map_map,Subgroup.map_equiv_eq_comap_symm' (radicalEquiv K) J]
  rw [he]
  exact vector_image_card_le K A hA

theorem index_mul_layer_cards (M : Subgroup (source K)) :
    M.index*Nat.card (centralLayer K M)*Nat.card (vectorLayer K M) =
      Nat.card K^3*Nat.card K^2*(M ⊔ radical K).index := by
  letI := radical_normal K
  have he := ActualNormalLayerOrbitIndex.index_mul_layer_cards (radical K) M
    (projection K) (projection_surjective K) (centralEmbedding K) (centralEmbedding_range K)
  have hc : (M.comap (radical K).subtype).comap (centralEmbedding K) = centralLayer K M := by
    ext z
    rfl
  have hZ : Nat.card (Multiplicative (Fin 3 → K)) = Nat.card K^3 := by
    change Nat.card (Fin 3 → K) = _
    rw [Nat.card_fun,Nat.card_fin]
  have hV : Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K^2 := by
    change Nat.card (Fin 2 → K) = _
    rw [Nat.card_fun,Nat.card_fin]
  rw [hc,hZ,hV] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerCounts

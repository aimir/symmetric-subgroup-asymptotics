import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerCounts
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointOrbit
import SymmetricSubgroupAsymptotics.AutomorphismSubgroupInversionJoin

/-! The actual nonzero endpoint orbit is paid by the SAME preserving join.
Adjoining the actual central-modulo-radical involution preserves that same
endpoint image because its proved action is inversion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerOrbit
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleSourceRadical
open CFSGGTwoCharacteristicThreeMiddleSourceInvolution
open CFSGGTwoCharacteristicThreeMiddleEndpointAction
open CFSGGTwoCharacteristicThreeMiddleEndpointWeyl
open CFSGGTwoCharacteristicThreeMiddleEndpointOrbit
open CFSGGTwoCharacteristicThreeMiddleLayerCounts
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : Finite (source K) := source_finite K
local instance : (radical K).Normal := radical_normal K

theorem vector_invariant_join (M : Subgroup (source K)) :
    ∀ g ∈ M ⊔ radical K, ∀ v ∈ vectorLayer K M,
      sourceAction K g v ∈ vectorLayer K M :=
  ActualNormalLayerOrbitIndex.quotient_layer_invariant (radical K) M
    (projection K) (projection_surjective K) (sourceAction K) (sourceAction_apply K)

theorem vector_invariant_enlarged_join (M : Subgroup (source K)) :
    ∀ g ∈ (M ⊔ radical K) ⊔ Subgroup.zpowers (involution K), ∀ v ∈ vectorLayer K M,
      sourceAction K g v ∈ vectorLayer K M :=
  AutomorphismSubgroupInversionJoin.invariant_join (sourceAction K) (M ⊔ radical K)
    (vectorLayer K M) (vector_invariant_join K M) (involution K)
    (fun v => involution_endpoint K v.toAdd)

private theorem orbit_bound (M L : Subgroup (source K))
    (hL : ∀ g ∈ L, ∀ v ∈ vectorLayer K M, sourceAction K g v ∈ vectorLayer K M)
    (hW : 1 < Nat.card (vectorLayer K M)) :
    Nat.card K^2-1 ≤ Nat.card (vectorLayer K M)*L.index := by
  letI : Nontrivial (vectorLayer K M) := Finite.one_lt_card_iff_nontrivial.mp hW
  obtain ⟨v,hv⟩ := exists_ne (1 : vectorLayer K M)
  have hv1 : v.val ≠ 1 := fun h => hv (Subtype.ext h)
  have hh := CentralExtensionLayerOrbitIndex.orbit_card_le (sourceAction K) L
    (vectorLayer K M) hL v.val v.property hv1
  have ho := source_endpoint_orbit_card K v.val.toAdd hv1
  rw [ofAdd_toAdd] at ho
  rw [ho] at hh
  exact hh.trans (Nat.mul_le_mul_right L.index (Nat.sub_le _ _))

theorem vector_orbit_bound (M : Subgroup (source K))
    (hW : 1 < Nat.card (vectorLayer K M)) :
    Nat.card K^2-1 ≤ Nat.card (vectorLayer K M)*(M ⊔ radical K).index :=
  orbit_bound K M _ (vector_invariant_join K M) hW

theorem vector_orbit_bound_enlarged (M : Subgroup (source K))
    (hW : 1 < Nat.card (vectorLayer K M)) :
    Nat.card K^2-1 ≤ Nat.card (vectorLayer K M)*
      ((M ⊔ radical K) ⊔ Subgroup.zpowers (involution K)).index :=
  orbit_bound K M _ (vector_invariant_enlarged_join K M) hW

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerOrbit

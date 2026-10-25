import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointSourceOrbit
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIsotropy
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralCapacity
import SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex
import SymmetricSubgroupAsymptotics.CentralExtensionIsotropicOrbitNumerics

/-! The full q^3 central intersection, the endpoint image and the join
index all come from one literal subgroup of the actual source normalizer.
The nonzero endpoint orbit and scalar-line isotropy are coupled through
that exact identity; independent worst-case indices are never multiplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointSourceIndex
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleCentralExtensionData
open CFSGGTwoD4GeckMiddleFullCentralLine CFSGGTwoD4GeckMiddleEndpointProjection
open CFSGGTwoD4GeckMiddleSourceNormalizer CFSGGTwoD4GeckMiddleEndpointSourceOrbit
open CFSGGTwoD4GeckMiddleEndpointIsotropy CFSGGTwoD4GeckMiddleCentralCapacity
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def highestElement : sourceNormalizer K :=
  ((radicalEquiv K).symm (central K (Multiplicative.ofAdd (1 : K)))).val

theorem source_index_le_of_highest_motion (hcard : 4 ≤ Nat.card K)
    (M : Subgroup (sourceNormalizer K)) (hM : highestElement K ∉ M) :
    3*(Nat.card K^2-1) ≤ M.index := by
  let e := radicalEquiv K
  let π := CFSGGTwoD4GeckMiddleSourceEndpointAction.projection K
  let ι := CFSGGTwoD4GeckMiddleSourceEndpointAction.centralEmbedding K
  let ψ := CFSGGTwoD4GeckMiddleSourceEndpointAction.sourceAction K hcard
  let J : Subgroup (radical K) := M.comap (radical K).subtype
  let A : Subgroup (fixedMiddle K) := J.comap e.symm.toMonoidHom
  let C : Subgroup (Subgroup.center (fixedMiddle K)) := J.comap ι
  let W : Subgroup (Multiplicative (Fin 2 → K)) := J.map π
  let L := M ⊔ radical K
  have hA : central K (Multiplicative.ofAdd (1 : K)) ∉ A := hM
  have hCeq : C = A.comap (Subgroup.center (fixedMiddle K)).subtype := rfl
  have hWeq : W = A.map (endpointHom K) := by
    change J.map ((endpointHom K).comp e.toMonoidHom) =
      (J.comap e.symm.toMonoidHom).map (endpointHom K)
    rw [←Subgroup.map_map,Subgroup.map_equiv_eq_comap_symm' e J]
  have hc : 3*Nat.card C ≤ Nat.card K^3 := by
    rw [hCeq]
    exact central_intersection_mul_three_le K hcard A hA
  have hw : Nat.card W ≤ Nat.card K := by
    rw [hWeq]
    exact vector_image_card_le K hcard A hA
  have hπ := CFSGGTwoD4GeckMiddleSourceEndpointAction.projection_surjective K hcard
  have hi := CFSGGTwoD4GeckMiddleSourceEndpointAction.centralEmbedding_range K hcard
  have he := ActualNormalLayerOrbitIndex.index_mul_layer_cards (radical K) M π hπ ι hi
  change M.index*Nat.card C*Nat.card W =
    Nat.card (Subgroup.center (fixedMiddle K))*Nat.card (Multiplicative (Fin 2 → K))*L.index at he
  have hV : Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K^2 := by
    change Nat.card (Fin 2 → K) = _
    rw [Nat.card_fun,Nat.card_fin]
  rw [center_card K hcard,hV] at he
  have horbit : 1 < Nat.card W → Nat.card K^2-1 ≤ (Nat.card W-1)*L.index := by
    intro hW
    letI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW
    obtain ⟨v,hv⟩ := exists_ne (1 : W)
    have hv1 : v.val ≠ 1 := fun h => hv (Subtype.ext h)
    have hh := ActualNormalLayerOrbitIndex.quotient_orbit_card_le (radical K) M π hπ ψ
      (CFSGGTwoD4GeckMiddleSourceEndpointAction.sourceAction_apply K hcard) v.val v.property hv1
    have ho : Nat.card (CentralExtensionLayerOrbitIndex.layerOrbit ψ v.val) = Nat.card K^2-1 :=
      source_endpoint_orbit_card K hcard v.val.toAdd hv1
    exact ho.symm.trans_le hh
  exact CentralExtensionIsotropicOrbitNumerics.prime_mul_orbit_le_index 3 (Nat.card K^3) (Nat.card K)
    M.index (Nat.card C) (Nat.card W) L.index (Nat.card K^2-1)
    (pow_pos (Nat.card_pos (α := K)) 3) (Nat.card_pos (α := K))
    (Nat.card_pos (α := C)) (Nat.card_pos (α := W))
    (Nat.pos_of_ne_zero (show L.index ≠ 0 from Subgroup.index_ne_zero_of_finite))
    hc hw he (Nat.sub_le _ _) horbit

theorem degree_le_of_highest_motion (hcard : 4 ≤ Nat.card K)
    {X : Type*} [Finite X] [MulAction (sourceNormalizer K) X]
    (x : X) (hx : highestElement K • x ≠ x) :
    3*(Nat.card K^2-1) ≤ Nat.card X := by
  calc
    _ ≤ (MulAction.stabilizer (sourceNormalizer K) x).index :=
      source_index_le_of_highest_motion K hcard _ hx
    _ = (MulAction.orbit (sourceNormalizer K) x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointSourceIndex

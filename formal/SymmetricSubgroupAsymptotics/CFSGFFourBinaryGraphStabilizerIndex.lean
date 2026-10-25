import SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphPointLayers
import SymmetricSubgroupAsymptotics.BinaryNormalCentralEvaluationIndex
import SymmetricSubgroupAsymptotics.HeisenbergAbelianProductIsotropy
import SymmetricSubgroupAsymptotics.CentralLayerOrbitCapacityNumerics

/-! The actual graph stabilizer supplies ONE radical intersection, ONE
central intersection, ONE vector image and ONE join index. No separate
worst-case indices, full Levi image or split extension are substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphStabilizerIndex
open CFSGFFourBinaryLeviConjugationGraph CFSGFFourBinaryGraphCentralLayers
open CFSGFFourBinaryGraphPointLayers CFSGFFourBinaryFixedRadicalEmbedding
open CFSGFFourBinaryRadicalCentralLayers
local instance fFourGraphIndexRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K=2)

private theorem map_comap_equiv {R S V : Type} [Group R] [Group S] [Group V]
    (e : R ≃* S) (π : R →* V) (U : Subgroup S) :
    (U.comap e.toMonoidHom).map π = U.map (π.comp e.symm.toMonoidHom) := by
  apply Subgroup.ext
  intro v
  constructor
  · rintro ⟨r,hr,hrv⟩
    refine ⟨e r,hr,?_⟩
    change π (e.symm (e r))=v
    rw [e.symm_apply_apply]
    exact hrv
  · rintro ⟨n,hn,hnv⟩
    refine ⟨e.symm n,?_,hnv⟩
    change e (e.symm n) ∈ U
    rw [e.apply_symm_apply]
    exact hn

private theorem point_card (hcard : Nat.card K=2) : Nat.card (Point K)=2^7 := by
  change Nat.card (((Fin 3 → K) × (Fin 3 → K)) × K)=2^7
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,hcard]
  norm_num

private theorem vector_card (hcard : Nat.card K=2) :
    Nat.card (Multiplicative ((Fin 4 → K) × (Fin 4 → K)))=2^8 := by
  rw [Nat.card_congr (Multiplicative.toAdd :
    Multiplicative ((Fin 4 → K) × (Fin 4 → K)) ≃ ((Fin 4 → K) × (Fin 4 → K)))]
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,hcard]
  norm_num

private theorem multiplicative_point_card (hcard : Nat.card K=2) :
    Nat.card (Multiplicative (Point K))=2^7 :=
  (Nat.card_congr (Multiplicative.toAdd : Multiplicative (Point K) ≃ Point K)).trans
    (point_card K hcard)

private theorem normalize_layer_cards {m c w l z v : ℕ}
    (hz : z=2^7) (hv : v=2^8) (he : m*c*w=z*v*l) : m*c*w=2^7*2^8*l := by
  rw [hz,hv] at he
  exact he

theorem central_capacity (M : Subgroup (Graph K hK))
    (hM : pointLift K hK (Multiplicative.ofAdd ((0,1) : Point K)) ∉
      M.comap (liftedRadical K hK).subtype) :
    2*4*Nat.card ((M.comap (liftedRadical K hK).subtype).comap (pointLift K hK)) ≤
      2^7*(M ⊔ liftedRadical K hK).index := by
  have h := BinaryNormalCentralEvaluationIndex.normalized_central_orbit_capacity
    hK (liftedRadical K hK) M (pointLift K hK) (pointLift_injective K hK)
    (pointLift_central K hK) (vectorAction K hK) (vectorAction_polar K hK)
    (pointLift_covariance K hK) (exists_Y_transvection K hK) hM (by decide)
  simpa only [hK,Fintype.card_fin,point_card K hK] using h

theorem vector_image_card_le (M : Subgroup (Graph K hK))
    (hM : pointLift K hK (Multiplicative.ofAdd ((0,1) : Point K)) ∉
      M.comap (liftedRadical K hK).subtype) :
    Nat.card ((M.comap (liftedRadical K hK).subtype).map (vectorMap K hK)) ≤ 2^4 := by
  let U := M.comap (liftedRadical K hK).subtype
  let e := radicalEquiv K hK
  let J := U.comap e.toMonoidHom
  have hJ : centralCoordinates K (Multiplicative.ofAdd ((1 : K),(0 : Extra K))) ∉ J := hM
  have hiso := HeisenbergAbelianProductIsotropy.vectorImage_card_le
    (K := K) (E := Extra K) (m := 4) 2 J hJ
  have hmap : J.map (vectorProjection K) = U.map (vectorMap K hK) :=
    map_comap_equiv e (vectorProjection K) U
  have hcard : Nat.card (HeisenbergAbelianProductIsotropy.vectorImage J) =
      Nat.card (U.map (vectorMap K hK)) := by
    change Nat.card (J.map (vectorProjection K)) = _
    rw [hmap]
  rw [hcard,hK] at hiso
  exact hiso

theorem graph_index_lower (M : Subgroup (Graph K hK))
    (hM : pointLift K hK (Multiplicative.ofAdd ((0,1) : Point K)) ∉
      M.comap (liftedRadical K hK).subtype) : 128 ≤ M.index := by
  let U := M.comap (liftedRadical K hK).subtype
  let C := U.comap (pointLift K hK)
  let W := U.map (vectorMap K hK)
  have he := ActualNormalLayerOrbitIndex.index_mul_layer_cards
    (liftedRadical K hK) M (vectorMap K hK) (vectorMap_surjective K hK)
    (pointLift K hK) (pointLift_range_eq_kernel K hK)
  have he' := normalize_layer_cards (multiplicative_point_card K hK) (vector_card K hK) he
  exact CentralLayerOrbitCapacityNumerics.binary_eight_seven_index
    M.index (Nat.card C) (Nat.card W) (M ⊔ liftedRadical K hK).index Nat.card_pos
    (vector_image_card_le K hK M hM) (central_capacity K hK M hM) he'

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphStabilizerIndex

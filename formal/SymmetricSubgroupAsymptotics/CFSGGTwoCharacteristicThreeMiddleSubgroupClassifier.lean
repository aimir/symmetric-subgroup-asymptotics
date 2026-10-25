import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleLayerOrbit
import SymmetricSubgroupAsymptotics.GTwoFieldThreeJointCapacityNumerics

/-! Small-index classification inside the actual field-three source.
The full central intersection C, endpoint image W and join M∨N are kept
throughout. The conclusion is a horizontal central plane, not a false
local index bound of fifty-four. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSubgroupClassifier
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleSourceRadical
open CFSGGTwoCharacteristicThreeMiddleSourceInvolution
open CFSGGTwoCharacteristicThreeMiddleLayerCounts
open CFSGGTwoCharacteristicThreeMiddleLayerOrbit
open CFSGGTwoCharacteristicThreeMiddleCentralJoin
open CFSGGTwoCharacteristicThreeCentralGraph
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : Finite (source K) := source_finite K

private theorem capacity_facts (hcard : Nat.card K = 3)
    (M : Subgroup (source K)) (hM : highestElement K ∉ M) :
    Nat.card (centralLayer K M) ≤ 9 ∧ Nat.card (centralLayer K M) ∣ 27 ∧
    (Nat.card (vectorLayer K M) = 1 ∨ Nat.card (vectorLayer K M) = 3) ∧
    M.index*Nat.card (centralLayer K M)*Nat.card (vectorLayer K M) =
      243*(M ⊔ radical K).index ∧
    (Nat.card (vectorLayer K M) = 3 → 8 ≤ 3*(M ⊔ radical K).index) ∧
    (Nat.card (vectorLayer K M) = 3 →
      8 ≤ 3*((M ⊔ radical K) ⊔ Subgroup.zpowers (involution K)).index) := by
  have hc := central_capacity K M hM
  rw [hcard] at hc
  have hc9 : Nat.card (centralLayer K M) ≤ 9 := by norm_num at hc; omega
  have hz : Nat.card (Multiplicative (Fin 3 → K)) = 27 := by
    change Nat.card (Fin 3 → K) = _
    rw [Nat.card_fun,Nat.card_fin,hcard]
    norm_num
  have hcdiv := Subgroup.card_subgroup_dvd_card (centralLayer K M)
  rw [hz] at hcdiv
  have hw := vector_capacity K M hM
  rw [hcard] at hw
  have hv : Nat.card (Multiplicative (Fin 2 → K)) = 9 := by
    change Nat.card (Fin 2 → K) = _
    rw [Nat.card_fun,Nat.card_fin,hcard]
    norm_num
  have hwdiv := Subgroup.card_subgroup_dvd_card (vectorLayer K M)
  rw [hv] at hwdiv
  have hwp := Nat.card_pos (α := vectorLayer K M)
  have hwcases : Nat.card (vectorLayer K M) = 1 ∨ Nat.card (vectorLayer K M) = 3 := by
    have hh : Nat.card (vectorLayer K M) = 1 ∨
        Nat.card (vectorLayer K M) = 2 ∨ Nat.card (vectorLayer K M) = 3 := by omega
    rcases hh with h1|h2|h3
    · exact Or.inl h1
    · rw [h2] at hwdiv
      norm_num at hwdiv
    · exact Or.inr h3
  refine ⟨hc9,hcdiv,hwcases,?_,?_,?_⟩
  · simpa only [hcard,Nat.reducePow,Nat.reduceMul] using index_mul_layer_cards K M
  · intro hw3
    have ho := vector_orbit_bound K M (by rw [hw3]; decide)
    simpa only [hcard,hw3,Nat.reducePow,Nat.reduceSub] using ho
  · intro hw3
    have ho := vector_orbit_bound_enlarged K M (by rw [hw3]; decide)
    simpa only [hcard,hw3,Nat.reducePow,Nat.reduceSub] using ho

theorem source_index_ge_twentySeven (hcard : Nat.card K = 3)
    (M : Subgroup (source K)) (hM : highestElement K ∉ M) : 27 ≤ M.index := by
  obtain ⟨hc,hd,hw,hprod,hline,henlarge⟩ := capacity_facts K hcard M hM
  exact GTwoFieldThreeJointCapacityNumerics.index_ge_twentySeven _ _ _ _
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hc hw hline hprod

theorem involution_mem_join_of_index_lt (hcard : Nat.card K = 3)
    (M : Subgroup (source K)) (hM : highestElement K ∉ M) (hm : M.index < 54) :
    involution K ∈ M ⊔ radical K := by
  obtain ⟨hc,hd,hw,hprod,hline,henlarge⟩ := capacity_facts K hcard M hM
  by_contra ht
  have he := CentralModuloNormalInvolutionJoin.index_double_of_commutators
    (radical K) (M ⊔ radical K) le_sup_right (involution K)
    (involution_square K) ht (involution_commutator_mem K)
  have he' : (M ⊔ radical K).index =
      2*((M ⊔ radical K) ⊔ Subgroup.zpowers (involution K)).index :=
    he.symm.trans (Nat.mul_comm _ _)
  have hh := GTwoFieldThreeJointCapacityNumerics.index_ge_fiftyFour_of_double_join _ _ _ _ _
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hc hw he' henlarge hprod
  exact (Nat.not_lt_of_ge hh) hm

theorem central_card_eq_nine_of_index_lt (hcard : Nat.card K = 3)
    (M : Subgroup (source K)) (hM : highestElement K ∉ M) (hm : M.index < 54) :
    Nat.card (centralLayer K M) = 9 := by
  obtain ⟨hc,hd,hw,hprod,hline,henlarge⟩ := capacity_facts K hcard M hM
  exact GTwoFieldThreeJointCapacityNumerics.central_card_eq_nine_of_index_lt _ _ _ _
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hc hd hw hline hprod hm

theorem central_layer_horizontal_of_index_lt (hcard : Nat.card K = 3)
    (M : Subgroup (source K)) (hM : highestElement K ∉ M) (hm : M.index < 54) :
    (centralLayer K M).toAddSubgroup' =
      (LinearMap.proj (2 : Fin 3) : (Fin 3 → K) →ₗ[K] K).toAddMonoidHom.ker := by
  have hhigh : vertical K 1 ∉ (centralLayer K M).toAddSubgroup' := hM
  have ht := involution_mem_join_of_index_lt K hcard M hM hm
  have hflip := central_preimage_flip K M ht
  have hc : Nat.card (centralLayer K M).toAddSubgroup' = Nat.card K^2 := by
    change Nat.card (centralLayer K M) = _
    rw [central_card_eq_nine_of_index_lt K hcard M hM hm,hcard]
    norm_num
  exact eq_horizontal_of_flip_card K hcard (centralLayer K M).toAddSubgroup' hhigh hflip hc

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSubgroupClassifier

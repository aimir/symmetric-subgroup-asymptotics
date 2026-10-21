import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoWideKernelModels
import SymmetricSubgroupAsymptotics.DerivedOneThousandTwentyFourUnitBound
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSmallNormalCenters
import SymmetricSubgroupAsymptotics.BinaryHeisenbergSixCanonicalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairRankSixTopQuotientCenter
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessOneAbelianization
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank
import SymmetricSubgroupAsymptotics.TransitiveNonabelianCenterBound

/-! The whole original rank-nine source with actual rank-six top and
whole kernel head four has an all-normal unit packet. The three original
coordinate states are selected internally; no rank-ten hypothesis or
outer split is inferred. Only the fullconstant order-two capacity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance wideKernelUnitPacketPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) [MulAction.IsPretransitive U X]
include F

theorem rank_nine_rank_six_top_wide_kernel_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (hwide : 4≤MarkedC4.normalGen F.top.ker)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U)=512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp,hrank]
    decide
  have hderived_of_card (b : ℕ) (hb : Nat.card U≤512*b) : Nat.card (commutator U)≤b := by
    have hh := (commutator U).card_mul_index
    change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
    rw [hAb] at hh
    nlinarith
  have hsourceCenter : Nat.card (Subgroup.center U)≤32 := by
    have hc := Nat.card_le_card_of_injective
      (fun z : Subgroup.center U => (z : U) • F.frame (0,0))
      (transitive_center_evaluation_injective (F.frame (0,0)))
    exact hc.trans_eq hdegree
  have hquotCenter (L : Subgroup U) [L.Normal]
      (hnon : ¬∀ a b : U ⧸ L,a*b=b*a) : Nat.card (Subgroup.center (U ⧸ L))≤256 :=
    F.rank_six_top_nonabelian_quotient_center_card_le_256 hU hTopRank L hnon
  obtain ⟨E,hzero,hmodels⟩ := F.rank_six_top_wide_original_kernel_models hU hTopRank hwide
  rcases hmodels with ⟨hH,hK,hS | hS⟩ | ⟨hH,hK,hS⟩
  · change E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) at hH
    change E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space at hK
    have htopcard : Nat.card F.top.range=128 := by
      rw [E.card_of_original_zero_frame hzero,hK,hH,
        BinaryRegularSixCanonicalGenerators.K.card,BinaryMenuCayley8T3.exact_card]
      norm_num
    have hkcard : Nat.card F.kernelSpace=256 :=
      F.kernelSpace_card_of_original_coordinate_state E (BinaryRegular46GraphHeadRigidity.stateChart 0) hS
    have hcard : Nat.card U=32768 := by
      have hh := F.kernelSpace_card_mul_top
      rw [hkcard,htopcard] at hh
      omega
    have hd : Nat.card (commutator U)≤64 := hderived_of_card 64 (by rw [hcard])
    apply derived_one_thousand_twenty_four_unit_packet hU (hd.trans (by decide)) hsourceCenter hquotCenter ?_ N hnonab
    intro L _ _ _ hlarge
    omega
  · change E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) at hH
    change E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space at hK
    change (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      BinaryRegularFullConstantPlaneOne.K.space at hS
    have htopcard : Nat.card F.top.range=128 := by
      rw [E.card_of_original_zero_frame hzero,hK,hH,
        BinaryRegularSixCanonicalGenerators.K.card,BinaryMenuCayley8T3.exact_card]
      norm_num
    have hkcard : Nat.card F.kernelSpace=4096 :=
      F.kernelSpace_card_of_original_coordinate_state E BinaryRegularFullConstantPlaneOne.K hS
    have hcard : Nat.card U=524288 := by
      have hh := F.kernelSpace_card_mul_top
      rw [hkcard,htopcard] at hh
      omega
    have hd : Nat.card (commutator U)≤1024 := hderived_of_card 1024 (by rw [hcard])
    apply derived_one_thousand_twenty_four_unit_packet hU hd hsourceCenter hquotCenter ?_ N hnonab
    intro L _ _ htwo _
    exact (F.fullconstant_normal_two_quotient_center_card_le_eight E hU hzero hH hK hS L htwo).trans (by decide)
  · change E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) at hH
    change E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space at hK
    have htopcard : Nat.card F.top.range=256 := by
      rw [E.card_of_original_zero_frame hzero,hK,hH,
        BinaryHeisenbergSixCanonicalGenerators.K.card,BinaryMenuCayley8T22.exact_card]
      norm_num
    have hkcard : Nat.card F.kernelSpace=1024 :=
      F.kernelSpace_card_of_original_coordinate_state E (BinaryHeisenberg14GraphHeadRigidity.stateChart 0) hS
    have hcard : Nat.card U=262144 := by
      have hh := F.kernelSpace_card_mul_top
      rw [hkcard,htopcard] at hh
      omega
    have hd : Nat.card (commutator U)≤512 := hderived_of_card 512 (by rw [hcard])
    apply derived_one_thousand_twenty_four_unit_packet hU (hd.trans (by decide)) hsourceCenter hquotCenter ?_ N hnonab
    intro L _ _ _ hlarge
    omega
end SymmetricSubgroupAsymptotics.BinaryPairFrame

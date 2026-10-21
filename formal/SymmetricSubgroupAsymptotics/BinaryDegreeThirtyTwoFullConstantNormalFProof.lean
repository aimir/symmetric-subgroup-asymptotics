import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSmallNormalCenters
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.BinaryPairRankSixTopQuotientCenter
import SymmetricSubgroupAsymptotics.DerivedFiveTwelveNormalFBound
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder

/-! Complete all-original-normal normal-F packet for the fullconstant
rank-ten template. The actual outer action and arbitrary offsets remain;
seven scalar planes cover only its order-four derived denominators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance fullconstantNormalFProofPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem fullconstant_rank_ten_all_normalF_packet
    (hU : IsPGroup 2 U) (hhigh : 10≤MarkedC4.genRank U)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      BinaryRegularFullConstantPlaneOne.K.space)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+(5/4 : ℝ)*centralLog V≤16 ∧ centralLog V≤8 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hAb : Nat.card (Abelianization U)=1024 := by
    have hu := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    rw [hdegree] at hu
    norm_num at hu
    have hl := (Nat.pow_le_pow_right (by decide : 0<2) hhigh).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
    norm_num at hl
    omega
  have htopcard : Nat.card F.top.range=128 := by
    rw [E.card_of_original_zero_frame hzero,hK,hH,
      BinaryRegularSixCanonicalGenerators.K.card,BinaryMenuCayley8T3.exact_card]
    norm_num
  have hkcard : Nat.card F.kernelSpace=4096 := by
    exact F.kernelSpace_card_of_original_coordinate_state E BinaryRegularFullConstantPlaneOne.K hS
  have hUcard : Nat.card U=524288 := by
    have hh := F.kernelSpace_card_mul_top
    rw [hkcard,htopcard] at hh
    omega
  have hderived : Nat.card (commutator U)≤512 := by
    have hh := (commutator U).card_mul_index
    change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
    rw [hAb,hUcard] at hh
    omega
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    simpa only [F.original_ambientAxis_kernel] using hS
  apply derived_five_twelve_normalF_packet hU hderived
    ((F.original_fullconstant_center_card_le_two E hU hspace).trans (by decide))
    (fun L _ hnon => F.rank_six_top_nonabelian_quotient_center_card_le_256 hU hTopRank L hnon)
    ?_ N hnonab
  intro L _ _ hsmall
  rcases hsmall with htwo | hfour
  · exact (F.fullconstant_normal_two_quotient_center_card_le_eight E hU hzero hH hK hS L htwo).trans (by decide)
  · exact (F.fullconstant_normal_four_quotient_center_card_le_thirty_two E hU hzero hH hK hS L hfour).trans (by decide)
end SymmetricSubgroupAsymptotics.BinaryPairFrame

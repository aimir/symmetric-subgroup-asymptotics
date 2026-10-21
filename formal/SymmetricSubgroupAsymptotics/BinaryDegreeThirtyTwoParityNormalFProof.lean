import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.BinaryPairRankSixTopQuotientCenter
import SymmetricSubgroupAsymptotics.BinaryRegular46GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryRegularSixCanonicalGenerators
import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder

/-! The parity-zero rank-ten source has actual derived order32. The
proved rank-six-top quotient-centre bound256 supplies every original
normal quotient directly; no small-denominator scalar packet is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance parityNormalFProofPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem regular_parity_rank_ten_all_normalF_packet
    (hU : IsPGroup 2 U) (hhigh : 10≤MarkedC4.genRank U)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      (BinaryRegular46GraphHeadRigidity.stateChart 0).space)
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
  have hkcard : Nat.card F.kernelSpace=256 :=
    F.kernelSpace_card_of_original_coordinate_state E (BinaryRegular46GraphHeadRigidity.stateChart 0) hS
  have hUcard : Nat.card U=32768 := by
    have hh := F.kernelSpace_card_mul_top
    rw [hkcard,htopcard] at hh
    omega
  have hderived : Nat.card (commutator U)≤32 := by
    have hh := (commutator U).card_mul_index
    change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
    rw [hAb,hUcard] at hh
    omega
  have hd : Nat.card (commutator (U ⧸ N))≤32 :=
    (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hderived
  have hz := F.rank_six_top_nonabelian_quotient_center_card_le_256 hU hTopRank N hnonab
  have hp := normalF_fiveQuarter_packet_of_actual_product_bound (⊤ : Subgroup (U ⧸ N)) 16 8 (by
    simpa only [targetCommutator,commutator_def,targetCentralizer,Subgroup.coe_top,
      Subgroup.centralizer_univ] using
      (Nat.mul_le_mul (Nat.pow_le_pow_left hd 4) (Nat.pow_le_pow_left hz 5)).trans
        (by norm_num : 32^4*256^5≤2^(4*16))) (by
    simpa only [targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ] using hz)
  exact ⟨⊤,inferInstance,hp⟩
end SymmetricSubgroupAsymptotics.BinaryPairFrame

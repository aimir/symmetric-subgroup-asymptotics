import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryKernelDimension
import SymmetricSubgroupAsymptotics.BinaryPairRankNineElementaryIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct

/-! The full coefficient-prefix bound closes every original quotient in
the rank-nine elementary-top case. The original derived group has order
at most128 and the same quotient has center at most256, so its whole
group is a valid unit-coefficient normal F. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem elementary_rank_nine_all_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hpow : ∀ t : F.top.range,t^2=1)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hdim := F.rank_nine_elementary_kernel_finrank_le_twelve hU hrank.ge hpow
  have hTopCard : Nat.card F.top.range=16 := by
    simpa only [Nat.card_fin] using ElementaryBinaryTransitiveNormalRank.card_eq_degree
      (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow) (0 : Fin 16)
  have hKCard : Nat.card F.kernelSpace≤4096 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hdim).trans (by norm_num)
  have hGCard : Nat.card U≤65536 := by
    have h := F.kernelSpace_card_mul_top
    rw [hTopCard] at h
    nlinarith
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U)=512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp,hrank]
    norm_num
  have hderived : Nat.card (commutator U)≤128 := by
    have hh := (commutator U).card_mul_index
    change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
    rw [hAb] at hh
    omega
  have hd := (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hderived
  have hz := F.rank_nine_elementary_quotient_center_card_le_256_of_kernel_dimension
    hU hrank hpow hdim N hnonab
  have hp := normalF_unit_packet_of_actual_product_bound (⊤ : Subgroup (U ⧸ N)) 16 8 (by
    simpa only [targetCommutator,commutator_def,targetCentralizer,
      Subgroup.coe_top,Subgroup.centralizer_univ] using
      (Nat.mul_le_mul hd hz).trans (by norm_num : 128*256≤2^16)) (by
    simpa only [targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ] using hz)
  exact ⟨⊤,inferInstance,hp⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame

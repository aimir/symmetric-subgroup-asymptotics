import SymmetricSubgroupAsymptotics.RDTNormalFRemainingDegreeAssembly
import SymmetricSubgroupAsymptotics.RDTNormalFRegularRankFive
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergRankFive
import SymmetricSubgroupAsymptotics.RDTNormalFSmallPairTopExcessOne
import SymmetricSubgroupAsymptotics.RDTNormalFTopTwentyNine
import SymmetricSubgroupAsymptotics.RDTNormalFTopThirtyOne
import SymmetricSubgroupAsymptotics.BinaryPairTopThirtyRankBound
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveHighTopDispatch

/-! Complete degree-sixteen excess-one assembly on the original group
and its SAME rank-preserving normal quotient. Reindexing pair labels does
not replace the group, denominator, or quotient by a split extension. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure
local instance sixteenNormalFProofFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binarySixteenExcessOneNormalF_proved : BinarySixteenExcessOneNormalF := by
  intro G hG htrans hexcess N _ hnonab hquot
  letI : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  have hrank := degree_sixteen_excess_one_genRank_eq_five G hG htrans hexcess
  have hhigh : 5≤genRank G := by omega
  have hexp := binary_excess_one_abelianization_exponent 16 G (by decide) hG htrans hexcess
  have hNderived := binary_excess_one_rank_preserving_denominator_le_commutator
    16 G (by decide) hG htrans hexcess N hquot
  have hAbG : Nat.card (Abelianization G)=32 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hG hexp,hrank]
    norm_num
  have hAbQ : Nat.card (Abelianization (G ⧸ N))≤32 := by
    let a := Abelianization.map (QuotientGroup.mk' N)
    have ha : Function.Surjective a := by
      intro x
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (commutator (G ⧸ N)) x
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N y
      exact ⟨Abelianization.of g,Abelianization.map_of _ g⟩
    exact (Nat.card_le_card_of_surjective a ha).trans hAbG.le
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 3 G hG (by norm_num only [Nat.card_fin])
  by_cases hregular : ∃ c : Equiv.Perm (Fin 8),MulAut.conj c • F.top.range=
      Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)
  · obtain ⟨c,hc⟩ := hregular
    have hh : (F.reindex c).top.range=BinaryRegularEightNaturalRegistry.H := by
      rw [F.reindex_top_range_conjugation]
      exact hc
    exact (F.reindex c).regular_rank_five_all_normal_quotients_unit hG hhigh hh N hnonab
  by_cases hheisenberg : ∃ c : Equiv.Perm (Fin 8),MulAut.conj c • F.top.range=
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)
  · obtain ⟨c,hc⟩ := hheisenberg
    have hh : (F.reindex c).top.range=BinaryHeisenbergEightNaturalHeads.H := by
      rw [F.reindex_top_range_conjugation]
      exact hc
    exact (F.reindex c).heisenberg_rank_five_all_normal_quotients_unit hG hhigh hh N hnonab
  rcases F.rank_five_residual_high_top_dispatch hG hhigh hregular hheisenberg with
    hsmall | ⟨c,h29|h30|h31⟩
  · letI : MulAction F.top.range (Fin 8) := inferInstance
    letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
    letI : MulAction G (Fin 8) := MulAction.compHom (Fin 8) F.top
    letI : MulAction.IsPretransitive G (Fin 8) := ⟨by
      intro i j
      obtain ⟨t,ht⟩ := MulAction.exists_smul_eq F.top.range i j
      obtain ⟨g,rfl⟩ := F.top.rangeRestrict_surjective t
      exact ⟨g,ht⟩⟩
    have hact : ∀ (g : G) (i : Fin 8),g • i=F.top g i := fun _ _ => rfl
    obtain ⟨_,_,htop,_,_,_⟩ :=
      F.rank_five_residual_top_saturation hact hG hhigh hregular hheisenberg
    have hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := G) (X := Fin 8) := by
      intro hel
      apply hregular
      apply BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
        F.top.range (F.top_isPGroup hG)
        (fun i j => MulAction.exists_smul_eq F.top.range i j)
      intro t i
      obtain ⟨g,rfl⟩ := F.top.rangeRestrict_surjective t
      rw [←map_pow]
      exact (hact (g^2) i).symm.trans (hel g i)
    exact F.small_pair_top_excess_one_rank_preserving_unit hact hG htrans hexcess
      hnon hsmall htop.le N (hquot.trans hrank) hnonab
  · exact (F.reindex c).top_twenty_nine_all_normal_unit hG hhigh h29
      N hNderived hAbQ hnonab
  · have hlow := (F.reindex c).genRank_le_four_of_top_thirty hG h30
    omega
  · exact (F.reindex c).top_thirty_one_all_normal_unit hG hhigh h31
      N hNderived hAbQ hnonab

end SymmetricSubgroupAsymptotics

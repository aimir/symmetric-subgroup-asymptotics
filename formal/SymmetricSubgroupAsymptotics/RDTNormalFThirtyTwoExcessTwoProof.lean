import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoNonelementaryKernelModels
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryNormalFProof
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoParityNormalFProof
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoFullConstantNormalFProof
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoHeisenbergNormalFProof
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessTwoAbelianization

/-! Complete excess-two degree32 normal-F theorem. The original action
selects either the elementary model or one of three nonelementary kernel
models. The original denominator is passed unchanged into each proved
all-normal consumer; the outer extension is never assumed split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel

theorem theorem57_degree_thirty_two_excess_two
    (G : Subgroup (Equiv.Perm (Fin 32))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 32,∃ g : G,g.val x=y)
    (hexcess : HasExcess G 32 2)
    (N : Subgroup G) [N.Normal] (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a) :
    ∃ F : Subgroup (G ⧸ N),F.Normal ∧
      commutatorLog F+(5/4 : ℝ)*centralLog F≤16 ∧ centralLog F≤8 := by
  letI : MulAction.IsPretransitive G (Fin 32) := ⟨htrans⟩
  have hrank := binary_degree_thirty_two_excess_two_genRank_eq_ten G hG
    (by simp only [Nat.card_fin]) hexcess
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 4 G hG (by norm_num only [Nat.card_fin])
  by_cases hpow : ∀ t : F.top.range,t^2=1
  · exact F.elementary_rank_ten_normalF_packet hG hrank.ge hpow N hnonab
  obtain ⟨_,_,hTopRank,E,hzero,hmodels⟩ :=
    F.rank_ten_nonelementary_original_kernel_models hG hrank.ge hpow
  rcases hmodels with ⟨hH,hK,hS|hS⟩ | ⟨hH,hK,hS⟩
  · exact F.regular_parity_rank_ten_all_normalF_packet E hG hrank.ge hTopRank.ge
      hzero hH hK hS N hnonab
  · exact F.fullconstant_rank_ten_all_normalF_packet E hG hrank.ge hTopRank.ge
      hzero hH hK hS N hnonab
  · exact F.heisenberg_rank_ten_all_normalF_packet E hG hrank.ge hTopRank.ge
      hzero hH hK hS N hnonab

end SymmetricSubgroupAsymptotics

import SymmetricSubgroupAsymptotics.RDTNormalFThirtyTwoCriticalReduction
import SymmetricSubgroupAsymptotics.RDTNormalFThirtyTwoExcessTwoProof
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessOneProof

/-! Final degree and excess dispatch. The only parameters here are the
two internal critical clauses, to be installed by their proved concrete
original-action consumers; they are not proposed literature inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel

theorem binaryNormalFTargetAtThirtyTwo_of_critical_clauses
    (h36 : BinaryThirtyTwoCriticalHeadTopNormalF 3 6)
    (h45 : BinaryThirtyTwoCriticalHeadTopNormalF 4 5) : BinaryNormalFTargetAtDegree 32 := by
  have hhalf : (32:ℝ)/2=16 := by norm_num
  have hquarter : (32:ℝ)/4=8 := by norm_num
  intro G hG htrans i hi hexcess N _ hnonab hrank
  rcases hi with rfl | rfl
  · obtain ⟨F,hF,hc,hz⟩ := theorem57_degree_thirty_two_excess_one_of_critical_clauses
      h36 h45 G hG htrans hexcess N hnonab (hrank rfl)
    refine ⟨F,1,hF,Or.inr (Or.inl ⟨rfl,rfl⟩),?_,?_⟩
    · simpa only [one_mul,Nat.cast_ofNat,hhalf] using hc
    · simpa only [Nat.cast_ofNat,hquarter] using hz
  · obtain ⟨F,hF,hc,hz⟩ := theorem57_degree_thirty_two_excess_two G hG htrans hexcess N hnonab
    refine ⟨F,5/4,hF,Or.inr (Or.inr ⟨rfl,rfl⟩),?_,?_⟩
    · simpa only [Nat.cast_ofNat,hhalf] using hc
    · simpa only [Nat.cast_ofNat,hquarter] using hz

theorem publishedTheorem57Binary_of_critical_clauses
    (h36 : BinaryThirtyTwoCriticalHeadTopNormalF 3 6)
    (h45 : BinaryThirtyTwoCriticalHeadTopNormalF 4 5) : PublishedTheorem57Binary :=
  publishedTheorem57Binary_of_remaining_degree_clauses
    binarySixteenExcessOneNormalF_proved
    (binaryNormalFTargetAtThirtyTwo_of_critical_clauses h36 h45)

end SymmetricSubgroupAsymptotics

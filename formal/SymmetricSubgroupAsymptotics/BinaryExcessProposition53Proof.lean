import SymmetricSubgroupAsymptotics.BinaryDegreeFourExcessProfile
import SymmetricSubgroupAsymptotics.BinaryDegreeEightExcessProfile
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessProfile
import SymmetricSubgroupAsymptotics.BinarySharpLargeDegreeNormalBound

/-! Exact ordinary RDT5.3 binary excess conclusion. All inputs are
proved source theorems; no published excess or replacement classification
premise is added. Original point degree and ambient normal generation
are retained through the complete small-degree/tail split. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open MarkedC4

theorem publishedProposition53Binary_proved :
    MarkedC4.ActualCaseIITargetStructure.PublishedProposition53Binary := by
  intro n G hn hG htrans hhigh
  letI : MulAction.IsPretransitive G (Fin n) := ⟨htrans⟩
  by_cases hlarge : 64 ≤ n
  · obtain ⟨N,hN,hbig⟩ := hhigh
    letI := hN
    have hb := twoGroup_transitive_normalGen_le_quarter_of_large_degree G hG
      (by simpa only [Nat.card_fin] using hlarge) N
    simp only [Nat.card_fin] at hb
    have hm := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mp hb
    have hr : (normalGen N : ℝ) * 4 ≤ (n : ℝ) := by exact_mod_cast hm
    exfalso
    linarith
  · let x : Fin n := ⟨0,by omega⟩
    obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hG
      (MulAction.stabilizer G x) ⊤ le_top
    have hcard : n = 2 ^ s.length := by
      simpa only [Subgroup.relIndex_top_right,
        MulAction.index_stabilizer_of_transitive G x,Nat.card_fin] using s.relIndex
    have hlo : 2 ≤ s.length := by
      by_contra h
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s.length ≤ 1)
      rw [← hcard] at hp
      norm_num at hp
      omega
    have hup : s.length ≤ 5 := by
      by_contra h
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ s.length)
      rw [← hcard] at hp
      norm_num at hp
      omega
    have hdegrees : n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 := by
      have hs : s.length = 2 ∨ s.length = 3 ∨ s.length = 4 ∨ s.length = 5 := by omega
      rcases hs with hs | hs | hs | hs <;> rw [hs] at hcard <;> norm_num at hcard <;> omega
    rcases hdegrees with rfl | rfl | rfl | rfl
    · exact BinaryDegreeFourExcessProfile.proposition53_degree_four G hG htrans hhigh
    · exact BinaryDegreeEightExcessProfile.proposition53_degree_eight G hG htrans hhigh
    · exact BinaryDegreeSixteenExcessProfile.proposition53_degree_sixteen G hG htrans hhigh
    · exact BinaryDegreeThirtyTwoExcessProfile.proposition53_degree_thirty_two G hG htrans hhigh

end SymmetricSubgroupAsymptotics

import SymmetricSubgroupAsymptotics.BinaryDegreeFourProperNormalRank
import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIITargetStructure

/-! The exact first excess packet is intrinsic to the original four
points. It uses only the proved half-degree and proper-normal bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryDegreeFourExcessProfile
open MarkedC4 MarkedC4.RDTExcessStructure

theorem proposition53_degree_four
    (G : Subgroup (Equiv.Perm (Fin 4))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 4, ∃ g : G, g.val x = y)
    (hhigh : ∃ N : Subgroup G, N.Normal ∧ (4 : ℝ) / 4 < normalGen N) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧ HasExcess G 4 i ∧ 4 ≤ 32 ∧
      (i = 1 → ∀ N : Subgroup G, N.Normal → (4 : ℝ) / 4 < normalGen N → N = ⊤) ∧
      (i = 2 → 4 = 8 ∨ 4 = 16 ∨ 4 = 32) := by
  letI : MulAction.IsPretransitive G (Fin 4) := ⟨htrans⟩
  have hall (N : Subgroup G) [N.Normal] : normalGen N ≤ 2 := by
    have hN := hG.to_subgroup N
    have hb := (normalGen_normalSubgroup_le_primeCharacterRank 2 N hN).trans
      (permutationTwoGroup_primeCharacterRank_le N (Fin 4) hN)
    simpa only [Nat.card_fin] using hb
  have hexcess : HasExcess G 4 1 := by
    constructor
    · obtain ⟨N,hN,hbig⟩ := hhigh
      letI := hN
      have hb := hall N
      norm_num at hbig
      have hNat : 1 < normalGen N := by exact_mod_cast hbig
      have heq : normalGen N = 2 := by omega
      exact ⟨N,hN,by norm_num [heq]⟩
    · intro N hN
      letI := hN
      norm_num
      exact hall N
  refine ⟨1,Or.inl rfl,hexcess,by decide,?_,by intro h;omega⟩
  intro _ N hN hbig
  letI := hN
  by_contra hproper
  have hb := twoGroup_transitive_degree_four_proper_normalGen_le_one
    (by simp only [Nat.card_fin]) G hG N hproper
  norm_num at hbig
  have hNat : 1 < normalGen N := by exact_mod_cast hbig
  omega

end SymmetricSubgroupAsymptotics.BinaryDegreeFourExcessProfile

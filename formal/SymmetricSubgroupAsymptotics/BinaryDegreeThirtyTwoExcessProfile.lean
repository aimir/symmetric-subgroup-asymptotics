import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoProperSaving
import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIITargetStructure

/-! Exact degree32 excess packet, with the actual proper-normal saving
proved internally from the original source and literal point action. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessProfile

open MarkedC4 MarkedC4.RDTExcessStructure

/-- Only the original whole group is excessive in excess-one degree32. -/
theorem only_whole_of_excess_one
    (G : Subgroup (Equiv.Perm (Fin 32))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 32, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 32 1)
    (N : Subgroup G) [N.Normal] (hhigh : (32 : ℝ) / 4 < normalGen N) : N = ⊤ := by
  letI : MulAction.IsPretransitive G (Fin 32) := ⟨htrans⟩
  letI : Group.IsNilpotent G := hG.isNilpotent
  have hwhole := hexcess.2 (⊤ : Subgroup G) inferInstance
  norm_num at hwhole hhigh
  have hwholeNat : normalGen (⊤ : Subgroup G) ≤ 9 := by exact_mod_cast hwhole
  have hgen := MarkedC4.genRank_le_normalGen_top (G := G)
  by_contra hproper
  have hNsmall : 8 < normalGen N := by exact_mod_cast hhigh
  have hN : 9 ≤ normalGen N := by omega
  have hten := twoGroup_degree_thirty_two_ten_le_genRank_of_proper_normal_nine
    G hG (by simp only [Nat.card_fin]) N hproper hN
  omega

/-- Full exact h53 conclusion at degree32, with no published excess input. -/
theorem proposition53_degree_thirty_two
    (G : Subgroup (Equiv.Perm (Fin 32))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 32, ∃ g : G, g.val x = y)
    (hhigh : ∃ N : Subgroup G, N.Normal ∧ (32 : ℝ) / 4 < normalGen N) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧ HasExcess G 32 i ∧ 32 ≤ 32 ∧
      (i = 1 → ∀ N : Subgroup G, N.Normal → (32 : ℝ) / 4 < normalGen N → N = ⊤) ∧
      (i = 2 → 32 = 8 ∨ 32 = 16 ∨ 32 = 32) := by
  letI : MulAction.IsPretransitive G (Fin 32) := ⟨htrans⟩
  have hall (N : Subgroup G) [N.Normal] : normalGen N ≤ 10 := by
    simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two G hG N
  by_cases hten : ∃ N : Subgroup G, N.Normal ∧ normalGen N = 10
  · have hexcess : HasExcess G 32 2 := by
      constructor
      · obtain ⟨N, hN, hval⟩ := hten
        exact ⟨N, hN, by norm_num [hval]⟩
      · intro N hN
        letI := hN
        norm_num
        exact hall N
    exact ⟨2, Or.inr rfl, hexcess, by decide, by intro h; omega,
      fun _ => Or.inr (Or.inr rfl)⟩
  · have hnine (N : Subgroup G) [N.Normal] : normalGen N ≤ 9 := by
      have hb := hall N
      have hne : normalGen N ≠ 10 := fun he => hten ⟨N, inferInstance, he⟩
      omega
    have hexcess : HasExcess G 32 1 := by
      constructor
      · obtain ⟨N, hN, hval⟩ := hhigh
        letI := hN
        have hb := hnine N
        norm_num at hval
        have heq : normalGen N = 9 := by omega
        exact ⟨N, hN, by norm_num [heq]⟩
      · intro N hN
        letI := hN
        norm_num
        exact hnine N
    refine ⟨1, Or.inl rfl, hexcess, by decide, ?_, fun _ => Or.inr (Or.inr rfl)⟩
    intro _ N hN hval
    letI := hN
    exact only_whole_of_excess_one G hG htrans hexcess N hval

end SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessProfile

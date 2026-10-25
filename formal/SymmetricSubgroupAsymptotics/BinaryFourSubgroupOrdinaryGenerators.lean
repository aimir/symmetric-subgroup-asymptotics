import SymmetricSubgroupAsymptotics.BinaryFourSylowOrderFour
import SymmetricSubgroupAsymptotics.BinaryFourSubgroupArithmetic
import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGeneratorSaving

/-! Every actual subgroup of binary GL4 needs at most seven ordinary
generators. Proper subgroups use faithful coset actions, exact order
multiplicity, and the actual unitriangular order-four argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourSubgroupOrdinaryGenerators
open BinaryFourLinearGroups

/-- Simplicity supplies the actual faithful coset action, not a catalogue. -/
theorem eight_le_index (H : Subgroup General) (hH : H ≠ ⊤) : 8 ≤ H.index := by
  letI : IsSimpleGroup General := simple_GL
  letI : Fintype (General ⧸ H) := Fintype.ofFinite _
  have hd := Subgroup.card_dvd_of_injective (MulAction.toPermHom General (General ⧸ H))
    (PrimitiveSocleRawStructure.simple_cosetAction_injective H hH)
  have hperm : Nat.card (Equiv.Perm (General ⧸ H)) = H.index.factorial := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,
      ←H.index_eq_card]
  rw [card_GL,hperm] at hd
  have hle : 20160 ≤ H.index.factorial := Nat.le_of_dvd (Nat.factorial_pos _) hd
  by_contra hn
  have hlt := BinaryFourSubgroupArithmetic.factorial_lt (show H.index < 8 by omega)
  omega

theorem genRank_le_seven (H : Subgroup General) : MarkedC4.genRank H ≤ 7 := by
  by_cases hH : H = ⊤
  · subst H
    have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (Subgroup.topEquiv : (⊤ : Subgroup General) ≃* General)
    exact he.le.trans (genRank_GL_le_two.trans (by decide))
  have hmul : Nat.card H * H.index = 20160 := H.card_mul_index.trans card_GL
  obtain ⟨hbudget,hcases⟩ := BinaryFourSubgroupArithmetic.budget hmul (eight_le_index H hH)
  rcases hcases with hsmall | h32
  · exact (FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors H).trans hsmall
  · obtain ⟨g,hg⟩ := BinaryFourSylowOrderFour.exists_order_four H h32
    have hsave := FiniteGroupPrimeMultiplicityGeneratorSaving.genRank_add_one_le_of_order_four g hg
    omega

/-- The ordinary rank conclusion retains any original faithfully embedded group. -/
theorem genRank_le_seven_of_injective {G : Type} [Group G] [Finite G]
    (f : G →* General) (hf : Function.Injective f) : MarkedC4.genRank G ≤ 7 := by
  have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (MonoidHom.ofInjective hf : G ≃* f.range)
  exact he.le.trans (genRank_le_seven f.range)

theorem exists_generating_finset (H : Subgroup General) :
    ∃ S : Finset H, Subgroup.closure (S : Set H) = ⊤ ∧ S.card ≤ 7 := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := H)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_seven H)⟩

end SymmetricSubgroupAsymptotics.BinaryFourSubgroupOrdinaryGenerators

import SymmetricSubgroupAsymptotics.DerivedOneCosetOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import Mathlib.Data.Fin.VecNotation

/-! Seven ordinary generators of the original binary derived fixed group
and its FULL central quotient defining Tits. The three actual derived
elements x,wo,wm and the remaining original y generate the full fixed
group, while y² is derived. The generic literal Schreier family gives7.
No outer-automorphism bound, global Tracey bound, model order, simplicity,
index table or assumed two-generation enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTitsSevenOrdinaryGenerators
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOuterThreeWord
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourBinaryDerivedGeneration CFSGReeFFourBinaryOuterSaving
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourOriginalPositiveSylow
private abbrev D := commutator (originalModelFixed 0)

private def g : Fin 3 → D := ![
  ⟨outerInvolution 0, outer_mem_derived 0⟩,
  ⟨outerFixedWeyl 0, outer_weyl_mem_derived 0 (outer_mem_derived 0)⟩,
  ⟨middleFixedWeyl 0, middle_weyl_mem_derived 0⟩]

private theorem original_generated :
    Subgroup.closure (Set.range (fun i => (g i : originalModelFixed 0)) ∪ {fourCycle 0}) = ⊤ := by
  apply subgroup_eq_top_of_four_generators
  · exact Subgroup.subset_closure (Or.inl ⟨0, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr rfl)
  · exact Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨2, rfl⟩)

theorem exists_derived_generating_finset :
    ∃ T : Finset D, Subgroup.closure (T : Set D) = ⊤ ∧ T.card ≤ 7 := by
  obtain ⟨T, hT, hcard⟩ := DerivedOneCosetOrdinaryGenerators.exists_generating_finset
    g (fourCycle 0) original_generated (square_mem_derived 0)
  exact ⟨T, hT, by simpa only [Nat.card_fin] using hcard⟩

theorem derived_genRank_le_seven : MarkedC4.genRank D ≤ 7 := by
  obtain ⟨T, hT, hcard⟩ := exists_derived_generating_finset
  exact (MarkedC4.genRank_le hT).trans hcard

/-- The image of the same finite generating family under the actual
surjection through the FULL derived-centre quotient. -/
theorem exists_tits_generating_finset :
    ∃ T : Finset CFSG.Models.Tits,
      Subgroup.closure (T : Set CFSG.Models.Tits) = ⊤ ∧ T.card ≤ 7 := by
  obtain ⟨T, hT, hcard⟩ := exists_derived_generating_finset
  refine ⟨T.image (derivedReeHom 0), ?_, Finset.card_image_le.trans hcard⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hT]
  exact Subgroup.map_top_of_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)

theorem tits_genRank_le_seven : MarkedC4.genRank CFSG.Models.Tits ≤ 7 := by
  obtain ⟨T, hT, hcard⟩ := exists_tits_generating_finset
  exact (MarkedC4.genRank_le hT).trans hcard

end SymmetricSubgroupAsymptotics.CFSGTitsSevenOrdinaryGenerators

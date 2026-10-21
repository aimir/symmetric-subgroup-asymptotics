import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow1BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow3BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow5BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow6BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow7BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow8BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow9BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow10BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow11BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow12BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow13BinaryExtension
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow2Top1Binding
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow4Top18Binding
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRow14Top19Binding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue
import Mathlib.Tactic.FinCases

/-! A literal affine row is binary, has one of three actual canonical point
charts, or contains a larger actual transitive binary subgroup. Every finite
witness module must exist and pass before this assembly can be checked. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineRowsCanonicalOrEscape
open BinaryThreeAffineRowActions
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Canonical (U : Subgroup BinaryThreeAffineRowActions.Ambient) : Prop :=
  ∃ j : Fin 24,∃ c : BinaryThreeAffineRowActions.Ambient,
    MulAut.conj c • U = DegreeEightCanonicalCatalogue.canonical j

theorem row_zero : rows 0 = translation.range := by
  simp only [rows,affine,GeneralThreeTwoActualSubgroupCoverage.rows,
    GeneralThreeTwoSubgroupRows.row_zero,Subgroup.map_bot,sup_bot_eq]

theorem complete (i : Fin 15) :
    IsPGroup 2 (rows i) ∨ Canonical (rows i) ∨
      PermutationPrimePowerSeedEscape.ContainsAbove 2 8 (rows i) := by
  fin_cases i
  · left
    change IsPGroup 2 (rows 0)
    rw [row_zero]
    exact BinaryThreeAffineBinaryExtensions.translation_isPGroup
  · exact Or.inr (Or.inr BinaryThreeAffineRow1BinaryExtension.contains_above)
  · exact Or.inr (Or.inl ⟨0,BinaryThreeAffineRow2Top1Binding.conjugator,
      BinaryThreeAffineRow2Top1Binding.canonical_conjugated⟩)
  · exact Or.inr (Or.inr BinaryThreeAffineRow3BinaryExtension.contains_above)
  · exact Or.inr (Or.inl ⟨17,BinaryThreeAffineRow4Top18Binding.conjugator,
      BinaryThreeAffineRow4Top18Binding.canonical_conjugated⟩)
  · exact Or.inr (Or.inr BinaryThreeAffineRow5BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow6BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow7BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow8BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow9BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow10BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow11BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow12BinaryExtension.contains_above)
  · exact Or.inr (Or.inr BinaryThreeAffineRow13BinaryExtension.contains_above)
  · exact Or.inr (Or.inl ⟨18,BinaryThreeAffineRow14Top19Binding.conjugator,
      BinaryThreeAffineRow14Top19Binding.canonical_conjugated⟩)

end SymmetricSubgroupAsymptotics.BinaryThreeAffineRowsCanonicalOrEscape
end

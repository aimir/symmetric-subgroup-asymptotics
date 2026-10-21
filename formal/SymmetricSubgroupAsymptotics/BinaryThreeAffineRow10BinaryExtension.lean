import SymmetricSubgroupAsymptotics.BinaryThreeAffineBinaryExtensions
import SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord

/-! One actual involution word in a fixed linear row, retaining the literal
point action. No row-order metadata occurs in this proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineRow10BinaryExtension
open BinaryThreeAffineRowActions

def witnessWord : FiniteGeneratorWord (Fin 3) := (.generator 0)
def element : Linear := witnessWord.eval (GeneralThreeTwoRowGenerators.generators 10)

theorem element_mem : element ∈ GeneralThreeTwoActualSubgroupCoverage.rows 10 := by
  rw [GeneralThreeTwoRowGenerators.rows_eq_closure]
  exact witnessWord.eval_mem_closure (GeneralThreeTwoRowGenerators.generators 10)

theorem element_square : element ^ 2 = 1 := by
  apply GeneralThreeTwoPointAction.action_injective
  rw [map_pow,map_one]
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem element_ne_one : element ≠ 1 := by
  have hm : linear element (1 : Fin 8) ≠ (1 : Fin 8) := by decide +kernel
  intro he
  apply hm
  exact Equiv.congr_fun ((congrArg linear he).trans linear.map_one) (1 : Fin 8)

theorem contains_above : PermutationPrimePowerSeedEscape.ContainsAbove 2 8 (rows 10) :=
  BinaryThreeAffineBinaryExtensions.contains_above _ element element_mem 1
    element_square element_ne_one

end SymmetricSubgroupAsymptotics.BinaryThreeAffineRow10BinaryExtension
end

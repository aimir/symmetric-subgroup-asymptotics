import SymmetricSubgroupAsymptotics.BinaryEightTop30NaturalComplete
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicPilot
import SymmetricSubgroupAsymptotics.BinaryEightTop30K45Head
import SymmetricSubgroupAsymptotics.BinaryEightTop30K29Head
import SymmetricSubgroupAsymptotics.BinaryEightTop30K37Head
import SymmetricSubgroupAsymptotics.BinaryEightTop30K9Head
import SymmetricSubgroupAsymptotics.BinaryEightTop30K44Head
import SymmetricSubgroupAsymptotics.BinaryEightTop30K20Head
import SymmetricSubgroupAsymptotics.BinaryEightTop30K23Head

/-! Every actual natural submodule for the literal30 action has at most
one coinvariant generator, including the zero/full correlated kernels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30NaturalHead
open BinaryEightTop30CoordinateAction BinaryEightTop30NineStates

theorem head_le_one (W : Subrepresentation rho) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  obtain ⟨i,rfl⟩ := BinaryEightTop30NaturalComplete.complete W
  fin_cases i
  · apply representationCoinvariants_finrank_le_of_displacementSpan rho generators (states 0) 1
    have hz : Module.finrank (ZMod 2) (states 0).toSubmodule = 0 := by
      change Module.finrank (ZMod 2) BinaryRegularEightNaturalRegistry.chart0.space = 0
      exact BinaryRegularEightNaturalRegistry.chart0.finrank
    rw [hz]
    omega
  · exact BinaryEightTop30CyclicPilot.head_le_one _ rfl
  · exact BinaryEightTop30K45Head.head_le_one _ rfl
  · exact BinaryEightTop30K29Head.head_le_one _ rfl
  · exact BinaryEightTop30K37Head.head_le_one _ rfl
  · exact BinaryEightTop30K9Head.head_le_one _ rfl
  · exact BinaryEightTop30K44Head.head_le_one _ rfl
  · exact BinaryEightTop30K20Head.head_le_one _ rfl
  · exact BinaryEightTop30K23Head.head_le_one _ rfl
end SymmetricSubgroupAsymptotics.BinaryEightTop30NaturalHead

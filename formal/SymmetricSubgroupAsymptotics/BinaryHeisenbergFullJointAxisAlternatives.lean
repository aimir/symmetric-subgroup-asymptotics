import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis1
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis2
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis4
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis5
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis12
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis13
import SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis14

/-! Every actual invariant axis is either one of the two proper-F axes or
has the joint whole-quotient envelope. The fixed fifteen-state registry
supplies exhaustive coverage with the original axis unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFullJointAxisAlternatives
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart0 chart1 chart23 chart45)

theorem all_axes (A : Subrepresentation rho) :
    A.toSubmodule = chart0.space ∨ A.toSubmodule = chart23.space ∨
      JointAxisEnvelope chart1.space chart45.space A.toSubmodule 128 := by
  obtain ⟨i,rfl⟩ := complete A
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis1.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis2.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis3.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis4.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis5.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis6.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis7.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis8.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis9.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis10.coordinate_envelope)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis12.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis13.coordinate_envelope)
  · exact Or.inr (Or.inr BinaryHeisenberg1FixedAxis14.coordinate_envelope)

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFullJointAxisAlternatives

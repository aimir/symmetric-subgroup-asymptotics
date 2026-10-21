import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis2
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis4
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis5
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis12
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis13
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K12 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg12AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart45 chart33)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart45.space) :
    JointAxisEnvelope chart45.space chart33.space A.toSubmodule 64 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg12FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart45.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart45.space) hm)
  · exact BinaryHeisenberg12FixedAxis2.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis3.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis4.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis5.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis6.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis7.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis8.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis11.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis12.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis13.coordinate_envelope
  · exact BinaryHeisenberg12FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg12AllJointAxes

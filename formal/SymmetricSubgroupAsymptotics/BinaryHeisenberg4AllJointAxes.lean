import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis4
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis13
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K4 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg4AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart31 chart33)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart31.space) :
    JointAxisEnvelope chart31.space chart33.space A.toSubmodule 32 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg4FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart31.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart31.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart31.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart31.space) hm)
  · exact BinaryHeisenberg4FixedAxis3.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis4.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart31.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart31.space) hm)
  · exact BinaryHeisenberg4FixedAxis6.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis7.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis8.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart31.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart31.space) hm)
  · exact BinaryHeisenberg4FixedAxis13.coordinate_envelope
  · exact BinaryHeisenberg4FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg4AllJointAxes

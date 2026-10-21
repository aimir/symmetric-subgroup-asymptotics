import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K8 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg8AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart46 chart40)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart46.space) :
    JointAxisEnvelope chart46.space chart40.space A.toSubmodule 8 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg8FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart4.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart4.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart4.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart4.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · exact BinaryHeisenberg8FixedAxis6.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart15.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart15.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart15.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart15.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart46.space) hm)
  · exact BinaryHeisenberg8FixedAxis8.coordinate_envelope
  · exact BinaryHeisenberg8FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg8FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg8FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart33.space ≤ chart46.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart33.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart46.space) hm)
  · exact BinaryHeisenberg8FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg8AllJointAxes

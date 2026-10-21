import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K3 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg3AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart4 chart40)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart4.space) :
    JointAxisEnvelope chart4.space chart40.space A.toSubmodule 8 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg3FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart4.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · exact BinaryHeisenberg3FixedAxis3.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · exact BinaryHeisenberg3FixedAxis6.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart15.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart15.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart15.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart15.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart46.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart46.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart46.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart46.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · exact BinaryHeisenberg3FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg3FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg3FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart33.space ≤ chart4.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart33.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart4.space) hm)
  · exact BinaryHeisenberg3FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg3AllJointAxes

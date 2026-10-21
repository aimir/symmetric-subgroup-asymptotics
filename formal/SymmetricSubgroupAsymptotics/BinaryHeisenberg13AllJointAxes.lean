import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis13
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K13 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg13AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart33 chart40)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart33.space) :
    JointAxisEnvelope chart33.space chart40.space A.toSubmodule 16 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg13FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart33.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart33.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart33.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart33.space) hm)
  · exact BinaryHeisenberg13FixedAxis3.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart33.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart33.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart33.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart33.space) hm)
  · exact BinaryHeisenberg13FixedAxis6.coordinate_envelope
  · exact BinaryHeisenberg13FixedAxis7.coordinate_envelope
  · exact BinaryHeisenberg13FixedAxis8.coordinate_envelope
  · exact BinaryHeisenberg13FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg13FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg13FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart33.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart33.space) hm)
  · exact BinaryHeisenberg13FixedAxis13.coordinate_envelope
  · exact BinaryHeisenberg13FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg13AllJointAxes

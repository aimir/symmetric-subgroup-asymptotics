import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K7 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg7AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart15 chart40)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart15.space) :
    JointAxisEnvelope chart15.space chart40.space A.toSubmodule 8 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg7FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart4.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart4.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart4.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart4.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · exact BinaryHeisenberg7FixedAxis6.coordinate_envelope
  · exact BinaryHeisenberg7FixedAxis7.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart46.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart46.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart46.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart46.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart15.space) hm)
  · exact BinaryHeisenberg7FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg7FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg7FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart33.space ≤ chart15.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart33.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart15.space) hm)
  · exact BinaryHeisenberg7FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg7AllJointAxes

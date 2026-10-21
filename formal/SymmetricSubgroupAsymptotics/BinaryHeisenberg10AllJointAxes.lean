import SymmetricSubgroupAsymptotics.BinaryHeisenberg10FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg10FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg10FixedAxis11

/-! All original invariant axes inside the actual Heisenberg K10 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg10AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart22 chart23)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart22.space) :
    JointAxisEnvelope chart22.space chart23.space A.toSubmodule 2 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg10FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart4.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart4.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart4.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart4.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart13.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart13.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart13.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart13.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart15.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart15.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart15.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart15.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart46.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart46.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart46.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart46.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart21.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart21.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart21.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart21.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · exact BinaryHeisenberg10FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg10FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart33.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart33.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart33.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart22.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart40.space ≤ chart22.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart40.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart40.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart40.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart22.space) hm)

end SymmetricSubgroupAsymptotics.BinaryHeisenberg10AllJointAxes

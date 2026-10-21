import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis2
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis13
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K2 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg2AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart24 chart33)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart24.space) :
    JointAxisEnvelope chart24.space chart33.space A.toSubmodule 32 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg2FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart24.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart24.space) hm)
  · exact BinaryHeisenberg2FixedAxis2.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis3.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart24.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart24.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart32.space ≤ chart24.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart32.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart32.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart24.space) hm)
  · exact BinaryHeisenberg2FixedAxis6.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis7.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis8.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart24.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart24.space) hm)
  · exact BinaryHeisenberg2FixedAxis13.coordinate_envelope
  · exact BinaryHeisenberg2FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg2AllJointAxes

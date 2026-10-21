import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis5
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis6
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis7
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis8
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis9
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis10
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis11
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis13
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5FixedAxis14

/-! All original invariant axes inside the actual Heisenberg K5 kernel.
The existing complete fifteen-state registry supplies coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg5AllJointAxes
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate
open BinaryRegularEightNaturalRegistry (chart32 chart33)
theorem all_axes (A : Subrepresentation rho) (hA : A.toSubmodule ≤ chart32.space) :
    JointAxisEnvelope chart32.space chart33.space A.toSubmodule 32 := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryHeisenberg5FixedAxis0.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart1.space ≤ chart32.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart1.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart1.inclusion
      (Pi.single ⟨0, by decide⟩ 1) ∈ chart32.space) hm)
  · change BinaryRegularEightNaturalRegistry.chart24.space ≤ chart32.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart24.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart24.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart32.space) hm)
  · exact BinaryHeisenberg5FixedAxis3.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart31.space ≤ chart32.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart31.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart31.inclusion
      (Pi.single ⟨1, by decide⟩ 1) ∈ chart32.space) hm)
  · exact BinaryHeisenberg5FixedAxis5.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis6.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis7.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis8.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis9.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis10.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis11.coordinate_envelope
  · change BinaryRegularEightNaturalRegistry.chart45.space ≤ chart32.space at hA
    have hm := hA (show BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨3, by decide⟩ 1) ∈ BinaryRegularEightNaturalRegistry.chart45.space from ⟨_, rfl⟩)
    exact False.elim ((by decide +kernel : ¬ BinaryRegularEightNaturalRegistry.chart45.inclusion
      (Pi.single ⟨3, by decide⟩ 1) ∈ chart32.space) hm)
  · exact BinaryHeisenberg5FixedAxis13.coordinate_envelope
  · exact BinaryHeisenberg5FixedAxis14.coordinate_envelope

end SymmetricSubgroupAsymptotics.BinaryHeisenberg5AllJointAxes

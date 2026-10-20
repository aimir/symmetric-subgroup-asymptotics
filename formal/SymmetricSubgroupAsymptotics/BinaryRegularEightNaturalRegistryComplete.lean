import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCyclic
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryJoin0
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryJoin12
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryJoin24
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryJoin36

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

private theorem all_child_eq (i : Fin 47) (c : Fin 24) :
  (states (child i c)).toSubmodule =
    (states i).toSubmodule ⊔ binaryOrbitSpan rho (representative c) := by
  by_cases h0 : i.val < 12
  · have he : Join0.embed ⟨i.val - 0, by omega⟩ = i := by
      apply Fin.ext
      simp only [Join0.embed]
      omega
    simpa only [he] using Join0.child_eq ⟨i.val - 0, by omega⟩ c
  by_cases h12 : i.val < 24
  · have he : Join12.embed ⟨i.val - 12, by omega⟩ = i := by
      apply Fin.ext
      simp only [Join12.embed]
      omega
    simpa only [he] using Join12.child_eq ⟨i.val - 12, by omega⟩ c
  by_cases h24 : i.val < 36
  · have he : Join24.embed ⟨i.val - 24, by omega⟩ = i := by
      apply Fin.ext
      simp only [Join24.embed]
      omega
    simpa only [he] using Join24.child_eq ⟨i.val - 24, by omega⟩ c
  have he : Join36.embed ⟨i.val - 36, by omega⟩ = i := by
    apply Fin.ext
    simp only [Join36.embed]
    omega
  simpa only [he] using Join36.child_eq ⟨i.val - 36, by omega⟩ c
def certificate : BinaryInvariantRepresentativeRegistry (C := Fin 24) rho states where
  representative := representative
  pointClass := pointClass
  point_span := point_representative_span
  bottom := 0
  bottom_eq := bottom_space
  child := child
  child_eq := all_child_eq
theorem complete (W : Subrepresentation rho) : ∃ i, states i = W := certificate.complete W

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

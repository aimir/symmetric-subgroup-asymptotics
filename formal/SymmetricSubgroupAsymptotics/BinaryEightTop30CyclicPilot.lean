import SymmetricSubgroupAsymptotics.BinaryEightTop30NineStates
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate

/-! ONE actual8T30 point-orbit and head pilot. Each displayed basis
relation is checked on eight original coordinates by Lean's kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicPilot
open BinaryEightTop30CoordinateAction BinaryEightTop30NineStates
open BinaryRegularEightNaturalRegistry (chart1 chart45)
def orbitWords : Fin 8 → List (List (Fin 3)) := ![[[2,1]],[[0,1]],[[0,2]],[[1,0,1]],[[2,0,1]],[[1]],[[2]],[[]]]
private theorem orbit_basis : ∀ j : Fin 8,
    chart1.inclusion (Pi.single j 1) =
      ((orbitWords j).map (fun w => rho (word w) (binaryVectorOfMask 8 1))).sum := by
  decide +kernel
theorem full_space_cyclic : chart1.space = binaryOrbitSpan rho (binaryVectorOfMask 8 1) := by
  apply le_antisymm
  · apply chart1.le_of_basis_mem
    intro j
    rw [orbit_basis]
    apply (binaryOrbitSpan rho (binaryVectorOfMask 8 1)).list_sum_mem
    intro x hx
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
    exact Submodule.subset_span ⟨word w,rfl⟩
  · exact binaryOrbitSpan_le rho (states 1) (by
      change binaryVectorOfMask 8 1 ∈ chart1.space
      decide +kernel)
def coefficients : Fin 7 → Fin 3 → ℕ := ![![0,0,1],![2,32,0],![2,32,4],![2,34,0],![0,1,1],![0,32,0],![6,32,4]]
private theorem radical_mem : ∀ j : Fin 7,
    chart45.inclusion (Pi.single j 1) ∈ chart1.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 7,
    chart45.inclusion (Pi.single j 1) =
      ∑ t : Fin 3, (rho (generators t)
        (chart1.inclusion (binaryVectorOfMask 8 (coefficients j t))) -
        chart1.inclusion (binaryVectorOfMask 8 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho) (hW : W.toSubmodule = chart1.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart45.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart45.le_of_basis_mem _ radical_mem
  let term (j : Fin 7) (t : Fin 3) : W.toSubmodule :=
    ⟨chart1.inclusion (binaryVectorOfMask 8 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart45 := {
    space_le_state := hC
    termCount _ := 3
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart1.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicPilot

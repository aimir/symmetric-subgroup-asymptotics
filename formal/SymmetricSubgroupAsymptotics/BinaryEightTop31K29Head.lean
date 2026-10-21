import SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate

/-! ONE selected larger-top head certificate. The actual invariant W
may come from any original source; only its literal coordinate space is
identified. All displayed relations are genuine original8T31 displacements. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31K29Head
open BinaryEightTop31CoordinateAction
open BinaryRegularEightNaturalRegistry (chart29 chart37)

def coefficients : Fin 5 → Fin 3 → ℕ := ![![0,1,0],![1,8,2],![1,11,2],![1,8,0],![1,1,0]]
private theorem radical_mem : ∀ j : Fin 5,
    chart37.inclusion (Pi.single j 1) ∈ chart29.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 5,
    chart37.inclusion (Pi.single j 1) =
      ∑ t : Fin 3, (rho (generators t)
        (chart29.inclusion (binaryVectorOfMask 6 (coefficients j t))) -
        chart29.inclusion (binaryVectorOfMask 6 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart29.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart37.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart37.le_of_basis_mem _ radical_mem
  let term (j : Fin 5) (t : Fin 3) : W.toSubmodule :=
    ⟨chart29.inclusion (binaryVectorOfMask 6 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart37 := {
    space_le_state := hC
    termCount _ := 3
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart29.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop31K29Head

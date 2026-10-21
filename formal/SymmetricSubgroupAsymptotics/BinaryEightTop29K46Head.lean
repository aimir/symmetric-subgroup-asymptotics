import SymmetricSubgroupAsymptotics.BinaryEightTop29CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate

/-! ONE selected larger-top head certificate. The actual invariant W
may come from any original source; only its literal coordinate space is
identified. All displayed relations are genuine original8T29 displacements. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29K46Head
open BinaryEightTop29CoordinateAction
open BinaryRegularEightNaturalRegistry (chart46 chart42)

def coefficients : Fin 3 → Fin 5 → ℕ := ![![2,0,0,4,0],![0,0,0,2,0],![0,0,0,6,0]]
private theorem radical_mem : ∀ j : Fin 3,
    chart42.inclusion (Pi.single j 1) ∈ chart46.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 3,
    chart42.inclusion (Pi.single j 1) =
      ∑ t : Fin 5, (rho (generators t)
        (chart46.inclusion (binaryVectorOfMask 4 (coefficients j t))) -
        chart46.inclusion (binaryVectorOfMask 4 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart46.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart42.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart42.le_of_basis_mem _ radical_mem
  let term (j : Fin 3) (t : Fin 5) : W.toSubmodule :=
    ⟨chart46.inclusion (binaryVectorOfMask 4 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart42 := {
    space_le_state := hC
    termCount _ := 5
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart46.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop29K46Head

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
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29K24Head
open BinaryEightTop29CoordinateAction
open BinaryRegularEightNaturalRegistry (chart24 chart30)

def coefficients : Fin 5 → Fin 5 → ℕ := ![![16,0,0,1,0],![16,0,2,0,0],![2,0,3,1,0],![16,0,1,1,0],![0,0,0,1,0]]
private theorem radical_mem : ∀ j : Fin 5,
    chart30.inclusion (Pi.single j 1) ∈ chart24.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 5,
    chart30.inclusion (Pi.single j 1) =
      ∑ t : Fin 5, (rho (generators t)
        (chart24.inclusion (binaryVectorOfMask 6 (coefficients j t))) -
        chart24.inclusion (binaryVectorOfMask 6 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart24.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart30.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart30.le_of_basis_mem _ radical_mem
  let term (j : Fin 5) (t : Fin 5) : W.toSubmodule :=
    ⟨chart24.inclusion (binaryVectorOfMask 6 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart30 := {
    space_le_state := hC
    termCount _ := 5
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart24.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop29K24Head

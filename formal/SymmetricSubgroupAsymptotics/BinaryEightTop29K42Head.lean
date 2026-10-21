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
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29K42Head
open BinaryEightTop29CoordinateAction
open BinaryRegularEightNaturalRegistry (chart42 chart22)

def coefficients : Fin 2 → Fin 5 → ℕ := ![![2,0,0,2,0],![0,0,0,2,0]]
private theorem radical_mem : ∀ j : Fin 2,
    chart22.inclusion (Pi.single j 1) ∈ chart42.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 2,
    chart22.inclusion (Pi.single j 1) =
      ∑ t : Fin 5, (rho (generators t)
        (chart42.inclusion (binaryVectorOfMask 3 (coefficients j t))) -
        chart42.inclusion (binaryVectorOfMask 3 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart42.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart22.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart22.le_of_basis_mem _ radical_mem
  let term (j : Fin 2) (t : Fin 5) : W.toSubmodule :=
    ⟨chart42.inclusion (binaryVectorOfMask 3 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart22 := {
    space_le_state := hC
    termCount _ := 5
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart42.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop29K42Head

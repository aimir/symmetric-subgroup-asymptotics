import SymmetricSubgroupAsymptotics.BinaryEightTop30CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate

/-! ONE selected larger-top head certificate. The actual invariant W
may come from any original source; only its literal coordinate space is
identified. All displayed relations are genuine original8T30 displacements. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30K20Head
open BinaryEightTop30CoordinateAction
open BinaryRegularEightNaturalRegistry (chart20 chart23)

def coefficients : Fin 1 → Fin 3 → ℕ := ![![0,0,1]]
private theorem radical_mem : ∀ j : Fin 1,
    chart23.inclusion (Pi.single j 1) ∈ chart20.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 1,
    chart23.inclusion (Pi.single j 1) =
      ∑ t : Fin 3, (rho (generators t)
        (chart20.inclusion (binaryVectorOfMask 2 (coefficients j t))) -
        chart20.inclusion (binaryVectorOfMask 2 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart20.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart23.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart23.le_of_basis_mem _ radical_mem
  let term (j : Fin 1) (t : Fin 3) : W.toSubmodule :=
    ⟨chart20.inclusion (binaryVectorOfMask 2 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart23 := {
    space_le_state := hC
    termCount _ := 3
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart20.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop30K20Head

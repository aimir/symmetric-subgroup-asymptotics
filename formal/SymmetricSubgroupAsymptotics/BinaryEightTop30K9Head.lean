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
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30K9Head
open BinaryEightTop30CoordinateAction
open BinaryRegularEightNaturalRegistry (chart9 chart44)

def coefficients : Fin 3 → Fin 3 → ℕ := ![![0,0,1],![0,2,0],![0,2,4]]
private theorem radical_mem : ∀ j : Fin 3,
    chart44.inclusion (Pi.single j 1) ∈ chart9.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 3,
    chart44.inclusion (Pi.single j 1) =
      ∑ t : Fin 3, (rho (generators t)
        (chart9.inclusion (binaryVectorOfMask 4 (coefficients j t))) -
        chart9.inclusion (binaryVectorOfMask 4 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart9.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart44.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart44.le_of_basis_mem _ radical_mem
  let term (j : Fin 3) (t : Fin 3) : W.toSubmodule :=
    ⟨chart9.inclusion (binaryVectorOfMask 4 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart44 := {
    space_le_state := hC
    termCount _ := 3
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart9.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop30K9Head

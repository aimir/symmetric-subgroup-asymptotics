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
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30K44Head
open BinaryEightTop30CoordinateAction
open BinaryRegularEightNaturalRegistry (chart44 chart20)

def coefficients : Fin 2 → Fin 3 → ℕ := ![![0,0,1],![0,1,0]]
private theorem radical_mem : ∀ j : Fin 2,
    chart20.inclusion (Pi.single j 1) ∈ chart44.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 2,
    chart20.inclusion (Pi.single j 1) =
      ∑ t : Fin 3, (rho (generators t)
        (chart44.inclusion (binaryVectorOfMask 3 (coefficients j t))) -
        chart44.inclusion (binaryVectorOfMask 3 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart44.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart20.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart20.le_of_basis_mem _ radical_mem
  let term (j : Fin 2) (t : Fin 3) : W.toSubmodule :=
    ⟨chart44.inclusion (binaryVectorOfMask 3 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart20 := {
    space_le_state := hC
    termCount _ := 3
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart44.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop30K44Head

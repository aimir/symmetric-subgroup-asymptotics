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
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30K45Head
open BinaryEightTop30CoordinateAction
open BinaryRegularEightNaturalRegistry (chart45 chart29)

def coefficients : Fin 6 → Fin 3 → ℕ := ![![0,0,1],![2,4,0],![4,0,0],![2,2,0],![0,5,1],![0,4,0]]
private theorem radical_mem : ∀ j : Fin 6,
    chart29.inclusion (Pi.single j 1) ∈ chart45.space := by decide +kernel
private theorem radical_eq : ∀ j : Fin 6,
    chart29.inclusion (Pi.single j 1) =
      ∑ t : Fin 3, (rho (generators t)
        (chart45.inclusion (binaryVectorOfMask 7 (coefficients j t))) -
        chart45.inclusion (binaryVectorOfMask 7 (coefficients j t))) := by decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = chart45.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  have hC : chart29.space ≤ W.toSubmodule := by
    rw [hW]
    exact chart29.le_of_basis_mem _ radical_mem
  let term (j : Fin 6) (t : Fin 3) : W.toSubmodule :=
    ⟨chart45.inclusion (binaryVectorOfMask 7 (coefficients j t)), by
      rw [hW]
      exact ⟨_,rfl⟩⟩
  let D : BinaryCoordinateDisplacementCertificate rho generators W chart29 := {
    space_le_state := hC
    termCount _ := 3
    termGenerator _ t := t
    termVector := term
    basis_eq j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using radical_eq j }
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators W D.submodule 1 D.le_generatorDisplacementSpan
  rw [D.finrank,hW,chart45.finrank]

end SymmetricSubgroupAsymptotics.BinaryEightTop30K45Head

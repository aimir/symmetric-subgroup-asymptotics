import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedA2MatrixCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalRealization

/-! The literal rational A2 Serre quotient has its original eight-vector
basis, detected by integral matrix-entry coordinates. No simplicity or
faithful-realization assumption enters this result. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSGTwistedANaturalMatrices CFSGTwistedA2MatrixCoordinates

theorem rationalNatural_P : rationalNatural 2 P = Matrix.single 0 2 1 := by
  change rationalNatural 2 ⁅E 0, E 1⁆ = _
  rw [(rationalNatural 2).map_lie]
  simp only [E, rationalNatural_E]
  simp [positive, Ring.lie_def]

theorem rationalNatural_N : rationalNatural 2 N = Matrix.single 2 0 1 := by
  change rationalNatural 2 ⁅F 1, F 0⁆ = _
  rw [(rationalNatural 2).map_lie]
  simp only [F, rationalNatural_F]
  simp [negative, positive, Ring.lie_def]

theorem rationalNatural_vectors (i : Fin 8) :
    rationalNatural 2 (vectors i) = matrixVectors ℚ i := by
  fin_cases i
  · exact rationalNatural_H 2 0
  · exact rationalNatural_H 2 1
  · exact rationalNatural_E 2 0
  · exact rationalNatural_E 2 1
  · exact rationalNatural_P
  · exact rationalNatural_F 2 0
  · exact rationalNatural_F 2 1
  · exact rationalNatural_N

def rationalCoordinates : L →ₗ[ℚ] (Fin 8 → ℚ) :=
  (matrixCoordinates ℚ).comp (rationalNatural 2).toLinearMap

theorem rationalNatural_combination (a : Fin 8 → ℚ) :
    rationalNatural 2 (rationalCombination a) = matrixCombination ℚ a := by
  change rationalNatural 2 (∑ i, a i • vectors i) = ∑ i, a i • matrixVectors ℚ i
  simp only [map_sum, map_smul, rationalNatural_vectors]

theorem coordinates_combination (a : Fin 8 → ℚ) :
    rationalCoordinates (rationalCombination a) = a := by
  change matrixCoordinates ℚ (rationalNatural 2 (rationalCombination a)) = a
  rw [rationalNatural_combination, CFSGTwistedA2MatrixCoordinates.coordinates_combination]

theorem combination_coordinates (x : L) : rationalCombination (rationalCoordinates x) = x := by
  obtain ⟨a, rfl⟩ := rationalCombination_surjective x
  rw [coordinates_combination]

def rationalBasisEquiv : L ≃ₗ[ℚ] (Fin 8 → ℚ) where
  __ := rationalCoordinates
  invFun := rationalCombination
  left_inv := combination_coordinates
  right_inv := coordinates_combination

theorem rationalNatural_injective : Function.Injective (rationalNatural 2) := by
  intro x y h
  apply rationalBasisEquiv.injective
  exact congrArg (matrixCoordinates ℚ) h

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations

import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Complete rational D Cartan reconstruction, with no inverse determinant
or model recognition. The actual column left inverse makes the square
finite-dimensional map injective and hence surjective. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanReconstruction
open CFSGOrthogonalDSerreMatrices
variable (r : ℕ) (hr : 4 ≤ r)

def columns : (Fin r→ℚ)→ₗ[ℚ](Fin r→ℚ) :=
  Fintype.linearCombination ℚ (fun i k=>cartan ℚ r i (.inl k) (.inl k))

theorem coordinates_columns (a : Fin r→ℚ) :
    CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr (columns r a)=a := by
  change CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
    (Fintype.linearCombination ℚ (fun i k=>cartan ℚ r i (.inl k) (.inl k)) a)=a
  rw [Fintype.linearCombination_apply]
  simp only [map_sum,map_smul,CFSGOrthogonalDRationalCartanCoordinates.coordinates_cartan]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

include hr in
theorem columns_surjective : Function.Surjective (columns r) := by
  apply LinearMap.injective_iff_surjective.mp
  exact (show Function.LeftInverse
    (CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr) (columns r) from
      coordinates_columns r hr).injective

theorem reconstruction (a : Fin r→ℚ) :
    columns r (CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr a)=a := by
  obtain ⟨b,rfl⟩:=columns_surjective r hr a
  rw [coordinates_columns]

theorem coordinates_injective :
    Function.Injective (CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr) := by
  intro a b h
  rw [←reconstruction r hr a,←reconstruction r hr b,h]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanReconstruction

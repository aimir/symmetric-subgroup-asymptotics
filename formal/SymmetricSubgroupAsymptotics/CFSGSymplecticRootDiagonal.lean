import SymmetricSubgroupAsymptotics.CFSGSymplecticIntegralOperators
import SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveSupport

/-! The actual standard symplectic simple-root matrices have zero
diagonal in every characteristic. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem positive_diagonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) (x : Index r) :
    positive R r i x x = 0 := by
  cases x with
  | inl a => exact positive_left_below R r i a a le_rfl
  | inr a => exact positive_right_above R r i a a le_rfl

theorem rootMatrix_diagonal (R : Type*) [CommRing R] (r : ℕ)
    (neg : Bool) (i : Fin r) (x : Index r) : rootMatrix R r neg i x x = 0 := by
  cases neg
  · exact positive_diagonal R r i x
  · change (positive R r i).transpose x x = 0
    exact positive_diagonal R r i x

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

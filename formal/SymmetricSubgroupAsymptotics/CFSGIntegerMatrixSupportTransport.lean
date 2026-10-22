import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
import Mathlib.Data.Rat.Cast.CharZero

/-! Literal matrix support proved after rational casting descends to the
integer matrix and hence to every coefficient ring. The grading set is
unchanged; no separation by coefficient-field eigenvalues is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixSupportTransport
open CFSGGradedMatrixSupport
variable {I W : Type*} [Fintype I] [DecidableEq I]

theorem integer_support (weight : I→W) (f : W→W) (M : Matrix I I ℤ)
    (hM : Supported weight f ((Int.castRingHom ℚ).mapMatrix M)) :
    Supported weight f M := by
  intro i j hij
  have hz : (M i j:ℚ)=0 := hM i j hij
  exact (Int.cast_injective (α:=ℚ)) (by simpa only [Int.cast_zero] using hz)

theorem map_support (weight : I→W) (f : W→W) (M : Matrix I I ℤ)
    (hM : Supported weight f ((Int.castRingHom ℚ).mapMatrix M))
    (K : Type*) [CommRing K] : Supported weight f ((Int.castRingHom K).mapMatrix M) := by
  intro i j hij
  change (M i j:K)=0
  rw [integer_support weight f M hM i j hij,Int.cast_zero]

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixSupportTransport

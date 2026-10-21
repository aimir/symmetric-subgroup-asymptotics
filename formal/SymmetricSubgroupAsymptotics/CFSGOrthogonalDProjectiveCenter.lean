import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveSupport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroProjectiveCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDImageRealization

/-! The actual natural D elementary central quotient is centre-free,
using the shared square-zero scalar ambiguity theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

theorem positive_diagonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) (x : Index r) :
    positive R r i x x=0 := by
  rcases x with a | a
  · exact positive_left_below R r i a a le_rfl
  · exact positive_right_above R r i a a le_rfl

theorem negative_diagonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) (x : Index r) :
    negative R r i x x=0 := positive_diagonal R r i x

theorem rootMatrix_diagonal (R : Type*) [CommRing R] (r : ℕ)
    (neg : Bool) (i : Fin r) (x : Index r) : rootMatrix R r neg i x x=0 := by
  cases neg
  · exact positive_diagonal R r i x
  · exact negative_diagonal R r i x

theorem elementaryProjective_center_eq_bot (K : Type) [Field K] (r : ℕ) :
    Subgroup.center (elementaryProjective K (r+4))=⊥ := by
  let D := realizationData (r+4) (by omega)
  let j0 : Index (r+4) := Sum.inl ⟨0,by omega⟩
  have hd : ∀neg i,CFSGSerreSquareZeroMatrix.fieldRoot D K neg i j0 j0=0 := by
    intro neg i
    rw [realizationData_fieldRoot]
    exact rootMatrix_diagonal K (r+4) neg i j0
  exact CFSGSerreSquareZeroMatrix.elementaryProjective_center_eq_bot D K (rootTransvection K (r+4))
    (rootTransvection_val_data K (r+4) (by omega))
    (rootTransvection_inv_val_data K (r+4) (by omega))
    (elementaryRootGroup_center_iff_scalar K (r+2)) j0 hd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularSoluble

/-! The actual C Borel is soluble, by its faithful SAME coordinate
upper-triangular representation. No order formula or model-recognition
hypothesis enters this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

 def borelFlagRepresentation (K : Type) [Field K] (n : ℕ) :
    borel K n →* Matrix (Fin (n + n)) (Fin (n + n)) K :=
  (Matrix.reindexAlgEquiv K K (flagEquiv n)).toMonoidHom.comp
    ((Units.coeHom (Mat K n)).comp ((elementaryRootGroup K n).subtype.comp (borel K n).subtype))

theorem borelFlagRepresentation_injective (K : Type) [Field K] (n : ℕ) :
    Function.Injective (borelFlagRepresentation K n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.reindexAlgEquiv K K (flagEquiv n)).injective h

theorem borel_soluble (K : Type) [Field K] (n : ℕ) : IsSolvable (borel K n) := by
  apply CFSGUpperUnitriangular.soluble_of_faithful_upper_matrix K (n + n) (borel K n)
    (borelFlagRepresentation K n) (borelFlagRepresentation_injective K n)
  intro g i j hij
  change (g.val.val : Mat K n) ((flagEquiv n).symm i) ((flagEquiv n).symm j) = 0
  apply g.property
  simpa only [Equiv.apply_symm_apply] using hij

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent

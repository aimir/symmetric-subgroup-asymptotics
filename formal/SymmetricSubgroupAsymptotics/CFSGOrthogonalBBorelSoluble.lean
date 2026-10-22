import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularSoluble

/-! Solubility of the actual B Borel through its SAME faithful upper
triangular coordinates. No group-order or recognition input appears. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices

def borelFlagRepresentation (K : Type) [Field K] (n : ℕ) :
    borel K n →* Matrix (Fin (n + (1 + n))) (Fin (n + (1 + n))) K :=
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
  apply CFSGUpperUnitriangular.soluble_of_faithful_upper_matrix K (n + (1 + n)) (borel K n)
    (borelFlagRepresentation K n) (borelFlagRepresentation_injective K n)
  intro g i j hij
  change (g.val.val : Mat K n) ((flagEquiv n).symm i) ((flagEquiv n).symm j) = 0
  apply g.property
  simpa only [Equiv.apply_symm_apply] using hij

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent

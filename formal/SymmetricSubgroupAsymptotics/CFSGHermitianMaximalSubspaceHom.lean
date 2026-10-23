import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalSubspaceAction

/-! The maximal-subspace extension respects composition of the original
point permutations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem isotropic_pointSet_injective
    {S T : Submodule K (I → K)} (hS : Orthogonal sigma H S S)
    (hT : Orthogonal sigma H T T) (he : pointSet sigma H S = pointSet sigma H T) : S = T := by
  rw [← pointSpan_pointSet_eq sigma H S hS, he, pointSpan_pointSet_eq sigma H T hT]

def orthogonalityGroup : Subgroup (Equiv.Perm (SingularPoint sigma H)) where
  carrier := PreservesOrthogonality sigma H
  one_mem' := by intro P Q; rfl
  mul_mem' := by
    intro f g hf hg P Q
    exact (hf (g P) (g Q)).trans (hg P Q)
  inv_mem' := by
    intro f hf
    exact preservesOrthogonality_symm sigma H f hf

def maximalIsotropicActionHom : orthogonalityGroup sigma H →*
    Equiv.Perm {S : Submodule K (I → K) // MaximalIsotropic sigma H S} where
  toFun f := maximalIsotropicEquiv sigma H f.val f.property
  map_one' := by
    apply Equiv.ext
    intro S
    apply Subtype.ext
    apply isotropic_pointSet_injective sigma H
      (maximalIsotropicEquiv sigma H 1 (orthogonalityGroup sigma H).one_mem S).property.1 S.property.1
    change pointSet sigma H (maximalIsotropicMap sigma H 1
      (orthogonalityGroup sigma H).one_mem S).val = pointSet sigma H S.val
    rw [maximalIsotropicMap_pointSet]
    exact Set.image_id _
  map_mul' := by
    intro f g
    apply Equiv.ext
    intro S
    apply Subtype.ext
    apply isotropic_pointSet_injective sigma H
      (maximalIsotropicEquiv sigma H (f.val * g.val) _ S).property.1
      (maximalIsotropicEquiv sigma H f.val f.property
        (maximalIsotropicEquiv sigma H g.val g.property S)).property.1
    change pointSet sigma H (maximalIsotropicMap sigma H (f.val * g.val)
      ((orthogonalityGroup sigma H).mul_mem f.property g.property) S).val =
      pointSet sigma H (maximalIsotropicMap sigma H f.val f.property
        (maximalIsotropicMap sigma H g.val g.property S)).val
    rw [maximalIsotropicMap_pointSet, maximalIsotropicMap_pointSet, maximalIsotropicMap_pointSet]
    exact Set.image_image f.val g.val (pointSet sigma H S.val) |>.symm

theorem maximalIsotropicActionHom_incidence (f : orthogonalityGroup sigma H)
    (S : {S : Submodule K (I → K) // MaximalIsotropic sigma H S})
    (P : SingularPoint sigma H) :
    (f.val P).val ≤ (maximalIsotropicActionHom sigma H f S).val ↔ P.val ≤ S.val :=
  maximalIsotropicEquiv_incidence sigma H f.val f.property S P

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan

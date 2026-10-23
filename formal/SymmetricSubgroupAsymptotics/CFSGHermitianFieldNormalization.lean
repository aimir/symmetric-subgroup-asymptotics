import SymmetricSubgroupAsymptotics.CFSGHermitianFieldAction

/-! Removing the same actual common field component makes every local
representative linear on its original singular subspace. The actual
inverse field map, and the exact original point-ray equation, are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianFieldAction
open CFSGHermitianOrthogonalSpan CFSGProjectiveFieldAction
variable {K I : Type*} [Field K] [Fintype I] [Finite K]
local instance (tau : K ≃+* K) : RingHomSurjective tau.toRingHom := ⟨tau.surjective⟩
local instance (tau : K ≃+* K) : RingHomInvPair tau.toRingHom tau.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv tau
local instance (tau : K ≃+* K) : RingHomInvPair tau.symm.toRingHom tau.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm tau
variable (sigma tau : K ≃+* K) (H : Matrix I I K)
variable (f : Equiv.Perm (SingularPoint sigma H)) (S : IsotropicSpace sigma H)

def normalizedPieceMap (F : SemilinearPiece sigma H f S tau) : S.val →ₗ[K] (I → K) where
  toFun x := (coordinateEquiv tau).symm (F.map x)
  map_add' x y := by rw [F.map.map_add,map_add]
  map_smul' a x := by
    change (coordinateEquiv tau).symm (F.map (a • x)) =
      a • (coordinateEquiv tau).symm (F.map x)
    rw [F.map.map_smulₛₗ,(coordinateEquiv tau).symm.map_smulₛₗ]
    simp only [RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,RingEquiv.symm_apply_apply]

def normalizedPiece (hcomm : Function.Commute sigma tau) (hH : H.map tau = H)
    (F : SemilinearPiece sigma H f S tau) :
    SemilinearPiece sigma H (normalizedPoints sigma tau H hcomm hH f) S (RingEquiv.refl K) where
  map := normalizedPieceMap sigma tau H f S F
  injective := (coordinateEquiv tau).symm.injective.comp F.injective
  ray x hx := by
    change Submodule.span K {(coordinateEquiv tau).symm (F.map x)} =
      (f (projectiveInside sigma H S (Projectivization.mk K x hx)).val).val.comap
        (coordinateEquiv tau).toLinearMap
    rw [Submodule.comap_equiv_eq_map_symm,← F.ray x hx,Submodule.map_span,Set.image_singleton]
    rfl

end SymmetricSubgroupAsymptotics.CFSGHermitianFieldAction

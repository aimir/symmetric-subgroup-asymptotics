import SymmetricSubgroupAsymptotics.CFSGPolarIsometryGeometry
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialFormGroup
import SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction

/-! The literal original B special isometry group acts on the SAME
singular points and planes. The action is by actual matrix submodule
images and composes in the original matrix order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialGeometry
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable (K : Type) [Field K]

abbrev linearEquiv (n : ℕ) (g : specialFormUnits K n) : (Index n→K)≃ₗ[K](Index n→K) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index n→K))) g.val

theorem pairing (n : ℕ) (g : specialFormUnits K n) (x y : Index n→K) :
    (gram K n).toBilin' (linearEquiv K n g x) (linearEquiv K n g y)=(gram K n).toBilin' x y :=
  pairing_invariant K n ⟨g.val,g.property.1⟩ x y

def point (n : ℕ) (g : specialFormUnits K n) : Points (gram K n).toBilin'≃Points (gram K n).toBilin' :=
  CFSGPolarIsometryGeometry.pointEquiv (gram K n).toBilin' (linearEquiv K n g) (pairing K n g)

def plane (n : ℕ) (g : specialFormUnits K n) : Planes (gram K n).toBilin'≃Planes (gram K n).toBilin' :=
  CFSGPolarIsometryGeometry.planeEquiv (gram K n).toBilin' (linearEquiv K n g) (pairing K n g)

theorem point_val (n : ℕ) (g : specialFormUnits K n) (P : Points (gram K n).toBilin') :
    (point K n g P).val=P.val.map (g.val : Mat K n).mulVecLin := rfl

theorem plane_val (n : ℕ) (g : specialFormUnits K n) (L : Planes (gram K n).toBilin') :
    (plane K n g L).val=L.val.map (g.val : Mat K n).mulVecLin := rfl

theorem incidence (n : ℕ) (g : specialFormUnits K n) (P : Points (gram K n).toBilin')
    (L : Planes (gram K n).toBilin') :
    (point K n g P).val≤(plane K n g L).val ↔ P.val≤L.val :=
  CFSGPolarIsometryGeometry.incidence (gram K n).toBilin' (linearEquiv K n g) (pairing K n g) P L

theorem orthogonality (n : ℕ) (g : specialFormUnits K n) (P Q : Points (gram K n).toBilin') :
    ZeroOn (gram K n).toBilin' (point K n g P).val (point K n g Q).val ↔
      ZeroOn (gram K n).toBilin' P.val Q.val :=
  CFSGPolarIsometryGeometry.orthogonality (gram K n).toBilin' (linearEquiv K n g) (pairing K n g) P Q

def pointAction (n : ℕ) : specialFormUnits K n→*Equiv.Perm (Points (gram K n).toBilin') where
  toFun := point K n
  map_one' := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (1 : Mat K n).mulVecLin=P.val
    rw [Matrix.mulVecLin_one,Submodule.map_id]
  map_mul' := by
    intro a b
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map ((a.val*b.val : (Mat K n)ˣ) : Mat K n).mulVecLin=
      (P.val.map (b.val : Mat K n).mulVecLin).map (a.val : Mat K n).mulVecLin
    exact CFSGMatrixSubspaceUnitAction.map_mul P.val a.val b.val

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialGeometry

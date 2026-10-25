import SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedDiagonal

/-! The actual associated-graded units homomorphism on weak triangular
units, with its exact strict kernel. The image is a literal matrix subgroup;
no abstract Levi or radical recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedUnitHom
open CFSGGradedMatrixAssociatedDiagonal CFSGGradedMatrixTriangularUnits
open CFSGGradedMatrixSubgroups CFSGGradedMatrixSupport
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def associatedUnit (w : I → ℤ) (u : triangularUnits (K := K) (fun i => -w i)) :
    (Matrix I I K)ˣ where
  val := associatedDiagonal w (u.val : Matrix I I K)
  inv := associatedDiagonal w (↑(u.val⁻¹) : Matrix I I K)
  val_inv := by
    rw [← associatedDiagonal_mul w _ _ u.property
      ((triangularUnits (fun i => -w i)).inv_mem u.property),
      Units.mul_inv,associatedDiagonal_one]
  inv_val := by
    rw [← associatedDiagonal_mul w _ _
      ((triangularUnits (fun i => -w i)).inv_mem u.property) u.property,
      Units.inv_mul,associatedDiagonal_one]

theorem associatedUnit_val (w : I → ℤ)
    (u : triangularUnits (K := K) (fun i => -w i)) :
    (associatedUnit w u : Matrix I I K) = associatedDiagonal w (u.val : Matrix I I K) := rfl

def associatedUnitHom (w : I → ℤ) :
    triangularUnits (K := K) (fun i => -w i) →* (Matrix I I K)ˣ where
  toFun := associatedUnit w
  map_one' := by
    apply Units.ext
    exact associatedDiagonal_one w
  map_mul' u v := by
    apply Units.ext
    exact associatedDiagonal_mul w (u.val : Matrix I I K) (v.val : Matrix I I K)
      u.property v.property

theorem associatedUnitHom_eq_one_iff (w : I → ℤ)
    (u : triangularUnits (K := K) (fun i => -w i)) :
    associatedUnitHom w u = 1 ↔ u.val ∈ strictUnits w := by
  constructor
  · intro h
    have hv : associatedDiagonal w (u.val : Matrix I I K) = 1 :=
      congrArg (fun z : (Matrix I I K)ˣ => z.val) h
    exact (associatedDiagonal_eq_one_iff w _ u.property).mp hv
  · intro h
    apply Units.ext
    exact (associatedDiagonal_eq_one_iff w _ u.property).mpr h

theorem associatedUnitHom_ker (w : I → ℤ) :
    (associatedUnitHom (K := K) w).ker =
      (strictUnits w).comap (triangularUnits (fun i => -w i)).subtype := by
  ext u
  exact associatedUnitHom_eq_one_iff w u

theorem associatedUnit_mem_preserving (w : I → ℤ)
    (u : triangularUnits (K := K) (fun i => -w i)) :
    associatedUnit w u ∈ preservingUnits w := by
  intro i j hij
  change (if w i = w j then (u.val : Matrix I I K) i j else 0) = 0
  exact if_neg hij

theorem associatedUnit_eq_of_preserving (w : I → ℤ)
    (u : triangularUnits (K := K) (fun i => -w i))
    (hu : u.val ∈ preservingUnits w) : associatedUnit w u = u.val := by
  apply Units.ext
  ext i j
  change (if w i = w j then (u.val : Matrix I I K) i j else 0) = _
  by_cases hij : w i = w j
  · exact if_pos hij
  · exact (if_neg hij).trans (hu i j hij).symm

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedUnitHom

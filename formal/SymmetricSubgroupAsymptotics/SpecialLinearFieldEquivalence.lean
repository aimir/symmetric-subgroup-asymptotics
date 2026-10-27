import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Entrywise field transport of literal SL and its full-centre quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SpecialLinearFieldEquivalence
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F K : Type*} [Field F] [Field K]

def specialLinear (e : F ≃+* K) :
    Matrix.SpecialLinearGroup n F ≃* Matrix.SpecialLinearGroup n K where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    change e.symm (e (A.val i j))=A.val i j
    exact e.symm_apply_apply _
  right_inv A := by
    apply Subtype.ext
    ext i j
    change e (e.symm (A.val i j))=A.val i j
    exact e.apply_symm_apply _
  map_mul' A B := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul A B

def projectiveSpecialLinear (e : F ≃+* K) :
    Matrix.ProjectiveSpecialLinearGroup n F ≃* Matrix.ProjectiveSpecialLinearGroup n K :=
  CFSGCenterQuotientEquiv.equiv (specialLinear (n := n) e)

end SymmetricSubgroupAsymptotics.SpecialLinearFieldEquivalence

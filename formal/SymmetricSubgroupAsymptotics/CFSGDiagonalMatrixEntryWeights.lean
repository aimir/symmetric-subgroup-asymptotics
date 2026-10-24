import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Ring

/-! A matrix entry is a Cartan eigenfunctional when its Cartan matrix is
diagonal. A unit entry on one known eigenvector identifies the functional
weight, so no diagonal-entry census is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixEntryWeights
variable {I R:Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem diagonal_lie_entry (D:Matrix I I R) (hD:D.IsDiag) (M:Matrix I I R) (r c:I) :
    ⁅D,M⁆ r c=(D r r-D c c)*M r c := by
  have hleft:(D*M) r c=D r r*M r c := by
    calc
      _=(Matrix.diagonal (Matrix.diag D)*M) r c :=
        congrArg (fun X:Matrix I I R=>(X*M) r c) hD.diagonal_diag.symm
      _=_:=Matrix.diagonal_mul (Matrix.diag D) M r c
  have hright:(M*D) r c=M r c*D c c := by
    calc
      _=(M*Matrix.diagonal (Matrix.diag D)) r c :=
        congrArg (fun X:Matrix I I R=>(M*X) r c) hD.diagonal_diag.symm
      _=_:=Matrix.mul_diagonal (Matrix.diag D) M r c
  change (D*M-M*D) r c=_
  rw [Matrix.sub_apply,hleft,hright]
  ring

theorem entry_weight_of_unit_seed (D:Matrix I I R) (hD:D.IsDiag)
    (S:Matrix I I R) (r c:I) (k:R) (hunit:S r c=1) (hweight:⁅D,S⁆=k • S)
    (M:Matrix I I R) : ⁅D,M⁆ r c=k*M r c := by
  have h:=congrArg (fun X:Matrix I I R=>X r c) hweight
  change ⁅D,S⁆ r c=k*S r c at h
  rw [diagonal_lie_entry D hD S r c,hunit] at h
  simp only [mul_one] at h
  rw [diagonal_lie_entry D hD M r c,h]

end SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixEntryWeights

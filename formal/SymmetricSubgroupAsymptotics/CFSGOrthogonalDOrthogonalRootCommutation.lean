import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerrePowers
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreEF
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements

/-! All-sign commutation at orthogonal natural D nodes, proved from the
literal matrix Lie relations. No faithfulness of a Serre quotient is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOrthogonalRootCommutation
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
variable (K : Type) [Field K] (r : ℕ)

theorem rootMatrix_lie_zero (hr : 4 ≤ r) (i j : Fin r) (hne : i ≠ j)
    (hij : CartanMatrix.D r i j = 0) (e f : Bool) :
    ⁅rootMatrix K r e i, rootMatrix K r f j⁆ = 0 := by
  cases e <;> cases f
  · exact positive_lie_of_cartan_zero K r hr i j hij
  · exact positive_negative_of_ne K r hr i j hne
  · change ⁅negative K r i, positive K r j⁆ = 0
    rw [← lie_skew (negative K r i) (positive K r j),
      positive_negative_of_ne K r hr j i (Ne.symm hne), neg_zero]
  · exact negative_lie_of_cartan_zero K r hr i j hij

theorem rootElement_commute (hr : 4 ≤ r) (i j : Fin r) (hne : i ≠ j)
    (hij : CartanMatrix.D r i j = 0) (e f : Bool) (a b : K) :
    Commute (rootElement K r e i a) (rootElement K r f j b) := by
  have hc : rootMatrix K r e i * rootMatrix K r f j =
      rootMatrix K r f j * rootMatrix K r e i := by
    exact sub_eq_zero.mp (rootMatrix_lie_zero K r hr i j hne hij e f)
  change _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  change (1 + a • rootMatrix K r e i) * (1 + b • rootMatrix K r f j) =
    (1 + b • rootMatrix K r f j) * (1 + a • rootMatrix K r e i)
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
    mul_smul_comm, hc, smul_add, smul_smul, mul_comm a b]
  abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOrthogonalRootCommutation

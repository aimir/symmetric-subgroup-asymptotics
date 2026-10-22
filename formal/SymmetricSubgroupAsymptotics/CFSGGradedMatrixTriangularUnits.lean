import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! Weak triangular subgroups for literal integer gradings, including
repeated weights. Opposite triangularity is exactly block preservation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularUnits
open CFSGGradedMatrixSubgroups CFSGGradedMatrixSupport
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def triangularUnits (w : I→ℤ) : Subgroup (Matrix I I K)ˣ where
  carrier := {u | (u : Matrix I I K).BlockTriangular w}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun hu hv=>hu.mul hv
  inv_mem' := by
    intro u hu
    change (u : Matrix I I K).BlockTriangular w at hu
    change (↑(u⁻¹) : Matrix I I K).BlockTriangular w
    letI : Invertible (u : Matrix I I K) := u.invertible
    have he : (u : Matrix I I K)⁻¹=(↑(u⁻¹) : Matrix I I K) :=
      Matrix.inv_eq_left_inv (Units.inv_mul u)
    rw [←he]
    exact Matrix.blockTriangular_inv_of_blockTriangular hu

theorem preserving_le_triangular (w : I→ℤ) :
    preservingUnits (K:=K) w≤triangularUnits w := by
  intro u hu i j hij
  exact hu i j (ne_of_gt hij)

theorem strict_le_reverse_triangular (w : I→ℤ) :
    strictUnits (K:=K) w≤triangularUnits (fun i=> -w i) := by
  intro u hu i j hij
  have hlt : w i<w j := by change -w j < -w i at hij; omega
  have hne : i≠j := by intro he; subst j; exact (lt_irrefl _ hlt)
  rw [hu i j hlt.le,Matrix.one_apply,if_neg hne]

theorem triangular_inf_reverse_eq_preserving (w : I→ℤ) :
    triangularUnits (K:=K) w⊓triangularUnits (fun i=> -w i)=preservingUnits w := by
  apply le_antisymm
  · intro u hu i j hij
    change w i≠w j at hij
    rcases lt_or_gt_of_ne hij with h|h
    · exact hu.2 (show -w j < -w i by omega)
    · exact hu.1 h
  · intro u hu
    refine ⟨preserving_le_triangular w hu,?_⟩
    intro i j hij
    apply hu i j
    change w i≠w j
    change -w j < -w i at hij
    omega

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularUnits

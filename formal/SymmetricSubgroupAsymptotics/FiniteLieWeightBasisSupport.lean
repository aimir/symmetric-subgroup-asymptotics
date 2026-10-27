import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Genuine target-action coefficient support from Cartan eigenweights.
This avoids enumerating target raising/lowering rows: Jacobi and basis
coordinates force every nonzero coefficient onto its shifted weight.
No source faithfulness or source stability conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteLieWeightBasisSupport
variable {J L : Type*} [Fintype J] [DecidableEq J]
    [LieRing L] [LieAlgebra ℚ L] (b : Module.Basis J ℚ L)

/-- Actual coordinate action of a diagonal Cartan operator. -/
theorem coordinate_lie (h : L) (w : J→ℚ)
    (hdiag : ∀j,⁅h,b j⁆=w j • b j) (x : L) (j : J) :
    b.repr ⁅h,x⁆ j=w j*b.repr x j := by
  conv_lhs => rw [←b.sum_repr x]
  rw [lie_sum,map_sum]
  simp only [lie_smul,hdiag,map_smul,Module.Basis.repr_self]
  simp [Finset.sum_apply,Finsupp.single_apply,mul_comm,mul_left_comm,mul_assoc]

/-- A nonzero coordinate of an eigenvector has that exact eigenvalue. -/
theorem eigen_coordinate_support (h : L) (w : J→ℚ)
    (hdiag : ∀j,⁅h,b j⁆=w j • b j) (x : L) (mu : ℚ)
    (hx : ⁅h,x⁆=mu • x) (j : J) (hj : b.repr x j≠0) : w j=mu := by
  have hh := congrArg (fun y : L=>b.repr y j) hx
  change b.repr ⁅h,x⁆ j=b.repr (mu • x) j at hh
  rw [coordinate_lie b h w hdiag] at hh
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at hh
  exact mul_right_cancel₀ hj hh

/-- Shift support for a genuine root action, simultaneously for every
Cartan direction. This pays the height/weight support clauses of source
lowering induction when the weights are the literal root coordinates. -/
theorem root_action_support {I : Type*} (h : I→L) (w : I→J→ℚ)
    (hdiag : ∀a j,⁅h a,b j⁆=w a j • b j)
    (e : L) (lambda : I→ℚ) (he : ∀a,⁅h a,e⁆=lambda a • e)
    (j k : J) (hk : b.repr ⁅e,b j⁆ k≠0) :
    ∀a,w a k=lambda a+w a j := by
  intro a
  apply eigen_coordinate_support b (h a) (w a) (hdiag a) ⁅e,b j⁆ _ _ k hk
  rw [leibniz_lie,he,hdiag,smul_lie,lie_smul,add_smul]

end SymmetricSubgroupAsymptotics.FiniteLieWeightBasisSupport

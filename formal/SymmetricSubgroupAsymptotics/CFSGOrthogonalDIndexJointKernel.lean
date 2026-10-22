import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Fewer linear forms than the actual vector-space dimension have
a common nonzero kernel vector. This is a generic original-vector
statement used to remove central scalars between rank-two roots. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexJointKernel
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
variable {I : Type*} [Fintype I]

theorem exists_nonzero_joint_kernel (f : I → Module.Dual K V)
    (hd : Fintype.card I < Module.finrank K V) :
    ∃ x : V, x ≠ 0 ∧ ∀ i, f i x = 0 := by
  by_contra hn
  have hk : ∀ x : V, (∀ i, f i x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    exact hn ⟨x, hx0, hx⟩
  have hi : Function.Injective (LinearMap.pi f) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hk (x - y)
    intro i
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun he i)
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := LinearMap.pi f) hi
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexJointKernel

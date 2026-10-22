import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

/-! The elementary half-dimension ceiling for an actual singular
subspace of a nondegenerate bilinear space. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem singular_two_finrank_le (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Subspaces B) : 2*Module.finrank K W.val ≤ Module.finrank K V := by
  have hle : W.val ≤ B.orthogonal W.val := fun x hx y hy=>W.property y hy x hx
  have hdim := B.finrank_add_finrank_orthogonal' W.val
  rw [hB.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hdim
  have hm := Submodule.finrank_mono hle
  omega

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

import Mathlib.LinearAlgebra.Projectivization.Basic

/-! A genuine linear equivalence between different vector spaces
induces an equivalence between their actual projectivizations. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectivizationLinearEquiv
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

 def map (e : V ≃ₗ[K] W) : ℙ K V ≃ ℙ K W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    rw [← Projectivization.mk_rep p]
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  right_inv p := by
    rw [← Projectivization.mk_rep p]
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

 theorem map_mk (e : V ≃ₗ[K] W) (v : V) (hv : v ≠ 0) :
    map e (Projectivization.mk K v hv) =
      Projectivization.mk K (e v) (fun h => hv (e.injective (by simpa using h))) :=
  Projectivization.map_mk e.toLinearMap e.injective v hv

end SymmetricSubgroupAsymptotics.CFSGProjectivizationLinearEquiv

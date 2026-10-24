import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-! The actual kernel preimage of a subgroup of an abelian semidirect
product is preserved by that same subgroup's actual projected image.
Its index has the exact kernel/projection factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex

variable {N H : Type*} [CommGroup N] [Group H] (φ : H →* MulAut N)

theorem conjugate_inl (x : N ⋊[φ] H) (n : N) :
    x * SemidirectProduct.inl n * x⁻¹ = SemidirectProduct.inl (φ x.right n) := by
  have he : (SemidirectProduct.inl (x.left * φ x.right n * x.left⁻¹) : N ⋊[φ] H) =
      x * SemidirectProduct.inl n * x⁻¹ := by
    calc
      _ = SemidirectProduct.inl x.left *
          (SemidirectProduct.inr x.right * SemidirectProduct.inl n *
            SemidirectProduct.inr x.right⁻¹) * (SemidirectProduct.inl x.left)⁻¹ := by
        rw [map_mul, map_mul, map_inv, SemidirectProduct.inl_aut]
      _ = (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) *
          SemidirectProduct.inl n *
            (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right)⁻¹ := by
        rw [map_inv]
        group
      _ = _ := by rw [SemidirectProduct.inl_left_mul_inr_right]
  rw [← he]
  congr 1
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- This is derived from actual membership in M, not a separate
invariance certificate for an unrelated coordinate subgroup. -/
theorem action_mem_kernel_of_projected (M : Subgroup (N ⋊[φ] H))
    (A : H) (hA : A ∈ M.map SemidirectProduct.rightHom)
    (n : N) (hn : n ∈ M.comap SemidirectProduct.inl) :
    φ A n ∈ M.comap SemidirectProduct.inl := by
  obtain ⟨x, hx, hr⟩ := hA
  change x.right = A at hr
  change SemidirectProduct.inl (φ A n) ∈ M
  rw [← hr, ← conjugate_inl φ x n]
  exact M.mul_mem (M.mul_mem hx hn) (M.inv_mem hx)

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (ψ : B →* MulAut A) : Finite (A ⋊[ψ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

/-- Both factors belong to the same actual subgroup M. -/
theorem index_factor [Finite N] [Finite H] (M : Subgroup (N ⋊[φ] H)) :
    M.index = (M.comap SemidirectProduct.inl).index *
      (M.map SemidirectProduct.rightHom).index := by
  have h := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H)
    SemidirectProduct.rightHom_surjective M
  have hk : (M.comap SemidirectProduct.inl).index =
      M.relIndex (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).ker := by
    rw [Subgroup.index_comap, SemidirectProduct.range_inl_eq_ker_rightHom]
  rw [← hk] at h
  exact h

end SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex

import Mathlib.Algebra.Group.Subgroup.Ker

/-! Subgroup intersections survive a noninjective quotient if its
kernel lies in one factor. This retains the literal positive subgroup
when transporting opposite-parabolic intersections to a projective
model; faithfulness of the entire source is unnecessary. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection
variable {G Q : Type*} [Group G] [Group Q]

theorem map_inf_eq_of_kernel_le_right (f : G →* Q) (H P : Subgroup G)
    (hker : f.ker ≤ P) : (H ⊓ P).map f = H.map f ⊓ P.map f := by
  apply le_antisymm (Subgroup.map_inf_le H P f)
  rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  have hxy : x * y⁻¹ ∈ f.ker := by
    change f (x * y⁻¹) = 1
    rw [map_mul, map_inv, ← hyx, mul_inv_cancel]
  have h := P.mul_mem (hker hxy) hy
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

theorem map_inf_eq_of_kernel_le_left (f : G →* Q) (H P : Subgroup G)
    (hker : f.ker ≤ H) : (H ⊓ P).map f = H.map f ⊓ P.map f := by
  rw [inf_comm H P, map_inf_eq_of_kernel_le_right f P H hker, inf_comm]

end SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

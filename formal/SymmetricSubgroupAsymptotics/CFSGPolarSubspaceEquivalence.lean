import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceTransport

/-! The constructed singular-subspace transport is reversible and an
order isomorphism. In particular maximal singular subspaces are genuine
images, rather than additional geometric data supplied to the proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V) (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)

include hinc in
theorem inverse_incidence : ∀P L,(f.symm P).val ≤ (l.symm L).val ↔ P.val ≤ L.val := by
  intro P L
  simpa only [f.apply_symm_apply,l.apply_symm_apply] using
    (hinc (f.symm P) (l.symm L)).symm

include horth in
theorem inverse_orthogonality :
    ∀P Q,ZeroOn B (f.symm P).val (f.symm Q).val ↔ ZeroOn B P.val Q.val := by
  intro P Q
  simpa only [f.apply_symm_apply] using (horth (f.symm P) (f.symm Q)).symm

theorem imageSubspace_left_inverse : Function.LeftInverse
    (imageSubspace B f.symm l.symm (inverse_incidence B f l hinc)
      (inverse_orthogonality B f horth)) (imageSubspace B f l hinc horth) := by
  intro W
  apply subspace_ext B
  intro P
  have hi := point_le_image_iff B f.symm l.symm (inverse_incidence B f l hinc)
    (imageSubspace B f l hinc horth W) (f P)
  simp only [f.symm_apply_apply] at hi
  exact hi.trans (point_le_image_iff B f l hinc W P)

theorem imageSubspace_right_inverse : Function.RightInverse
    (imageSubspace B f.symm l.symm (inverse_incidence B f l hinc)
      (inverse_orthogonality B f horth)) (imageSubspace B f l hinc horth) := by
  intro W
  apply subspace_ext B
  intro P
  have hi := point_le_image_iff B f l hinc
    (imageSubspace B f.symm l.symm (inverse_incidence B f l hinc)
      (inverse_orthogonality B f horth) W) (f.symm P)
  simp only [f.apply_symm_apply] at hi
  exact hi.trans (point_le_image_iff B f.symm l.symm (inverse_incidence B f l hinc) W P)

def subspaceOrderIso : Subspaces B ≃o Subspaces B where
  toFun := imageSubspace B f l hinc horth
  invFun := imageSubspace B f.symm l.symm (inverse_incidence B f l hinc)
    (inverse_orthogonality B f horth)
  left_inv := imageSubspace_left_inverse B f l hinc horth
  right_inv := imageSubspace_right_inverse B f l hinc horth
  map_rel_iff' := by
    intro W Z
    exact ⟨imageSubspace_reflects_le B f l hinc horth,imageSubspace_mono B f l hinc horth⟩

theorem subspaceOrderIso_point_incidence (W : Subspaces B) (P : Points B) :
    (f P).val ≤ (subspaceOrderIso B f l hinc horth W).val ↔ P.val ≤ W.val :=
  point_le_image_iff B f l hinc W P

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

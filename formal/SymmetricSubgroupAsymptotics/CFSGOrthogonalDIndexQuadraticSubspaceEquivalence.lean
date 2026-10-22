import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceTransport

/-! Reversible order transport of actual Q-zero submodules from the
literal singular point/plane incidence maps. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (f : Points Q ≃ Points Q) (l : Planes Q ≃ Planes Q)
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)

include hinc in
theorem inverse_incidence : ∀ P L, (f.symm P).val ≤ (l.symm L).val ↔ P.val ≤ L.val := by
  intro P L
  simpa only [f.apply_symm_apply, l.apply_symm_apply] using (hinc (f.symm P) (l.symm L)).symm

theorem imageSubspace_left_inverse : Function.LeftInverse
    (imageSubspace Q f.symm l.symm (inverse_incidence Q f l hinc))
      (imageSubspace Q f l hinc) := by
  intro W
  apply subspace_ext Q
  intro P
  have hi := point_le_image_iff Q f.symm l.symm (inverse_incidence Q f l hinc)
    (imageSubspace Q f l hinc W) (f P)
  simp only [f.symm_apply_apply] at hi
  exact hi.trans (point_le_image_iff Q f l hinc W P)

theorem imageSubspace_right_inverse : Function.RightInverse
    (imageSubspace Q f.symm l.symm (inverse_incidence Q f l hinc))
      (imageSubspace Q f l hinc) := by
  intro W
  apply subspace_ext Q
  intro P
  have hi := point_le_image_iff Q f l hinc
    (imageSubspace Q f.symm l.symm (inverse_incidence Q f l hinc) W) (f.symm P)
  simp only [f.apply_symm_apply] at hi
  exact hi.trans (point_le_image_iff Q f.symm l.symm (inverse_incidence Q f l hinc) W P)

def subspaceOrderIso : Subspaces Q ≃o Subspaces Q where
  toFun := imageSubspace Q f l hinc
  invFun := imageSubspace Q f.symm l.symm (inverse_incidence Q f l hinc)
  left_inv := imageSubspace_left_inverse Q f l hinc
  right_inv := imageSubspace_right_inverse Q f l hinc
  map_rel_iff' := by
    intro W Z
    exact ⟨imageSubspace_reflects_le Q f l hinc, imageSubspace_mono Q f l hinc⟩

theorem subspaceOrderIso_point_incidence (W : Subspaces Q) (P : Points Q) :
    (f P).val ≤ (subspaceOrderIso Q f l hinc W).val ↔ P.val ≤ W.val :=
  point_le_image_iff Q f l hinc W P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints

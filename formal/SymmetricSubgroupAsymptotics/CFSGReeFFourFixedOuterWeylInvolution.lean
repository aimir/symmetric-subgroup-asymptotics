import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterThreeWord

/-! The exact original fixed-group outer Weyl involution, proved with
its field parameter kept abstract. Concrete consumers use these opaque
semantic facts rather than repeatedly expanding a subtype/root word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterWeylInvolution
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeWeylInvolutions

theorem outer_weyl_inv (m : ℕ) : (outerFixedWeyl m)⁻¹ = outerFixedWeyl m :=
  Subtype.ext (outerRelativeWeyl_inv m)

theorem outer_weyl_square (m : ℕ) : (outerFixedWeyl m) ^ 2 = 1 := by
  rw [pow_two]
  calc
    outerFixedWeyl m * outerFixedWeyl m =
        outerFixedWeyl m * (outerFixedWeyl m)⁻¹ :=
      congrArg (fun z => outerFixedWeyl m * z) (outer_weyl_inv m).symm
    _ = 1 := mul_inv_cancel _

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterWeylInvolution

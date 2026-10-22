import Mathlib.Algebra.Group.Commute.Basic

/-! A rank-one Weyl reflection detects noncommutation without a
characteristic-dependent matrix entry. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGRankOneNoncommutation
variable {G : Type*} [Group G]

theorem not_commute (u v : G) (hsep : u ≠ v⁻¹)
    (hreflect : (u * v⁻¹ * u) * u * (u * v⁻¹ * u)⁻¹ = v⁻¹) : ¬ Commute u v := by
  intro hc
  have hw : Commute u (u * v⁻¹ * u) :=
    ((Commute.refl u).mul_right hc.inv_right).mul_right (Commute.refl u)
  apply hsep
  calc
    u = (u * v⁻¹ * u) * u * (u * v⁻¹ * u)⁻¹ := by
      rw [← hw.eq, mul_assoc, mul_inv_cancel, mul_one]
    _ = v⁻¹ := hreflect

end SymmetricSubgroupAsymptotics.CFSGRankOneNoncommutation

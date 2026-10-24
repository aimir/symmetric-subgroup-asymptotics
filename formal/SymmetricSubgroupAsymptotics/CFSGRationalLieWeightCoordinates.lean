import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights

/-! Weight transport and coefficient orthogonality over the rational
source. Exact zero coordinates can subsequently be reflected to integers
before reduction; no distinct-weight assertion is made in a finite field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRationalLieWeightCoordinates
variable {L:Type*} [LieRing L] [LieAlgebra ℚ L]

theorem bracket_weight (h x y:L) (mu nu:ℚ)
    (hx:⁅h,x⁆=mu • x) (hy:⁅h,y⁆=nu • y) :
    ⁅h,⁅x,y⁆⁆=(mu+nu) • ⁅x,y⁆ := by
  rw [leibniz_lie,hx,hy,smul_lie,lie_smul,add_smul]

theorem coordinate_zero_of_weights_ne (h:L) (ell:L→ₗ[ℚ]ℚ) (mu k:ℚ)
    (hell:∀y,ell ⁅h,y⁆=k*ell y) (x:L) (hx:⁅h,x⁆=mu • x) (hne:mu≠k) :
    ell x=0 := by
  have hc:=hell x
  rw [hx,map_smul] at hc
  change mu*ell x=k*ell x at hc
  have hz:(mu-k)*ell x=0 := by rw [sub_mul,hc,sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end SymmetricSubgroupAsymptotics.CFSGRationalLieWeightCoordinates

import SymmetricSubgroupAsymptotics.CFSGTwistedDImageTwist
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDImageRealization

/-! The actual natural group action on the SAME matrix image intertwines
its genuine natural diagram--field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalImageCovariance
open CFSGOrthogonalDSerreMatrices CFSGTwistedDImageTwist CFSGTwistedDNaturalFieldTwist

theorem elementary_covariance (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (u : elementaryRootGroup K (s + 4))
    (y : (orthogonalBaseChange K (s + 4) (by omega)).range) :
    elementaryImageAction K (s + 4) (by omega)
      (naturalAutomorphism K (s + 2) σ u) (rangeTwist K s σ y) =
      rangeTwist K s σ (elementaryImageAction K (s + 4) (by omega) u y) := by
  apply Subtype.ext
  change (unitTwist K (s + 2) σ u.val : Mat K (s + 4)) *
    matrixTwist K (s + 2) σ y.val *
      (↑((unitTwist K (s + 2) σ u.val)⁻¹) : Mat K (s + 4)) =
    matrixTwist K (s + 2) σ ((u.val : Mat K (s + 4)) * y.val *
      (↑(u.val⁻¹) : Mat K (s + 4)))
  rw [map_mul, map_mul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalImageCovariance

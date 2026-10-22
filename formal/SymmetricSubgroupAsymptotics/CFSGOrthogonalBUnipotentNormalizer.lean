import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSeparation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentSeparation

/-! The full actual unipotent normalizer lies in the SAME natural Borel.
The flag-recognition separation premise is discharged by the preceding
literal B root words, including the quadratic paired-axis tests. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices

def naturalMatrixHom (K : Type) [Field K] (n : ℕ) : elementaryRootGroup K n →* Mat K n :=
  (Units.coeHom (Mat K n)).comp (elementaryRootGroup K n).subtype

theorem normalizer_unipotent_le_borel (K : Type) [Field K]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Subgroup.normalizer (unipotent K (s + 1) : Set (elementaryRootGroup K (s + 1))) ≤
      borel K (s + 1) := by
  intro g hg
  apply CFSGMatrixFlagNormalizer.normalizer_upper_of_separation (flagEquiv (s + 1))
    (naturalMatrixHom K (s + 1)) (unipotent K (s + 1))
    (fun _ hu => hu.1) (fun _ hu => hu.2) ?_ g hg
  intro i j hij v hz
  exact unipotent_displacement_separates K h2 s i j hij v hz

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent

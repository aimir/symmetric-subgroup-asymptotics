import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentEntryTests

/-! The actual C-unipotent normalizer preserves the same isotropic
complete flag. All entry tests are supplied by literal root words. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

def naturalMatrixHom (K : Type) [Field K] (n : ℕ) :
    elementaryRootGroup K n →* Mat K n :=
  (Units.coeHom (Mat K n)).comp (elementaryRootGroup K n).subtype

theorem normalizer_unipotent_le_borel (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    Subgroup.normalizer (unipotent K (r + 1) : Set (elementaryRootGroup K (r + 1))) ≤
      borel K (r + 1) := by
  intro A hA
  apply CFSGMatrixFlagNormalizer.normalizer_upper (flagEquiv (r + 1))
    (naturalMatrixHom K (r + 1)) (unipotent K (r + 1))
    (fun _ hu => hu.1) (fun _ hu => hu.2) ?_ A hA
  intro i j hij
  obtain ⟨u, hu⟩ := unipotent_entry_test (K := K) r hr i j hij
  exact ⟨u.val, u.property, hu⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent

import SymmetricSubgroupAsymptotics.CFSGTwistedDImageTwist
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality

/-! Every actual elementary D central element is fixed by the natural
fork/field twist. Its scalar is literally 1 or -1, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDCenterFixed
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexCenterCard
open CFSGOrthogonalDCenterCardinality CFSGTwistedDNaturalFieldTwist
open CFSGTwistedDImageTwist

theorem center_fixed (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (z : elementaryRootGroup K (s + 4)) (hz : z ∈ Subgroup.center (elementaryRootGroup K (s + 4))) :
    naturalAutomorphism K (s + 2) σ z = z := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) z).mp hz
  have he : centerEntry K s ⟨z, hz⟩ = c := by
    change (z.val : Mat K (s + 4)) (Sum.inl 0) (Sum.inl 0) = c
    simp only [hc, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hpm := centerEntry_eq_one_or_neg_one K s ⟨z, hz⟩
  rw [he] at hpm
  have hσ : σ c = c := by
    rcases hpm with rfl | rfl <;> simp only [map_one, map_neg]
  apply Subtype.ext
  apply Units.ext
  change matrixTwist K (s + 2) σ (z.val : Mat K (s + 4)) = (z.val : Mat K (s + 4))
  rw [hc, matrixTwist_smul, map_one, hσ]

end SymmetricSubgroupAsymptotics.CFSGTwistedDCenterFixed

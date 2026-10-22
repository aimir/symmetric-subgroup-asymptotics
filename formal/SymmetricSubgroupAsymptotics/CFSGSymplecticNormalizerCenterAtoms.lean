import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
import SymmetricSubgroupAsymptotics.CFSGSymplecticMinimalCenterAxes
import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelNormalizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticLongCenterRootLine

/-! Concrete intrinsic centre atoms for the actual characteristic-two
C Sylow. The normalizer in the predicate is the full actual group
normalizer; no chosen torus or Borel is assumed to be characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem normalizerCenterAtom_iff_axis (r : ℕ) (hr : 0 < r) (hq : 2 < Nat.card K)
    (H : Subgroup (elementaryRootGroup K (r + 1))) :
    CFSGNormalizerCenterAtoms.IsAtom (unipotent K (r + 1)) H ↔
      H = longCenterAxis r hr ∨ H = shortCenterAxis r hr := by
  have hcent : CFSGNormalizerCenterAtoms.centerImage (unipotent K (r + 1)) =
      (centerToElementary (K := K) r hr).range := (centerToElementary_range r hr).symm
  have hnorm := normalizer_unipotent_eq_borel K r hr
  constructor
  · intro h
    apply minimal_normalized_center_subgroup_axis r hr hq H h.1
      (h.2.1.trans_eq hcent)
    · rw [← hnorm]
      exact h.2.2.1
    · intro J hne hle hN
      apply h.2.2.2 J hne hle
      rw [hnorm]
      exact hN
  · rintro (rfl | rfl)
    · refine ⟨longCenterAxis_ne_bot r hr, ?_, ?_, ?_⟩
      · rw [hcent]
        exact longCenterAxis_le_range r hr
      · rw [hnorm]
        exact borel_le_normalizer_longCenterAxis r hr
      · intro J hne hle hN
        apply longCenterAxis_minimal r hr hq J hne hle
        rwa [← hnorm]
    · refine ⟨shortCenterAxis_ne_bot r hr, ?_, ?_, ?_⟩
      · rw [hcent]
        exact shortCenterAxis_le_range r hr
      · rw [hnorm]
        exact borel_le_normalizer_shortCenterAxis r hr
      · intro J hne hle hN
        apply shortCenterAxis_minimal r hr hq J hne hle
        rwa [← hnorm]

theorem naturalRoot_is_normalizerCenterAtom (r : ℕ) (hr : 0 < r) (hq : 2 < Nat.card K) :
    CFSGNormalizerCenterAtoms.IsAtom (unipotent K (r + 1))
      (CFSGSymplecticTransvectionGeometry.actualNaturalRootLine r hr
        (Pi.single (Sum.inl (0 : Fin (r + 1))) 1)) := by
  rw [← longCenterAxis_eq_actualNaturalRootLine r hr]
  exact (normalizerCenterAtom_iff_axis r hr hq _).mpr (Or.inl rfl)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent

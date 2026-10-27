import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormalizerStructure

/-! Transport the actual literal SL2 normalizer through its central quotient.
No projective action, torus position, or normalizer classification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitQuotientNormalizer
open PSLTwoLiteralNonsplitTorusCyclic PSLTwoLiteralNonsplitNormalizerStructure
variable {F : Type*} [Field F]
local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "PSL2" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) F

abbrev projection : SL2 →* PSL2 := QuotientGroup.mk' (Subgroup.center SL2)

theorem center_le_nonsplitSL (ν : F) : Subgroup.center SL2 ≤ nonsplitSL ν := by
  intro A hA
  obtain ⟨r,_,hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  change A.val 1 1=A.val 0 0 ∧ A.val 0 1=ν*A.val 1 0
  rw [←hr]
  simp [Matrix.scalar_apply]

theorem comap_torus (ν : F) : (nonsplitTorus ν).comap projection=nonsplitSL ν := by
  apply Subgroup.comap_map_eq_self
  rw [QuotientGroup.ker_mk']
  exact center_le_nonsplitSL ν

theorem comap_normalizer (ν : F) :
    (Subgroup.normalizer (nonsplitTorus ν : Set PSL2)).comap projection=
      Subgroup.normalizer (nonsplitSL ν : Set SL2) := by
  rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),comap_torus]

theorem map_normalizer (ν : F) :
    (Subgroup.normalizer (nonsplitSL ν : Set SL2)).map projection=
      Subgroup.normalizer (nonsplitTorus ν : Set PSL2) := by
  rw [←comap_normalizer]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem projection_mem_torus_iff (ν : F) (M : SL2) :
    projection M ∈ nonsplitTorus ν ↔ M ∈ nonsplitSL ν := by
  change M ∈ (nonsplitTorus ν).comap projection ↔ _
  rw [comap_torus]

/-- Exact projective-normalizer membership tested on ANY actual SL2 lift. -/
theorem projection_mem_normalizer_iff (h2 : (2 : F) ≠ 0) {ν : F} (hν : ¬IsSquare ν)
    {C : SL2} (hC : C ∈ nonsplitSL ν) (hy : C.val 1 0 ≠ 0) (M : SL2) :
    projection M ∈ Subgroup.normalizer (nonsplitTorus ν : Set PSL2) ↔
      M ∈ nonsplitSL ν ∨ IsAntiNS ν M := by
  change M ∈ (Subgroup.normalizer (nonsplitTorus ν : Set PSL2)).comap projection ↔ _
  rw [comap_normalizer]
  exact normalizer_mem_iff h2 hν hC hy M

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitQuotientNormalizer

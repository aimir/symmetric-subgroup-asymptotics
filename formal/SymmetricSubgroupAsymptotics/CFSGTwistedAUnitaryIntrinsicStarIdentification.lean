import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPlaneCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarConjugateContainment
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarConeGeneration

/-! Exact ORIGINAL projective intrinsic-star recognition. The join of
all original centre-root subgroups at points of the literal two-plane
is precisely the image of the actual Hermitian shear group. Both
inclusions are proved using original root words and additive rank-one
cone generation; no model identification or automorphism callback is
supplied as a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical

theorem starRankOne_zero_vector (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a) :
    starFixed q s (starRankOneParameters q s t htc a ha 0) = 1 := by
  apply unitaryNaturalEndHom_injective q (s + 3)
  rw [map_one]
  apply LinearMap.ext
  intro x
  change ((starFixed q s (starRankOneParameters q s t htc a ha 0)).val.val :
    Mat (q.Extension 2) (s + 3)) *ᵥ x = x
  rw [starRankOne_action]
  have hz : starVector q s 0 = 0 := by
    simp only [starVector, Pi.zero_apply, zero_smul, zero_add]
  rw [hz, smul_zero, add_zero]

theorem starRankOne_projective_mem_intrinsicStar (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
    (v : Fin 2 → q.Extension 2) :
    unitaryProjectiveCover q s (starFixed q s (starRankOneParameters q s t htc a ha v)) ∈
      unitaryRootStar q s (starPlane q s) := by
  by_cases hv : v = 0
  · rw [hv, starRankOne_zero_vector, map_one]
    exact (unitaryRootStar q s (starPlane q s)).one_mem
  obtain ⟨g, c, hc, hgv⟩ := exists_starVector_representative q s v hv
  have hroot : unitaryProjectiveCover q s
      (starFixed q s (starRankOneParameters q s t htc a ha v)) ∈
        unitaryPointRoot q s (starPoint q s v hv) := by
    rw [unitaryPointRoot_starPoint_representative q s v hv g c hc hgv,
      conjugateProjectiveCentralRootLine_cover]
    exact ⟨_, starRankOne_mem_conjugateRootLine q s t htc a ha v g c hc hgv, rfl⟩
  exact unitaryPointRoot_le_star q s (starPlane q s) (starPoint q s v hv)
    (starPoint_le_starPlane q s v hv) hroot

theorem naturalRootStarGroup_projective_eq_intrinsicStar (q : CFSG.PrimePower) (s : ℕ) :
    (naturalRootStarGroup q s).map (unitaryProjectiveCover q s) =
      unitaryRootStar q s (starPlane q s) := by
  obtain ⟨t, ht, htc⟩ := CFSGTwistedAUnitaryNaturalRadical.exists_nonzero_central_parameter q (s + 1)
  have htmem : t ∈ centralParameters q (s + 1) := (centralCondition_iff q (s + 1) t).mp htc
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply naturalRootStarGroup_le_of_rankOne q s t ht htmem
    intro a ha v
    exact starRankOne_projective_mem_intrinsicStar q s t htmem a ha v
  · apply iSup_le
    intro P
    obtain ⟨v, hv, heP⟩ := exists_starPoint_of_le q s P.val P.property
    obtain ⟨g, c, hc, hgv⟩ := exists_starVector_representative q s v hv
    change unitaryPointRoot q s P.val ≤ _
    rw [← heP, unitaryPointRoot_starPoint_representative q s v hv g c hc hgv,
      conjugateProjectiveCentralRootLine_cover]
    exact Subgroup.map_mono (conjugateRootLine_le_rootStarGroup q s t ht htmem v g c hgv)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

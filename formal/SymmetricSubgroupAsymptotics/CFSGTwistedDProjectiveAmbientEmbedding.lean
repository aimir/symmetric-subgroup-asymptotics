import SymmetricSubgroupAsymptotics.CFSGTwistedDIntrinsicRootProduct
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency

/-! The actual relative central quotient embeds in the ambient split-D
central quotient because both restricted centres are literal scalars.
Its fixed-field root lines map into ambient root lines, rather than
being asserted equal to the larger extension-field root lines. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveAmbientEmbedding
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeUnipotentSylow CFSGTwistedDRelativeCenter
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDProjectivePlaneLabel CFSGTwistedDIntrinsicRootProduct
open CFSGTwistedDPlaneRootLine CFSGTwistedDRootPlaneImage CFSGTwistedA2FixedField

theorem projectiveAmbientHom_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (projectiveAmbientHom s q) := by
  apply (projectiveAmbientHom s q).ker_eq_bot_iff.mp
  apply bot_unique
  intro z hz
  obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective
    (Subgroup.center (relativeRootGroup (s + 2) q))) z
  change CFSGOrthogonalDIndexProjectiveUnipotent.projection (q.Extension 2) s
    (relativeInclusion s q x) = 1 at hz
  have hc : relativeInclusion s q x ∈
      Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) :=
    (QuotientGroup.eq_one_iff _).mp hz
  have hs := (elementaryRootGroup_center_iff_scalar (q.Extension 2) (s + 2)
    (relativeInclusion s q x)).mp hc
  have hx : x ∈ Subgroup.center (relativeRootGroup (s + 2) q) :=
    (relativeRootGroup_center_iff_scalar (s + 2) q x).mpr hs
  change projection s q x = 1
  exact (QuotientGroup.eq_one_iff _).mpr hx

theorem projective_root_maps_to_ambient (s : ℕ) (q : CFSG.PrimePower)
    (x : Projective s q) (hx : IsProjectiveRootElement s q x) :
    CFSGOrthogonalDIndexProjectiveRootAdjacency.IsProjectiveRootElement (q.Extension 2) s
      (projectiveAmbientHom s q x) := by
  obtain ⟨y, ⟨g, a, rfl⟩, rfl⟩ := hx
  refine ⟨relativeInclusion s q g * CFSGOrthogonalDIndexPairOperator.highestRoot
      (q.Extension 2) s (a : q.Extension 2) * (relativeInclusion s q g)⁻¹,
    ⟨relativeInclusion s q g, (a : q.Extension 2), rfl⟩, ?_⟩
  rw [projectiveAmbientHom_apply, inclusion_conjugate_highest]

theorem projectiveRootLine_image_le_ambient (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    (projectiveConjugateRootLine s q (projection s q g)).map (projectiveAmbientHom s q) ≤
      CFSGOrthogonalDIndexProjectiveRootFamily.projectiveConjugateRootLine (q.Extension 2) s
        (CFSGOrthogonalDIndexProjectiveUnipotent.projection (q.Extension 2) s
          (relativeInclusion s q g)) := by
  rintro x ⟨y, hy, rfl⟩
  rw [← map_conjugateRootLine] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨a, rfl⟩ := (mem_conjugateRootLine_iff s q g z).mp hz
  rw [projectiveAmbientHom_apply, inclusion_conjugate_highest,
    ← CFSGOrthogonalDIndexProjectivePlaneLabel.map_conjugateRootLine]
  refine ⟨relativeInclusion s q g * CFSGOrthogonalDIndexPairOperator.highestRoot
      (q.Extension 2) s (a : q.Extension 2) * (relativeInclusion s q g)⁻¹, ?_, rfl⟩
  exact (CFSGOrthogonalDIndexProjectivePlaneLabel.mem_conjugateRootLine_iff
    (q.Extension 2) s (relativeInclusion s q g) _).mpr ⟨(a : q.Extension 2), rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveAmbientEmbedding

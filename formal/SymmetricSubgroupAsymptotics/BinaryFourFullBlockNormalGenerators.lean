import SymmetricSubgroupAsymptotics.BinaryFourFullBlockNormalCover
import SymmetricSubgroupAsymptotics.NormalGeneratorAmbientEnlargement

/-! Two ambient normal generators for the full four-block source.
Proper invariant translation subgroups lie in augmentation and inherit
the checked restricted-action bound. The full translation module is
normally cyclic. Outside translations the actual quotient kernel cover
transfers the four-dimensional ternary quotient bound. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

theorem augmentation_normalGen_le_two (N : Subgroup Ambient) [N.Normal]
    (hNE : N ≤ ambientTranslationKernel)
    (haug : ∀ g ∈ N, augmentation g.left.toAdd = 0) : MarkedC4.normalGen N ≤ 2 := by
  let f : Row12Model →* Ambient := row12Subgroup.subtype
  let M : Subgroup Row12Model := N.comap f
  letI : M.Normal := (inferInstance : N.Normal).comap f
  have hME : M ≤ sourceKernel true := by
    intro g hg
    exact hNE hg
  have hmap : M.map f = N := by
    apply le_antisymm (Subgroup.map_comap_le _ _)
    intro g hg
    have hr : g.right = 1 := hNE hg
    have hs : g ∈ row12Subgroup := by
      change augmentation g.left.toAdd = localCycle g.right.left.toAdd
      rw [haug g hg, hr]
      exact (map_zero localCycle).symm
    exact ⟨⟨g, hs⟩, hg, rfl⟩
  letI : (M.map f).Normal := by rw [hmap]; infer_instance
  have hb := normalGen_map_le_of_normal_image f M
    (@sourceKernel_normalGen_le_two true M (inferInstance : M.Normal) hME)
  rwa [hmap] at hb

theorem ambientTranslationKernel_normalGen_le_one :
    MarkedC4.normalGen ambientTranslationKernel ≤ 1 := by
  let t : Ambient := inl (Multiplicative.ofAdd (fullBasis 6))
  let x : Fin 1 → Ambient := fun _ => t
  let L := Subgroup.normalClosure (Set.range x)
  have hLE : L ≤ ambientTranslationKernel := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    rfl
  have hL6 : fullBasis 6 ∈ ambientNormalSpace L :=
    Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
  have ha : augmentation (fullBasis 6) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    exact one_ne_zero h0
  have htop := fullSpace_eq_top_of_nonzero_augmentation (ambientNormalSpace L)
    (ambientNormalSpace_u L inferInstance) (ambientNormalSpace_v L inferInstance)
    (ambientNormalSpace_c L inferInstance) (fullBasis 6) hL6 ha
  have hEL : ambientTranslationKernel ≤ L := by
    intro g hg
    have h : g.left.toAdd ∈ ambientNormalSpace L := by
      rw [htop]
      exact Submodule.mem_top
    have he : (inl (Multiplicative.ofAdd g.left.toAdd) : Ambient) = g :=
      SemidirectProduct.ext rfl (show g.right = 1 from hg).symm
    change (inl (Multiplicative.ofAdd g.left.toAdd) : Ambient) ∈ L at h
    rwa [he] at h
  exact normalGen_le_of_fin_tuple x (le_antisymm hLE hEL)

theorem ambient_inside_translation_normalGen_le_two
    (N : Subgroup Ambient) [N.Normal] (hNE : N ≤ ambientTranslationKernel) :
    MarkedC4.normalGen N ≤ 2 := by
  rcases fullSpace_eq_top_or_augmentation (ambientNormalSpace N)
      (ambientNormalSpace_u N inferInstance) (ambientNormalSpace_v N inferInstance)
      (ambientNormalSpace_c N inferInstance) with htop | haug
  · have he : N = ambientTranslationKernel := by
      apply le_antisymm hNE
      intro g hg
      have h : g.left.toAdd ∈ ambientNormalSpace N := by
        rw [htop]
        exact Submodule.mem_top
      have he : (inl (Multiplicative.ofAdd g.left.toAdd) : Ambient) = g :=
        SemidirectProduct.ext rfl (show g.right = 1 from hg).symm
      change (inl (Multiplicative.ofAdd g.left.toAdd) : Ambient) ∈ N at h
      rwa [he] at h
    rw [he]
    exact ambientTranslationKernel_normalGen_le_one.trans (by decide)
  · apply augmentation_normalGen_le_two N hNE
    intro g hg
    apply haug g.left.toAdd
    have he : (inl (Multiplicative.ofAdd g.left.toAdd) : Ambient) = g :=
      SemidirectProduct.ext rfl (show g.right = 1 from hNE hg).symm
    change (inl (Multiplicative.ofAdd g.left.toAdd) : Ambient) ∈ N
    rwa [he]

theorem ambient_normalGen_le_two (N : Subgroup Ambient) [N.Normal] :
    MarkedC4.normalGen N ≤ 2 := by
  by_cases hNE : N ≤ ambientTranslationKernel
  · exact ambient_inside_translation_normalGen_le_two N hNE
  · letI : (N.map fullBlockQuotientMap).Normal :=
      (inferInstance : N.Normal).map fullBlockQuotientMap fullBlockQuotientMap_surjective
    apply normalGen_le_of_kernel_cover_outside fullBlockQuotientMap
      fullBlockQuotientMap_surjective ambientTranslationKernel ?_
      fullBlockQuotient_kernel_cover N hNE (fullBlockQuotient_normalGen_le_two _)
    intro g hg
    exact ((fullBlockQuotientMap_kernel g).mp hg).1

theorem ambient_normal_generating_pairs : ∀ N : Subgroup Ambient, N.Normal →
    ∃ x : Fin 2 → Ambient, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (ambient_normalGen_le_two N)

theorem fullBlockModel_socle_of_surjective {Q : Type} [Group Q]
    (pi : Ambient →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  normal_generating_tuples_of_surjective pi hpi ambient_normal_generating_pairs
    (finiteGroupSocle Q) inferInstance

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end

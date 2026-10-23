import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedCenterImage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily

/-! The previously counted highest-root family is intrinsic in the SAME
ORIGINAL simple triality model. The two-disjoint-Sylow argument makes
the central projection injective on this whole Sylow, so its full centre
survives exactly. Arbitrary original automorphisms need not lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalOrderLower
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckDerivedCenterImage
open CFSGTrialityGeckDerivedLongLine CFSGTrialityGeckDerivedProjectiveImage
open CFSGTrialityGeckDerivedSylowNormalizer CFSGOrthogonalDIndexSylowCenterFamily
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (DerivedImage q) :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Finite (CFSG.Models.TrialityD4 q) :=
  Finite.of_injective (originalProjectiveImageEquiv q) (originalProjectiveImageEquiv q).injective

private theorem restricted_center_image {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P : Subgroup G) (hf : Function.Injective (f.comp P.subtype)) :
    (centerImage P).map f=centerImage (P.map f) := by
  have he := CFSGInjectiveCenterImage.center_image (f.comp P.subtype) hf
  have hr : (f.comp P.subtype).range=P.map f := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  rw [hr] at he
  change ((Subgroup.center P).map P.subtype).map f=_
  rw [Subgroup.map_map]
  exact he

def originalSylow (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Sylow q.prime (CFSG.Models.TrialityD4 q) :=
  (imagePositiveSylow q).mapSurjective (f := originalProjection q)
    (originalProjection_surjective q)

theorem originalProjection_sylow_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective ((originalProjection q).comp
      (imagePositiveSylow q : Subgroup (DerivedImage q)).subtype) := by
  have hi := CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    (imagePositiveSylow q) (oppositeSylow q) (oppositeSylows_disjoint q)
  exact (originalProjectiveImageEquiv q).symm.injective.comp hi

theorem originalSylow_centerImage (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    centerImage (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))=originalLongLine q := by
  have he := restricted_center_image (originalProjection q)
    (imagePositiveSylow q : Subgroup (DerivedImage q)) (originalProjection_sylow_injective q)
  change ((Subgroup.center (imagePositiveSylow q)).map
      (imagePositiveSylow q : Subgroup (DerivedImage q)).subtype).map (originalProjection q)=
    centerImage ((imagePositiveSylow q : Subgroup (DerivedImage q)).map (originalProjection q)) at he
  rw [sylow_center_image] at he
  exact he.symm

private theorem conjugate_center_family_stable {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (R : Subgroup G)
    (hR : centerImage (P : Subgroup G)=R) (f : MulAut G) (g : G) :
    ∃h : G,(R.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
      R.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨h,hh⟩ := exists_inner_centerImage_map p P (f*MulAut.conj g)
  rw [hR] at hh
  refine ⟨h,?_⟩
  rw [Subgroup.map_map]
  exact hh

theorem automorphism_maps_original_conjugate_line (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (f : MulAut (CFSG.Models.TrialityD4 q)) (g : CFSG.Models.TrialityD4 q) :
    ∃h : CFSG.Models.TrialityD4 q,
      ((originalLongLine q).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
        (originalLongLine q).map (MulAut.conj h).toMonoidHom := by
  exact conjugate_center_family_stable q.prime (originalSylow q) (originalLongLine q)
    (originalSylow_centerImage q) f g

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootFamily

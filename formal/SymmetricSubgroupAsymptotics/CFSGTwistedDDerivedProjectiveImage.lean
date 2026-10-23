import SymmetricSubgroupAsymptotics.CFSGTwistedDImageParity
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots

/-! The SAME original twisted-D model is the central quotient of its
actual Derived action image. The image's noncentral witness is already
an explicit original Derived word. Only original model simplicity is
used; no simplicity or recognition of an ambient untwisted D is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedProjectiveImage

theorem derivedImageAction_eq (s : ℕ) (q : CFSG.PrimePower) :
    CFSGTwistedDDerivedPairedRoots.derivedImageAction s q =
      CFSGTwistedDFixedA2.derivedImageAction s q := by
  apply MonoidHom.ext
  intro g
  rfl

theorem imageProjective_nontrivial (s : ℕ) (q : CFSG.PrimePower) :
    Nontrivial ((CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range ⧸
      Subgroup.center (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range) := by
  rw [derivedImageAction_eq]
  let f := CFSGTwistedDFixedA2.derivedImageAction s q
  let Q := QuotientGroup.mk' (Subgroup.center f.range)
  apply nontrivial_of_ne (Q (f.rangeRestrict (CFSGTwistedDFixedA2.weylWord s q))) 1
  intro h
  exact CFSGTwistedDFixedA2.image_weyl_not_center s q ((QuotientGroup.eq_one_iff _).mp h)

def originalProjectiveImageEquiv (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    CFSG.Models.TwistedD (s + 4) q ≃*
      ((CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range ⧸
        Subgroup.center (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range) := by
  let f := CFSGTwistedDDerivedPairedRoots.derivedImageAction s q
  letI : Nontrivial (f.range ⧸ Subgroup.center f.range) := imageProjective_nontrivial s q
  change (CFSGTwistedDFixedA2.Derived s q ⧸
    Subgroup.center (CFSGTwistedDFixedA2.Derived s q)) ≃* (f.range ⧸ Subgroup.center f.range)
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    f.rangeRestrict f.rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedProjectiveImage

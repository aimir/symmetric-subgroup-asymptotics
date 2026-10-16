import SymmetricSubgroupAsymptotics.BinaryFourOriginalSourceTargetTransport
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalBottomAugmentationMaps
import SymmetricSubgroupAsymptotics.RepresentationCommonKernelSubquotient

/-! The literal-L whole-module case factors through the actual
augmentation plane, placed in the common middle active support. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

variable {G W : Type} [Group G] [AddCommGroup W] [_root_.Module Scalar W]
    (gamma : G →* SymmetricComplement)
    (hgamma : ∀ r : Complement, ∃ g : G, gamma g = SemidirectProduct.inl r)
    (L : Subrepresentation (canonicalFull.comp gamma))

def originalWholeEnvelopeMap : L.toRepresentation.IntertwiningMap
    (symmetricEnvelopeRepresentation.comp gamma) where
  toLinearMap := localMiddleInclusionLinear.comp
    (fullAugmentationLinear.comp L.toSubmodule.subtype)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change localMiddleInclusionLinear (fullAugmentationLinear (canonicalFull (gamma g) x.1)) =
      symmetricEnvelopeRepresentation (gamma g) (localMiddleInclusionLinear (fullAugmentationLinear x.1))
    have ha := Representation.IntertwiningMap.isIntertwining _ _
      canonicalAugmentationIntertwiner (gamma g) x.1
    change fullAugmentationLinear (canonicalFull (gamma g) x.1) =
      canonicalLocalRepresentation (gamma g) (fullAugmentationLinear x.1) at ha
    rw [ha]
    exact Representation.IntertwiningMap.isIntertwining _ _ canonicalLocalMiddleInclusion
      (gamma g) (fullAugmentationLinear x.1)

include hgamma

theorem originalWholeEnvelopeMap_kernel_le
    (htop : originalAmbientSource gamma L = ⊤)
    (tau : Representation Scalar G W) (f : L.toRepresentation.IntertwiningMap tau)
    (hfixed : ∀ g : G, gamma g ∈ BinaryFourSymmetricKleinNormalCover.klein →
      ∀ v : W, tau g v = v) :
    (originalWholeEnvelopeMap gamma L).ker ≤ f.ker := by
  intro x hx
  let e := originalAmbientEquiv gamma L
  have haug : fullAugmentationLinear x.1 = 0 := by
    apply canonicalLocalMiddleInclusion_injective
    simpa only [map_zero] using hx
  have hzero : ambientAugmentation (e x) = 0 := by
    change fullDecode x.1 0 + fullDecode x.1 1 + fullDecode x.1 2 + fullDecode x.1 3 = 0
    rw [fullDecode_augmentation]
    exact haug
  let u : originalAmbientSource gamma L := ⟨radicalUSource (e x), by exact htop.ge (by trivial)⟩
  let v : originalAmbientSource gamma L := ⟨radicalVSource (e x), by exact htop.ge (by trivial)⟩
  obtain ⟨gU, hgU⟩ := hgamma (SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0]))
  obtain ⟨gV, hgV⟩ := hgamma (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 1]))
  have hfixU := hfixed gU (by
    rw [hgU]
    exact (BinaryFourSymmetricKleinNormalCover.mem_klein _).mpr ⟨rfl, rfl⟩)
  have hfixV := hfixed gV (by
    rw [hgV]
    exact (BinaryFourSymmetricKleinNormalCover.mem_klein _).mpr ⟨rfl, rfl⟩)
  have hdecomp : x =
      (L.toRepresentation gU (e.symm u) - e.symm u) +
      (L.toRepresentation gV (e.symm v) - e.symm v) := by
    apply e.injective
    rw [map_add,
      originalAmbientEquiv_differenceU gamma hgamma L gU hgU,
      originalAmbientEquiv_differenceV gamma hgamma L gV hgV,
      e.apply_symm_apply, e.apply_symm_apply]
    apply Subtype.ext
    exact radical_difference_decomposition (e x) hzero
  change f x = 0
  rw [hdecomp, map_add, map_sub, map_sub,
    Representation.IntertwiningMap.isIntertwining,
    Representation.IntertwiningMap.isIntertwining, hfixU, hfixV, sub_self, sub_self, add_zero]

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end

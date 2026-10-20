import SymmetricSubgroupAsymptotics.BinaryFourOriginalSourceTargetTransport
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalRadicalEnvelopeProjection
import SymmetricSubgroupAsymptotics.RepresentationCommonKernelSubquotient

/-! The proper nonbottom literal-L case: its actual target is a
subquotient of the four middle positions in the common S4 envelope. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

variable {G W : Type} [Group G] [AddCommGroup W] [_root_.Module Scalar W]
    (gamma : G →* SymmetricComplement) (hgamma : ∀ r : Complement, ∃ g : G, gamma g = SemidirectProduct.inl r)
    (L : Subrepresentation (canonicalFull.comp gamma))

include hgamma

private theorem original_source_radical_include
    (hproper : originalAmbientSource gamma L ≠ ⊤) (x : L.toSubmodule) :
    x.1 = includeAugmentation (head x.1) := by
  have hrad := proper_submodule_le_augmentation_kernel (originalAmbientSource gamma L)
    hproper (originalAmbientSource_differenceU gamma hgamma L)
    (originalAmbientSource_differenceV gamma hgamma L)
    (originalAmbientSource_cycle gamma hgamma L)
  have hx := hrad (originalAmbientEquiv gamma L x).2
  change ambientAugmentation (fullChart x.1) = 0 at hx
  change fullDecode x.1 0 + fullDecode x.1 1 + fullDecode x.1 2 + fullDecode x.1 3 = 0 at hx
  rw [fullDecode_augmentation] at hx
  have h6 : x.1 6 = 0 := congrFun hx 0
  have h7 : x.1 7 = 0 := congrFun hx 1
  ext i
  fin_cases i <;> first | rfl | exact h6 | exact h7

def originalProperMiddleMap
    (hproper : originalAmbientSource gamma L ≠ ⊤) :
    L.toRepresentation.IntertwiningMap (symmetricEnvelopeRepresentation.comp gamma) where
  toLinearMap := radicalEnvelopeProjection.comp L.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change radicalEnvelopeProjection (canonicalFull (gamma g) x.1) =
      symmetricEnvelopeRepresentation (gamma g) (radicalEnvelopeProjection x.1)
    rw [original_source_radical_include gamma hgamma L hproper x]
    exact LinearMap.congr_fun
      (radicalEnvelopeProjection_intertwining_on_radical (gamma g)) (head x.1)

theorem originalProperMiddleMap_kernel_le
    (hproper : originalAmbientSource gamma L ≠ ⊤)
    (w : Module) (hw : w ∈ originalAmbientSource gamma L)
    (hnotbottom : ¬ ∃ a : Local, w = diagonal a)
    (tau : Representation Scalar G W) (f : L.toRepresentation.IntertwiningMap tau)
    (hfixed : ∀ g : G, gamma g ∈ BinaryFourSymmetricKleinNormalCover.klein →
      ∀ v : W, tau g v = v) :
    (originalProperMiddleMap gamma hgamma L hproper).ker ≤ f.ker := by
  intro x hx
  have hproj : middleProjection (head x.1) = 0 := by
    have identity : ∀ y : FullCoordinates, radicalEnvelopeProjection y = 0 ↔
        middleProjection (head y) = 0 := by decide +kernel
    exact (identity x.1).mp hx
  have hencode : encode (fullChart x.1) = head x.1 := by
    exact congrArg head (fullEncode_fullDecode x.1)
  have hm : originalAmbientEquiv gamma L x ∈
      LinearMap.ker (submoduleMiddleMap (originalAmbientSource gamma L)) := by
    change middleProjection (encode (fullChart x.1)) = 0
    rw [hencode]
    exact hproj
  have hkill := originalAmbientTargetMap_middle_kernel gamma hgamma L tau f
    hproper w hw hnotbottom hfixed hm
  change f ((originalAmbientEquiv gamma L).symm (originalAmbientEquiv gamma L x)) = 0 at hkill
  rw [LinearEquiv.symm_apply_apply] at hkill
  exact hkill

/-- The literal quotient source embeds in the common envelope and still
maps onto the unchanged original target. -/
theorem originalProperMiddle_target_subquotient
    (hproper : originalAmbientSource gamma L ≠ ⊤)
    (w : Module) (hw : w ∈ originalAmbientSource gamma L)
    (hnotbottom : ¬ ∃ a : Local, w = diagonal a)
    (tau : Representation Scalar G W) (f : L.toRepresentation.IntertwiningMap tau)
    (hf : Function.Surjective f)
    (hfixed : ∀ g : G, gamma g ∈ BinaryFourSymmetricKleinNormalCover.klein →
      ∀ v : W, tau g v = v) :
    let m := originalProperMiddleMap gamma hgamma L hproper
    ∃ q : (intertwinerKernelQuotient L.toRepresentation
        (symmetricEnvelopeRepresentation.comp gamma) m).IntertwiningMap tau,
      Function.Surjective q := by
  let m := originalProperMiddleMap gamma hgamma L hproper
  have hk := originalProperMiddleMap_kernel_le gamma hgamma L hproper w hw hnotbottom tau f hfixed
  exact ⟨intertwinerKernelQuotientMap _ _ m tau f hk,
    intertwinerKernelQuotientMap_surjective _ _ m tau f hk hf⟩

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end

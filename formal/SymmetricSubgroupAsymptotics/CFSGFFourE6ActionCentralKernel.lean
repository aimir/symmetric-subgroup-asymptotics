import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedGeneratedGroup
import SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeActionImages
import SymmetricSubgroupAsymptotics.CFSGE6GeckOpposedImageKernel

/-! The SAME original F4 restricted action has central kernel. The
literal folded matrix group is identified with the actual fixed-root
generated subgroup. Its positive action is injective and its two
opposed action images are disjoint; the actual Weyl-witness theorem
then recognizes a central kernel. Full ambient E6 faithfulness is not
assumed or specialized to the restricted representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ActionCentralKernel
open CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow
open CFSGFFourE6FixedGeneratedGroup CFSGFFourE6OppositeActionImages
open CFSGFFourE6PositiveCartanKernel CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGSerreQuadraticMatrix

theorem foldedToImage_kernel_le_center (K : Type) [Field K] [Finite K] :
    (foldedToImage K).ker ≤ Subgroup.center (canonicalElementaryGroup realizationData K) := by
  let e := MulEquiv.subgroupCongr (fixedRootGenerated_eq_folded K)
  let f := (foldedToImage K).comp e.toMonoidHom
  have hinj : Set.InjOn f (rootPart K (RingEquiv.refl K) false :
      Set (fixedRootGenerated K (RingEquiv.refl K))) := by
    intro a ha b hb he
    have hact : fullNaturalImageAction K (e a) = fullNaturalImageAction K (e b) :=
      congrArg (fun z : imageGroup K => z.val) he
    have hker : (e a)⁻¹ * e b ∈ (fullNaturalImageAction K).ker := by
      change fullNaturalImageAction K ((e a)⁻¹ * e b) = 1
      rw [map_mul, map_inv, hact, inv_mul_cancel]
    have hpos : ((e a)⁻¹ * e b).val ∈ CFSGTwistedE6GeckPositiveTwist.Positive K :=
      (CFSGTwistedE6GeckPositiveTwist.Positive K).mul_mem
        ((CFSGTwistedE6GeckPositiveTwist.Positive K).inv_mem ha.1) hb.1
    have hzero := image_kernel_eq_one_of_positive K ((e a)⁻¹ * e b) hker hpos
    exact e.injective (inv_mul_eq_one.mp hzero)
  have hpos : (rootPart K (RingEquiv.refl K) false).map f ≤
      (positivePart K).map (foldedToImage K) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨e a, ha.1, rfl⟩
  have hneg : (rootPart K (RingEquiv.refl K) true).map f ≤
      (negativePart K).map (foldedToImage K) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨e a, ha.1, rfl⟩
  have hdisjoint : (rootPart K (RingEquiv.refl K) false).map f ⊓
      (rootPart K (RingEquiv.refl K) true).map f = ⊥ :=
    le_antisymm ((inf_le_inf hpos hneg).trans
      (le_of_eq (opposite_action_images_disjoint K))) bot_le
  have hcentral := CFSGE6GeckOpposedImageKernel.kernel_le_center K (RingEquiv.refl K)
    f hinj hdisjoint
  intro g hg
  let j := e.symm g
  have hj : j ∈ f.ker := by
    change foldedToImage K (e (e.symm g)) = 1
    rw [e.apply_symm_apply]
    exact hg
  apply Subgroup.mem_center_iff.mpr
  intro h
  have he := congrArg e (Subgroup.mem_center_iff.mp (hcentral hj) (e.symm h))
  simpa only [map_mul, e.apply_symm_apply] using he

theorem fullNaturalImageAction_kernel_le_center (K : Type) [Field K] [Finite K] :
    (fullNaturalImageAction K).ker ≤
      Subgroup.center (canonicalElementaryGroup realizationData K) := by
  intro g hg
  apply foldedToImage_kernel_le_center K
  apply Subtype.ext
  exact hg

end SymmetricSubgroupAsymptotics.CFSGFFourE6ActionCentralKernel

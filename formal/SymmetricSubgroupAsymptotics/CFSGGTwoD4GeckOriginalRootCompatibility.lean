import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRootUnits

/-! The actual folded signed charts project to the literal ORIGINAL G2
root classes. This is a commuting source-root/projective diagram on the
same original tensor action, not a lift of arbitrary original Aut and
not an adjoint-D4 to natural-SO8 homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalRootCompatibility
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckSimpleParameters CFSGGTwoD4GeckImageRealization
open CFSGGTwoD4GeckGeneratedGroup CFSGGTwoD4GeckImageSylows CFSGGTwoD4GeckRootUnits
open CFSGTrialityGeckFixedRootWords CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K]

theorem sourceToImage_simple_root (neg a : Bool) (t : K) :
    sourceToImage K (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.G₂ K neg
      (if a then 1 else 0) t)=generatedToImage K
        (simpleGeneratedHom K neg a (Multiplicative.ofAdd t)) := by
  apply Subtype.ext
  change sourceImageRepresentation K (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.G₂ K neg
    (if a then 1 else 0) t)=generatedImageAction K (simpleGeneratedHom K neg a (Multiplicative.ofAdd t))
  rw [source_root_action]
  change foldedImageAction K (foldedRoot K neg (if a then 1 else 0) t)=
    foldedImageAction K (generatedEquiv K (simpleGeneratedHom K neg a (Multiplicative.ofAdd t)))
  apply congrArg (foldedImageAction K)
  apply Subtype.ext
  rw [generatedEquiv_val]
  change rootUnit K neg (if a then 1 else 0) t=(simpleGeneratedHom K neg a (Multiplicative.ofAdd t)).val
  rw [simpleGeneratedHom_val]
  cases a <;> rfl

theorem originalProjectiveImageEquiv_mk [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (x : Model CartanMatrix.G₂ K) :
    originalProjectiveImageEquiv K ((QuotientGroup.mk' (Subgroup.center (Model CartanMatrix.G₂ K))) x)=
      (QuotientGroup.mk' (Subgroup.center (imageGroup K))) (sourceToImage K x) := rfl

theorem originalSimpleHom_eq_modelRoot [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (neg a : Bool) (t : K) :
    originalSimpleHom K neg a (Multiplicative.ofAdd t)=
      (QuotientGroup.mk' (Subgroup.center (Model CartanMatrix.G₂ K)))
        (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.G₂ K neg (if a then 1 else 0) t) := by
  apply (originalProjectiveImageEquiv K).injective
  calc
    _=(QuotientGroup.mk' (Subgroup.center (imageGroup K)))
        (generatedToImage K (simpleGeneratedHom K neg a (Multiplicative.ofAdd t))) := by
      change originalProjectiveImageEquiv K
        ((originalProjectiveImageEquiv K).symm
          ((QuotientGroup.mk' (Subgroup.center (imageGroup K)))
            (generatedToImage K (simpleGeneratedHom K neg a (Multiplicative.ofAdd t)))))=_
      exact (originalProjectiveImageEquiv K).apply_symm_apply _
    _=(QuotientGroup.mk' (Subgroup.center (imageGroup K)))
        (sourceToImage K (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.G₂ K neg
          (if a then 1 else 0) t)) :=
      congrArg (QuotientGroup.mk' (Subgroup.center (imageGroup K))) (sourceToImage_simple_root K neg a t).symm
    _=_ := (originalProjectiveImageEquiv_mk K _).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalRootCompatibility

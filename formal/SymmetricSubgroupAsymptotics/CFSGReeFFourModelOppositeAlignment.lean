import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeStability
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedBruhatOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGSubgroupOppositeAlignmentRestriction

/-! Ordinary positive/opposite alignment in the same original F4 Model,
without passing to its projective quotient or assuming its simplicity.
The unconditional original-to-folded equivalence supplies exactly the
identity-coefficient diagram-fixed positives required by the checked
E6 alignment theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourModelOppositeAlignment
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalAmbientHom
open CFSGFFourOriginalGeneratedEquivalence CFSGReeFFourOriginalNegativeStability
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckFixedBruhatOppositeAlignment CFSGSubgroupOppositeAlignmentRestriction

private theorem rawHom_diagram_fixed (m : ℕ) (g : Model CartanMatrix.F₄ (Field m)) :
    unitTwist (Field m) (RingEquiv.refl (Field m)) (rawHom (Field m) g)=rawHom (Field m) g := by
  have hg : rawHom (Field m) g∈fixedRootGenerated (Field m) (RingEquiv.refl (Field m)) :=
    (modelEquivGenerated (Field m) g).property
  exact fixedRootGenerated_le_fixed (Field m) (RingEquiv.refl (Field m)) hg

theorem modelPositive_raw_image (m : ℕ) :
    (modelPositive (Field m)).map (rawHom (Field m))=
      signedFixed (Field m) (RingEquiv.refl (Field m)) false := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact ⟨hg,rawHom_diagram_fixed m g⟩
  · intro y hy
    let Y : fixedRootGenerated (Field m) (RingEquiv.refl (Field m)) :=
      ⟨y,signedFixed_le_generated (Field m) (RingEquiv.refl (Field m)) false hy⟩
    let g := (modelEquivGenerated (Field m)).symm Y
    have he : rawHom (Field m) g=y := congrArg
      (fun z : fixedRootGenerated (Field m) (RingEquiv.refl (Field m))=>z.val)
      ((modelEquivGenerated (Field m)).apply_symm_apply Y)
    have hg : g∈modelPositive (Field m) := by
      change rawHom (Field m) g∈Positive (Field m)
      rw [he]
      exact hy.1
    exact ⟨g,hg,he⟩

theorem modelNegative_eq_fixed_comap (m : ℕ) :
    modelNegative m=(signedFixed (Field m) (RingEquiv.refl (Field m)) true).comap
      (rawHom (Field m)) := by
  ext g
  constructor
  · intro hg
    exact ⟨hg,rawHom_diagram_fixed m g⟩
  · exact fun hg=>hg.1

theorem model_opposite_conjugate_by_positive (m : ℕ)
    (g : Model CartanMatrix.F₄ (Field m))
    (hdisj : modelPositive (Field m)⊓(modelPositive (Field m)).map
      (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈modelPositive (Field m),(modelPositive (Field m)).map (MulAut.conj g).toMonoidHom=
      (modelNegative m).map (MulAut.conj b).toMonoidHom := by
  have h := restrict_alignment (rawHom (Field m)) (rawHom_injective (Field m))
    (modelPositive (Field m)) (signedFixed (Field m) (RingEquiv.refl (Field m)) false)
    (signedFixed (Field m) (RingEquiv.refl (Field m)) true) (modelPositive_raw_image m) (by
      intro a ha
      exact fixed_opposite_conjugate_by_positive (Field m) (RingEquiv.refl (Field m))
        (rawHom (Field m) a) (modelAmbientHom (Field m) a).property
        (rawHom_diagram_fixed m a) ha) g hdisj
  rw [←modelNegative_eq_fixed_comap] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourModelOppositeAlignment

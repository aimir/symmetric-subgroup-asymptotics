import SymmetricSubgroupAsymptotics.CFSGFFourOriginalBruhatCells

/-! The exact positive image of the same original characteristic-two F4
Model is the diagram-fixed ambient E6 positive group. Lifts are built
using the proved original/generated equivalence and actual fixed-positive
membership; no ordinary F4 simplicity or fixed-point exactness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage
open CFSG.Models.Chevalley CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalGeneratedEquivalence CFSGFFourOriginalAmbientHom
open CFSGFFourOriginalBruhatCells CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem rawHom_diagram_fixed (g : Model CartanMatrix.F₄ K) :
    unitTwist K (RingEquiv.refl K) (rawHom K g)=rawHom K g := by
  have h := fixedRootGenerated_le_fixed K (RingEquiv.refl K) (modelEquivGenerated K g).property
  change unitTwist K (RingEquiv.refl K) (modelEquivGenerated K g).val=
    (modelEquivGenerated K g).val at h
  simpa only [modelEquivGenerated_val] using h

theorem exists_modelPositive_of_diagram_fixed (u : (Matrix GeckIndex GeckIndex K)ˣ)
    (hu : u∈Positive K) (hfix : unitTwist K (RingEquiv.refl K) u=u) :
    ∃g∈modelPositive K,rawHom K g=u := by
  let x : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨u,signedFixed_le_generated K (RingEquiv.refl K) false ⟨hu,hfix⟩⟩
  have hraw : rawHom K ((modelEquivGenerated K).symm x)=u := rawHom_generated_inverse K x
  refine ⟨(modelEquivGenerated K).symm x,?_,hraw⟩
  change rawHom K ((modelEquivGenerated K).symm x)∈Positive K
  rw [hraw]
  exact hu

theorem modelPositive_image_eq_signedFixed :
    (modelPositive K).map (rawHom K)=signedFixed K (RingEquiv.refl K) false := by
  ext u
  constructor
  · rintro ⟨g,hg,rfl⟩
    change rawHom K g∈Positive K at hg
    exact ⟨hg,rawHom_diagram_fixed K g⟩
  · rintro ⟨hu,hfix⟩
    obtain ⟨g,hg,he⟩ := exists_modelPositive_of_diagram_fixed K u hu hfix
    exact ⟨g,hg,he⟩

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage

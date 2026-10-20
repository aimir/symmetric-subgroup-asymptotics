import SymmetricSubgroupAsymptotics.BinaryFourOriginalBottomEnvelopeMap
import SymmetricSubgroupAsymptotics.BinaryFourOriginalProperMiddleSubquotient
import SymmetricSubgroupAsymptotics.BinaryFourOriginalWholeEnvelopeMap

/-! One actual middle-supported source for every Klein-trivial quotient
of a literal original invariant L. The source is constructed by the three
Loewy cases; no split extension or capacity premise is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

structure OriginalMiddleSource {G W : Type} [Group G]
    [AddCommGroup W] [_root_.Module Scalar W]
    (gamma : G →* SymmetricComplement) (tau : Representation Scalar G W) where
  Source : Type
  [sourceAdd : AddCommGroup Source]
  [sourceModule : _root_.Module Scalar Source]
  sourceRepresentation : Representation Scalar G Source
  embedding : sourceRepresentation.IntertwiningMap (symmetricEnvelopeRepresentation.comp gamma)
  embedding_injective : Function.Injective embedding
  targetMap : sourceRepresentation.IntertwiningMap tau
  targetMap_surjective : Function.Surjective targetMap
  middle_support : ∀ x : Source, (embedding x).1 2 = 0 ∧ (embedding x).2.2 = 0

attribute [instance] OriginalMiddleSource.sourceAdd OriginalMiddleSource.sourceModule

variable {G W : Type} [Group G] [AddCommGroup W] [_root_.Module Scalar W]
    (gamma : G →* SymmetricComplement)
    (hgamma : ∀ r : Complement, ∃ g : G, gamma g = SemidirectProduct.inl r)
    (L : Subrepresentation (canonicalFull.comp gamma))
    (tau : Representation Scalar G W) (f : L.toRepresentation.IntertwiningMap tau)
    (hf : Function.Surjective f)
    (hfixed : ∀ g : G, gamma g ∈ BinaryFourSymmetricKleinNormalCover.klein →
      ∀ v : W, tau g v = v)

include hgamma L f hf hfixed

theorem originalMiddleSource_exists : Nonempty (OriginalMiddleSource gamma tau) := by
  classical
  by_cases hbottom : ∀ x : L.toSubmodule, ∃ a : Local, fullChart x.1 = diagonal a
  · exact ⟨{
      Source := L.toSubmodule
      sourceRepresentation := L.toRepresentation
      embedding := originalBottomEnvelopeMap gamma L hbottom
      embedding_injective := originalBottomEnvelopeMap_injective gamma L hbottom
      targetMap := f
      targetMap_surjective := hf
      middle_support := by intro x; exact ⟨rfl, rfl⟩ }⟩
  by_cases htop : originalAmbientSource gamma L = ⊤
  · let m := originalWholeEnvelopeMap gamma L
    have hk := originalWholeEnvelopeMap_kernel_le gamma hgamma L htop tau f hfixed
    let sigma := intertwinerKernelQuotient L.toRepresentation
      (symmetricEnvelopeRepresentation.comp gamma) m
    let i := intertwinerKernelQuotientEmbedding L.toRepresentation
      (symmetricEnvelopeRepresentation.comp gamma) m
    let q := intertwinerKernelQuotientMap L.toRepresentation
      (symmetricEnvelopeRepresentation.comp gamma) m tau f hk
    exact ⟨{
      Source := L.toSubmodule ⧸ m.ker.toSubmodule
      sourceRepresentation := sigma
      embedding := i
      embedding_injective := intertwinerKernelQuotientEmbedding_injective _ _ m
      targetMap := q
      targetMap_surjective := intertwinerKernelQuotientMap_surjective _ _ m tau f hk hf
      middle_support := by
        intro y
        obtain ⟨x, rfl⟩ := m.ker.toSubmodule.mkQ_surjective y
        exact ⟨rfl, rfl⟩ }⟩
  · push_neg at hbottom
    obtain ⟨x, hx⟩ := hbottom
    let w : Module := fullChart x.1
    have hw : w ∈ originalAmbientSource gamma L := (originalAmbientEquiv gamma L x).2
    have hnot : ¬ ∃ a : Local, w = diagonal a := by
      rintro ⟨a, ha⟩
      exact hx a ha
    let m := originalProperMiddleMap gamma hgamma L htop
    have hk := originalProperMiddleMap_kernel_le gamma hgamma L htop w hw hnot tau f hfixed
    let sigma := intertwinerKernelQuotient L.toRepresentation
      (symmetricEnvelopeRepresentation.comp gamma) m
    let i := intertwinerKernelQuotientEmbedding L.toRepresentation
      (symmetricEnvelopeRepresentation.comp gamma) m
    let q := intertwinerKernelQuotientMap L.toRepresentation
      (symmetricEnvelopeRepresentation.comp gamma) m tau f hk
    exact ⟨{
      Source := L.toSubmodule ⧸ m.ker.toSubmodule
      sourceRepresentation := sigma
      embedding := i
      embedding_injective := intertwinerKernelQuotientEmbedding_injective _ _ m
      targetMap := q
      targetMap_surjective := intertwinerKernelQuotientMap_surjective _ _ m tau f hk hf
      middle_support := by
        intro y
        obtain ⟨z, rfl⟩ := m.ker.toSubmodule.mkQ_surjective y
        exact ⟨rfl, rfl⟩ }⟩

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end

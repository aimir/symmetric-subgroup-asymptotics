import SymmetricSubgroupAsymptotics.CFSGFFourE6SignedFixedInclusion
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedBruhatOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGSubgroupOppositeAlignmentRestriction
import SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment

/-! Actual opposite alignment for the SAME original simple F4 model.
The folded positive Sylow covers all identity-coefficient fixed U;
the literal fixed negative target lies in the folded matrix group.
Descent uses the checked positive restriction, never an Aut lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6SignedFixedInclusion CFSGFFourE6FixedPositiveProjection
open CFSGFFourE6OriginalProjection CFSGFFourE6PositiveSylow CFSGFFourE6DiagramFixed
open CFSGFFourE6RootSubgroups CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow
open CFSGFFourE6PositiveActionInjective CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedBruhatOppositeAlignment CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckPositiveTwist CFSGSubgroupOppositeAlignmentRestriction
open CFSGQuotientOppositeAlignment CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

def signedFixedToOriginal (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (neg : Bool) :
    signedFixed K (RingEquiv.refl K) neg→*Projective CartanMatrix.F₄ K :=
  (foldedToOriginal K).comp (signedFixedToFolded K neg)

def negativeInFolded (K : Type) [Field K] :
    Subgroup (canonicalElementaryGroup realizationData K) :=
  (signedFixed K (RingEquiv.refl K) true).subgroupOf (canonicalElementaryGroup realizationData K)

def originalNegative (K : Type) [Field K] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Subgroup (Projective CartanMatrix.F₄ K) := (negativeInFolded K).map (foldedToOriginal K)

theorem positiveSylow_raw_image (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
      (canonicalElementaryGroup realizationData K).subtype=signedFixed K (RingEquiv.refl K) false := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(le_of_eq (positiveSylow_coe K p)) hu,foldedModel_le_diagramFixed K u.property⟩
  · intro hx
    let u := fixedPositiveToSylow K p ⟨x,hx⟩
    exact ⟨u.val,u.property,rfl⟩

theorem folded_opposite_conjugate_by_positive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (g : canonicalElementaryGroup realizationData K)
    (hdisj : (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K))⊓
      (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
        (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)),
      (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
        (MulAut.conj g).toMonoidHom=(negativeInFolded K).map (MulAut.conj b).toMonoidHom := by
  apply restrict_alignment (canonicalElementaryGroup realizationData K).subtype Subtype.val_injective
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K))
    (signedFixed K (RingEquiv.refl K) false) (signedFixed K (RingEquiv.refl K) true)
    (positiveSylow_raw_image K p) ?_ g hdisj
  intro a ha
  exact fixed_opposite_conjugate_by_positive K (RingEquiv.refl K) a.val
    (foldedModel_le_ambient K a.property) (foldedModel_le_diagramFixed K a.property) ha

theorem positiveSylow_original_image (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
      (foldedToOriginal K)=(originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := by
  change (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
    ((imageToOriginal K).comp (foldedToImage K))=
      ((positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
        (foldedToImage K)).map (imageToOriginal K)
  rw [Subgroup.map_map]

theorem original_opposite_conjugate_by_positive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (g : Projective CartanMatrix.F₄ K)
    (hdisj : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))⊓
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map
        (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)),
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map
        (MulAut.conj g).toMonoidHom=(originalNegative K).map (MulAut.conj b).toMonoidHom := by
  have h := opposite_alignment_map (foldedToOriginal K) (foldedToOriginal_surjective K)
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K))
    (negativeInFolded K) (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K))
    (foldedPositiveToOriginal_injective K p) (folded_opposite_conjugate_by_positive K p) g
  rw [positiveSylow_original_image] at h
  exact h hdisj

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeAlignment

import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootSections
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords

/-! The constructed relative source section has exactly its displayed
root label and diagram-partner label. Fixedness of its chosen simple seed
is equivalent to fixedness of the actual root, proved from the original
integral Weyl action; no relative-root classification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionDiagramLabels
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckColumns CFSGNormTwoCoordinateDiagramIndices CFSGNormTwoCartanDiagramWords
open CFSGSerreDiagram CFSGNormTwoCartanDiagramRoots

theorem section_simple_image (k : PositiveRoot) :
    rootAction (expandRelative (sectionRelative k)) k.val=
      negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index (sectionNode k)) := by
  let W := linearAction (expandRelative (sectionRelative k))
  have hd := section_degree k
  rw [wordLinear_inverseWord] at hd
  change W.symm (-(E6Index (sectionNode k):Roots CartanMatrix.E₆).val)=k.val.val at hd
  have hl : W k.val.val= -(E6Index (sectionNode k):Roots CartanMatrix.E₆).val := by
    rw [←hd,W.apply_symm_apply]
  change wordRoot CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
    (expandRelative (sectionRelative k)) k.val=_
  apply Subtype.ext
  rw [←wordLinear_root,negative_val]
  exact hl

theorem section_partner_image (k : PositiveRoot) :
    rootAction (expandRelative (sectionRelative k)) (diagramRoot k.val)=
      negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        (E6Index (e6Permutation (sectionNode k))) := by
  have he := relative_root_action_commutes (sectionRelative k) k.val
  rw [section_simple_image] at he
  have hs : diagramRoot (E6Index (sectionNode k))=E6Index (e6Permutation (sectionNode k)) :=
    simple_rootPermutation CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation e6_preserves (sectionNode k)
  change rootPermutation CartanMatrix.E₆ e6Permutation e6_preserves (E6Index (sectionNode k))=
    E6Index (e6Permutation (sectionNode k)) at hs
  change rootPermutation CartanMatrix.E₆ e6Permutation e6_preserves
    (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index (sectionNode k)))=
      rootAction (expandRelative (sectionRelative k)) (diagramRoot k.val) at he
  rw [rootPermutation_negative,hs] at he
  exact he.symm

theorem section_seed_fixed_iff (k : PositiveRoot) :
    CFSG.Models.e6Twist (sectionNode k)=sectionNode k ↔ diagramRoot k.val=k.val := by
  constructor
  · intro hj
    change e6Permutation (sectionNode k)=sectionNode k at hj
    apply Subtype.ext
    apply (linearAction (expandRelative (sectionRelative k))).injective
    rw [wordLinear_root,wordLinear_root]
    change (rootAction (expandRelative (sectionRelative k)) (diagramRoot k.val)).val=
      (rootAction (expandRelative (sectionRelative k)) k.val).val
    rw [section_partner_image,section_simple_image,hj]
  · intro hk
    have he := section_partner_image k
    rw [hk,section_simple_image] at he
    have hv := congrArg Subtype.val he
    rw [negative_val,negative_val] at hv
    have hroots : (E6Index (sectionNode k):Roots CartanMatrix.E₆)=
        (E6Index (e6Permutation (sectionNode k)):Roots CartanMatrix.E₆) :=
      Subtype.ext (neg_injective hv)
    change coordinateRoot CartanMatrix.E₆ CartanMatrix.E₆_diag (sectionNode k)=
      coordinateRoot CartanMatrix.E₆ CartanMatrix.E₆_diag (e6Permutation (sectionNode k)) at hroots
    exact (coordinateRoot_injective CartanMatrix.E₆ CartanMatrix.E₆_diag hroots).symm

theorem section_partner_degree (k : PositiveRoot) :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      (CFSGNormTwoGeckWeylWordAlgebra.inverseWord (expandRelative (sectionRelative k)))
      (-(E6Index (e6Permutation (sectionNode k)):Roots CartanMatrix.E₆).val)=(diagramRoot k.val).val := by
  have hl : linearAction (expandRelative (sectionRelative k)) (diagramRoot k.val).val=
      -(E6Index (e6Permutation (sectionNode k)):Roots CartanMatrix.E₆).val := by
    rw [wordLinear_root]
    change (rootAction (expandRelative (sectionRelative k)) (diagramRoot k.val)).val=_
    rw [section_partner_image,negative_val]
  rw [wordLinear_inverseWord,←hl]
  exact (linearAction (expandRelative (sectionRelative k))).symm_apply_apply _

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionDiagramLabels

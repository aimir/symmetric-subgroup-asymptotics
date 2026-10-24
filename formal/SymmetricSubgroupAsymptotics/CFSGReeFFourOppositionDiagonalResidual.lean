import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionWordAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection

/-! Equal lattice actions leave a genuine diagonal residual in the SAME
original fixed Model. In particular opposition need only commute with
each relative reflection modulo that actual diagonal subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionDiagonalResidual
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedBruhatCover CFSGReeFFourMinimalParabolics
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourRelativeOpposition
open CFSGReeFFourOppositionWordAction CFSGReeFFourRelativeOppositionLattice
open CFSGReeFFourOriginalWeylWords CFSGReeFFourFixedWordClassification
open CFSGReeFFourPairedWordActions CFSGReeFFourPairedModelWords
open CFSGReeFFourPairedDescentPrefixes CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6WeylChamber

theorem simpleWeyl_val_modelWord (m : ℕ) (b : Bool) :
    (simpleWeyl m b).val=modelWeylWord (Field m) (pairedRelativeWord b) := by
  change modelWeylWord (Field m) (expandPaired [b])=_
  simp only [expandPaired,List.append_nil]

theorem opposition_square_mem_diagonal (m : ℕ) :
    oppositionFixed m*oppositionFixed m∈fixedDiagonal m := by
  have he : linearAction (expandRelative (oppositionRelativeWord++oppositionRelativeWord))=
      linearAction (expandRelative []) := by
    rw [expandRelative_append,expand_oppositionRelativeWord,linearAction_append]
    exact opposition_linear_square
  have hr := equal_action_model_residual_mem (Field m)
    (oppositionRelativeWord++oppositionRelativeWord) [] he
  rw [modelWeylWord_append,modelWeylWord_oppositionRelativeWord] at hr
  change relativeOpposition m*relativeOpposition m∈CFSGFFourOriginalBruhatCells.modelDiagonalPart (Field m)
  simpa only [modelWeylWord,inv_one,mul_one] using hr

theorem opposition_simple_residual_mem_diagonal (m : ℕ) (b : Bool) :
    oppositionFixed m*simpleWeyl m b*(oppositionFixed m)⁻¹*(simpleWeyl m b)⁻¹∈fixedDiagonal m := by
  have he : linearAction (expandRelative (oppositionRelativeWord++pairedRelativeWord b))=
      linearAction (expandRelative (pairedRelativeWord b++oppositionRelativeWord)) := by
    simp only [expandRelative_append,expand_oppositionRelativeWord,
      expand_pairedRelativeWord,linearAction_append]
    exact opposition_simple_linear_commute b
  have hr := equal_action_model_residual_mem (Field m)
    (oppositionRelativeWord++pairedRelativeWord b)
    (pairedRelativeWord b++oppositionRelativeWord) he
  rw [modelWeylWord_append,modelWeylWord_append,
    modelWeylWord_oppositionRelativeWord,←simpleWeyl_val_modelWord] at hr
  change relativeOpposition m*(simpleWeyl m b).val*(relativeOpposition m)⁻¹*
    ((simpleWeyl m b).val)⁻¹∈CFSGFFourOriginalBruhatCells.modelDiagonalPart (Field m)
  simpa only [mul_inv_rev,mul_assoc] using hr

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionDiagonalResidual

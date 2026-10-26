import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareOriginalWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute
import SymmetricSubgroupAsymptotics.CFSGReeFFourWholeOuterMiddleRelation

/-! The actual middle four-cycle commutes with the negative outer
root. The proof uses twelve selected E6 root pairings, all zero or one,
and the existing integral root-word transport. It applies at every Ree
parameter and introduces no simplicity or matrix-faithfulness premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeOuterCommute
open CFSGReeFFourMiddleSquareOriginalWords CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleSquareBracketRootRelations CFSGReeFFourMiddleSquareBracketRootData
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourInversionSuffixSignPilot
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckColumns CFSGFFourE6PositiveRootUnits
open CFSGNormTwoCoordinateRootPairCommute CFSGNormTwoCoordinateSelectedRootElement
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGIntegerMatrixPairing
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourOuterFixedRoot CFSGFFourOriginalMiddleWords CFSGFFourE6FixedGeneratedGroup
open CFSGReeFFourWholeOuterMiddleRelation
open CFSGReeFFourMiddleDerivedFiveWord CFSGTwistedE6GeckDiagramCovariance
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev negSimple (i : Fin 6) := negativeIndex A hs hp (E6Index i)
private def outerNode : Fin 3 → Fin 6 := ![0,5,1]

private theorem outer_degree (i : Fin 3) :
    vectorWord [0,5,1] (Pi.single (outerNode i) (1 : ℤ))=
      (negSimple (outerNode i)).val := by
  rw [negative_val]
  fin_cases i <;> decide +kernel

private theorem negative_pairings (i : Fin 4) (j : Fin 3) :
    integerPairing A (yRoot i).val (negSimple (outerNode j)).val=0 ∨
      integerPairing A (yRoot i).val (negSimple (outerNode j)).val=1 := by
  rw [negative_val]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem negative_word (K : Type) [CommRing K] [CharP K 2] (i : Fin 3) :
    canonicalWord e6Data K [0,5,1]*canonicalRoot e6Data K false (outerNode i) 1*
      (canonicalWord e6Data K [0,5,1])⁻¹=
        selectedRootElement A hd hs hp ho K (negSimple (outerNode i)) 1 :=
  word_simple_one K [0,5,1] (outerNode i) _ (outer_degree i)

private theorem raw_outer (m : ℕ) : fixedRawHom m (outerInvolution m)=
    canonicalRoot e6Data (Field m) false 0 1*canonicalRoot e6Data (Field m) false 5 1*
      canonicalRoot e6Data (Field m) false 1 1 := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (CFSGReeFFourOuterFixedRoot.outerWord m 1)=_
  simp only [CFSGReeFFourOuterFixedRoot.outerWord,map_mul,rawHom_root,map_one,
    folded_root_eq_orbitParameter]
  rfl

private theorem raw_weyl (m : ℕ) : fixedRawHom m (outerFixedWeyl m)=
    canonicalWord e6Data (Field m) [0,5,1] := by
  rw [fixedRawHom_apply]
  exact rawHom_outerRelativeWeyl m

def negativeOuter (m : ℕ) : originalModelFixed m :=
  outerFixedWeyl m*outerInvolution m*(outerFixedWeyl m)⁻¹

private theorem raw_negativeOuter (m : ℕ) : fixedRawHom m (negativeOuter m)=
    selectedRootElement A hd hs hp ho (Field m) (negSimple 0) 1*
      selectedRootElement A hd hs hp ho (Field m) (negSimple 5) 1*
      selectedRootElement A hd hs hp ho (Field m) (negSimple 1) 1 := by
  rw [negativeOuter,map_mul,map_mul,map_inv,raw_weyl,raw_outer]
  have h0 := negative_word (Field m) 0
  have h5 := negative_word (Field m) 1
  have h1 := negative_word (Field m) 2
  change _*canonicalRoot e6Data (Field m) false 0 1*_= _ at h0
  change _*canonicalRoot e6Data (Field m) false 5 1*_= _ at h5
  change _*canonicalRoot e6Data (Field m) false 1 1*_= _ at h1
  calc
    _ = (canonicalWord e6Data (Field m) [0,5,1]*
          canonicalRoot e6Data (Field m) false 0 1*
          (canonicalWord e6Data (Field m) [0,5,1])⁻¹)*
        (canonicalWord e6Data (Field m) [0,5,1]*
          canonicalRoot e6Data (Field m) false 5 1*
          (canonicalWord e6Data (Field m) [0,5,1])⁻¹)*
        (canonicalWord e6Data (Field m) [0,5,1]*
          canonicalRoot e6Data (Field m) false 1 1*
          (canonicalWord e6Data (Field m) [0,5,1])⁻¹) := by group
    _ = _ := by rw [h0,h5,h1]; rfl

theorem middle_commutes_negativeOuter (m : ℕ) :
    Commute (fourCycle m) (negativeOuter m) := by
  have hc (i : Fin 4) : Commute (yParameter (Field m) i 1)
      (fixedRawHom m (negativeOuter m)) := by
    rw [raw_negativeOuter]
    exact ((pair_commute A hd hs hp ho (Field m) (yRoot i) (negSimple 0)
      (negative_pairings i 0) 1 1).mul_right
      (pair_commute A hd hs hp ho (Field m) (yRoot i) (negSimple 5)
        (negative_pairings i 1) 1 1)).mul_right
      (pair_commute A hd hs hp ho (Field m) (yRoot i) (negSimple 1)
        (negative_pairings i 2) 1 1)
  have hraw : Commute (fixedRawHom m (fourCycle m))
      (fixedRawHom m (negativeOuter m)) := by
    rw [raw_fourCycle,yWord_eq]
    exact ((hc 0).mul_left (hc 1)).mul_left (hc 2) |>.mul_left (hc 3)
  apply (show Function.Injective (fixedRawHom m) from fun _ _ h =>
    Subtype.ext (rawHom_injective (Field m) h))
  simpa only [map_mul] using hraw.eq

theorem middle_conjugate_outerWeyl (m : ℕ) :
    fourCycle m*outerFixedWeyl m*(fourCycle m)⁻¹=
      (fiveWord m*outerInvolution m*(fiveWord m)⁻¹)*negativeOuter m*
        (fiveWord m*outerInvolution m*(fiveWord m)⁻¹) := by
  have hwoWord : outerFixedWeyl m=outerInvolution m*negativeOuter m*outerInvolution m :=
    outerWeyl_three_word m
  have hn : fourCycle m*negativeOuter m*(fourCycle m)⁻¹=negativeOuter m := by
    rw [(middle_commutes_negativeOuter m).eq,mul_assoc,mul_inv_cancel,mul_one]
  calc
    _ = (fourCycle m*outerInvolution m*(fourCycle m)⁻¹)*
        (fourCycle m*negativeOuter m*(fourCycle m)⁻¹)*
        (fourCycle m*outerInvolution m*(fourCycle m)⁻¹) := by rw [hwoWord]; group
    _ = _ := by rw [hn,outer_middle_conjugation]

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeOuterCommute

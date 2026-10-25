import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareRootWordValues
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterThreeWord

/-! Actual original fixed-group word values for the middle-square
commutator. Every map is the faithful original F4-to-E6 map, for all m,
including zero; no positive-parameter recognition theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareOriginalWords
open CFSGReeFFourMiddleSquareRootWordValues CFSGFFourOriginalMiddleWords
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleFixedWords
open CFSGReeFFourMiddleWeylConstantWord CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOuterThreeWord CFSGReeFFourOuterFixedRoot
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRelativeWeylRawWords
open CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGE6GeckMiddleAThreeCollecting CFSGE6GeckMiddleFactorInjective
open CFSGE6GeckSignedSimpleParameters

private abbrev R (m : ℕ) (i : Fin 6) := canonicalRoot e6Data (Field m) false i 1
private abbrev W (m : ℕ) (s : List (Fin 6)) := canonicalWord e6Data (Field m) s

private theorem word_append (m : ℕ) (s t : List (Fin 6)) :
    W m (s++t) = W m s*W m t := by
  induction s with
  | nil => simp only [W,List.nil_append,canonicalWord,one_mul]
  | cons i s ih =>
    change canonicalWeyl e6Data (Field m) i*W m (s++t) =
      (canonicalWeyl e6Data (Field m) i*W m s)*W m t
    rw [ih,mul_assoc]


private theorem raw_outer (m : ℕ) :
    fixedRawHom m (outerFixedWeyl m) = W m [0,5,1] := by
  rw [fixedRawHom_apply]
  exact rawHom_outerRelativeWeyl m

private theorem raw_middle (m : ℕ) :
    fixedRawHom m (middleFixedWeyl m) = W m [2,4,3,2,4,3] := by
  rw [fixedRawHom_apply]
  exact rawHom_middleRelativeWeyl m

private theorem raw_w (m : ℕ) :
    fixedRawHom m (outerFixedWeyl m*middleFixedWeyl m) = W m [0,5,1,2,4,3,2,4,3] := by
  rw [map_mul,raw_outer,raw_middle]
  exact (word_append m [0,5,1] [2,4,3,2,4,3]).symm

private theorem raw_v (m : ℕ) :
    fixedRawHom m (middleFixedWeyl m*outerFixedWeyl m) = W m [2,4,3,2,4,3,0,5,1] := by
  rw [map_mul,raw_middle,raw_outer]
  exact (word_append m [2,4,3,2,4,3] [0,5,1]).symm

private theorem raw_x (m : ℕ) :
    fixedRawHom m (outerInvolution m) = R m 0*R m 5*R m 1 := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (outerWord m 1) = _
  simp only [outerWord,map_mul,rawHom_root,map_one,folded_positive_root]
  rfl

def outerConjugate (m : ℕ) : originalModelFixed m :=
  (outerFixedWeyl m*middleFixedWeyl m)^2*outerInvolution m*
    ((outerFixedWeyl m*middleFixedWeyl m)^2)⁻¹

theorem raw_fourCycle (m : ℕ) : fixedRawHom m (fourCycle m) = yWord (Field m) := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (fixedMiddleWord m 1 0) = _
  rw [fixedMiddleWord_one_zero]
  simp only [map_mul,rawHom_root,rawHom_middleLong,folded_positive_root]
  change (R m 2*R m 4)*R m 3*highestMiddle (Field m) 1 = yWord (Field m)
  simp only [yWord,highestMiddle,canonicalWord,mul_one]

theorem raw_outerConjugate (m : ℕ) :
    fixedRawHom m (outerConjugate m) = uWord (Field m) := by
  simp only [outerConjugate,map_mul,map_inv,map_pow,raw_middle,raw_outer,raw_x]
  rw [←word_append m [0,5,1] [2,4,3,2,4,3]]
  rw [pow_two,←word_append m]
  rfl

private theorem raw_square (m : ℕ) : fixedRawHom m ((fourCycle m)^2) =
    highestMiddle (Field m) 1*
      (W m [3]*(R m 2*R m 4)*(W m [3])⁻¹) := by
  rw [fourCycle_square,fixedRawHom_apply]
  change rawHom (Field m) (fixedMiddleWord m 0 1) = _
  rw [fixedMiddleWord_zero_one,map_mul,rawHom_middleLong,rawHom_middleShort]
  simp only [middlePair,rawPairedHom,canonicalWord,mul_one,RingEquiv.refl_apply]
  rfl

theorem raw_conjugateSquare (m : ℕ) :
    fixedRawHom m ((middleFixedWeyl m*outerFixedWeyl m)*(fourCycle m)^2*
      (middleFixedWeyl m*outerFixedWeyl m)⁻¹) = squareWord (Field m) := by
  simp only [map_mul,map_inv,raw_square,raw_middle,raw_outer]
  rw [←word_append m [2,4,3,2,4,3] [0,5,1]]
  simp only [squareWord,highestMiddle,canonicalWord,mul_one]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareOriginalWords

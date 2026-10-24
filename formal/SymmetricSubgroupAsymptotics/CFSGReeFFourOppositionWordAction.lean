import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOppositionLattice
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedModelWords

/-! The pinned opposition has involutive lattice action and commutes on
that lattice with each of the two relative reflections. The certificates
are products of one explicit six-coordinate signed permutation and the
two small relative words. No equality of original group words is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionWordAction
open CFSGReeFFourRelativeOppositionLattice CFSGReeFFourRelativeOpposition
open CFSGReeFFourPairedDescentPrefixes CFSGReeFFourPairedWordActions
open CFSGReeFFourPairedModelWords CFSGReeFFourFieldParameters
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourOriginalWeylWords
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6WeylChamber
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckWeylLatticeLinear
open CFSGSignedCartanReflections CFSGSerreDiagram
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆

private def signedDiagram : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j=>if i=e6Permutation j then -1 else 0

private theorem opposition_matrix : latticeWord A relativeOppositionWord=signedDiagram := by
  ext i j
  have h := congrFun (relative_opposition_simple_lattice j) i
  rw [Matrix.mulVec_single_one] at h
  change latticeWord A relativeOppositionWord i j=-(Pi.single (e6Permutation j) (1:ℤ) : Fin 6→ℤ) i at h
  have hs : -(Pi.single (e6Permutation j) (1:ℤ) : Fin 6→ℤ) i=signedDiagram i j := by
    simp only [Pi.single_apply,signedDiagram]
    by_cases he : i=e6Permutation j
    · simp only [if_pos he]
    · simp only [if_neg he,neg_zero]
  exact h.trans hs

private theorem signedDiagram_square : signedDiagram*signedDiagram=1 := by decide

private theorem signedDiagram_commute (b : Bool) :
    signedDiagram*latticeWord A (pairedWord b)=latticeWord A (pairedWord b)*signedDiagram := by
  cases b <;> decide

private theorem latticeWord_append (v w : List (Fin 6)) :
    latticeWord A (v++w)=latticeWord A v*latticeWord A w := by
  induction v with
  | nil=>simp only [List.nil_append,latticeWord,one_mul]
  | cons i v ih=>simp only [List.cons_append,latticeWord,ih,mul_assoc]

private theorem linearAction_eq_of_latticeWord_eq (v w : List (Fin 6))
    (he : latticeWord A v=latticeWord A w) : linearAction v=linearAction w := by
  apply LinearEquiv.toLinearMap_injective
  exact (latticeWord_linear A CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos v).symm.trans
      ((congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ=>M.mulVecLin) he).trans
        (latticeWord_linear A CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
          E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w))

def oppositionRelativeWord : List (Fin 4) :=
  let c := pairedRelativeWord false++pairedRelativeWord true
  c++c++c++c

theorem expand_oppositionRelativeWord :
    expandRelative oppositionRelativeWord=relativeOppositionWord := by rfl

theorem modelWeylWord_oppositionRelativeWord (m : ℕ) :
    modelWeylWord (Field m) oppositionRelativeWord=relativeOpposition m := by
  have h0 : modelWeylWord (Field m) (pairedRelativeWord false)=outerRelativeWeyl m := by
    simp only [pairedRelativeWord,Bool.false_eq_true,ite_false,modelWeylWord,
      outerRelativeWeyl,mul_one]
  have h1 : modelWeylWord (Field m) (pairedRelativeWord true)=middleRelativeWeyl m := by
    simp only [pairedRelativeWord,ite_true,modelWeylWord,middleRelativeWeyl,mul_one,mul_assoc]
  simp only [oppositionRelativeWord,modelWeylWord_append,h0,h1,relativeOpposition]
  noncomm_ring

theorem opposition_linear_square :
    linearAction relativeOppositionWord*linearAction relativeOppositionWord=1 := by
  have hm : latticeWord A (relativeOppositionWord++relativeOppositionWord)=latticeWord A [] := by
    rw [latticeWord_append,opposition_matrix,signedDiagram_square]
    rfl
  have h := linearAction_eq_of_latticeWord_eq _ _ hm
  rw [linearAction_append] at h
  exact h

theorem opposition_simple_linear_commute (b : Bool) :
    linearAction relativeOppositionWord*linearAction (pairedWord b)=
      linearAction (pairedWord b)*linearAction relativeOppositionWord := by
  have hm : latticeWord A (relativeOppositionWord++pairedWord b)=
      latticeWord A (pairedWord b++relativeOppositionWord) := by
    rw [latticeWord_append,latticeWord_append,opposition_matrix]
    exact signedDiagram_commute b
  have h := linearAction_eq_of_latticeWord_eq _ _ hm
  simpa only [linearAction_append] using h

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionWordAction

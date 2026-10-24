import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedDescentPrefixes
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! The two paired descent words are involutions on the literal E6
lattice, and reversing their relative letters preserves that action.
Consequently the reversed-letter action condition survives a descent
step, without requiring an intermediate group cell to be fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPairedWordActions
open CFSGReeFFourPairedDescentPrefixes CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGNormTwoCoordinateLatticeWord
open CFSGNormTwoGeckWeylLatticeLinear CFSGSignedCartanReflections
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def pairedRelativeWord (middle : Bool) : List (Fin 4) :=
  if middle then [1,2,1,2] else [0,3]

theorem expand_pairedRelativeWord (middle : Bool) :
    expandRelative (pairedRelativeWord middle)=pairedWord middle := by
  cases middle <;> rfl

private theorem linearAction_eq_of_latticeWord_eq (v w : List (Fin 6))
    (he : latticeWord A v=latticeWord A w) : linearAction v=linearAction w := by
  apply LinearEquiv.toLinearMap_injective
  exact (latticeWord_linear A hd hs hp ho v).symm.trans
    ((congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ=>M.mulVecLin) he).trans
      (latticeWord_linear A hd hs hp ho w))

theorem paired_linear_square (middle : Bool) :
    linearAction (pairedWord middle)*linearAction (pairedWord middle)=1 := by
  have hmat : ∀b,latticeWord A (pairedWord b++pairedWord b)=latticeWord A [] := by
    decide
  have h := linearAction_eq_of_latticeWord_eq _ _ (hmat middle)
  rw [linearAction_append] at h
  exact h

theorem reverse_paired_root_action (middle : Bool) (k : CFSGNormTwoRootPairing.Roots A) :
    rootAction (expandRelative ((pairedRelativeWord middle).map CFSG.Models.reverseNode)) k=
      rootAction (expandRelative (pairedRelativeWord middle)) k := by
  have hmat : ∀b,
      latticeWord A (expandRelative ((pairedRelativeWord b).map CFSG.Models.reverseNode))=
        latticeWord A (expandRelative (pairedRelativeWord b)) := by
    decide
  have hlin := linearAction_eq_of_latticeWord_eq _ _ (hmat middle)
  apply Subtype.ext
  calc
    _=linearAction (expandRelative ((pairedRelativeWord middle).map CFSG.Models.reverseNode)) k.val :=
      (wordLinear_root A hs hp E6Base E6Index _ k).symm
    _=linearAction (expandRelative (pairedRelativeWord middle)) k.val :=
      congrArg (fun L : (Fin 6→ℤ)≃ₗ[ℤ](Fin 6→ℤ)=>L k.val) hlin
    _=_ := wordLinear_root A hs hp E6Base E6Index _ k

theorem reversed_word_action_append (r : List (Fin 4)) (middle : Bool)
    (hr : ∀k,rootAction (expandRelative (r.map CFSG.Models.reverseNode)) k=
      rootAction (expandRelative r) k) :
    ∀k,rootAction (expandRelative ((r++pairedRelativeWord middle).map CFSG.Models.reverseNode)) k=
      rootAction (expandRelative (r++pairedRelativeWord middle)) k := by
  intro k
  rw [List.map_append,expandRelative_append,expandRelative_append,
    rootAction_append,rootAction_append,hr,reverse_paired_root_action]

end SymmetricSubgroupAsymptotics.CFSGReeFFourPairedWordActions

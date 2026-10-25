import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketFixedBlocks

/-! The SAME whole middle-square word and its outer-Weyl conjugate.
Only these two fixed-block corrections are used by the designated inner
commutator candidate. No individual root is asserted exceptional-fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketSquareSupports
open CFSGReeFFourInnerBracketFixedBlocks CFSGReeFFourMiddleSquareBracketRootData
open CFSGReeFFourMiddleSquareBracketRootRelations CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourInversionSuffixSignPilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateSelectedRootElement CFSGFFourE6PositiveRootUnits
open CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def outerSquareVector : Fin 3 → Fin 6 → ℤ :=
  ![![1,1,2,2,1,1], ![1,1,1,2,2,1], ![1,2,2,3,2,1]]

theorem root_properties : ∀ i : Fin 3,
    integerPairing A (outerSquareVector i) (outerSquareVector i)=2 ∧
      ∀ t : Fin 6, 0≤outerSquareVector i t := by
  decide +kernel

private theorem transport_certificate : ∀ i : Fin 3, ∀ t : Fin 6,
    vectorWord [0,5,1] (bracketVector i) t = outerSquareVector i t := by
  decide +kernel

theorem outer_transport (i : Fin 3) :
    vectorWord [0,5,1] (bracketVector i) = outerSquareVector i := by
  funext t
  exact transport_certificate i t

def outerSquareRoot (i : Fin 3) : Roots A :=
  ⟨outerSquareVector i,(root_properties i).1⟩

variable (K : Type) [CommRing K] [CharP K 2]

abbrev outerSquareParameter (i : Fin 3) :=
  selectedRootElement A hd hs hp ho K (outerSquareRoot i) 1

theorem parameter_conjugate (i : Fin 3) :
    (MulAut.conj (canonicalWord e6Data K [0,5,1])) (bracketParameter K i 1) =
      outerSquareParameter K i :=
  selected_word_one K [0,5,1] (bracketRoot i) (outerSquareRoot i) (outer_transport i)

private theorem map_three {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b c : G) : f (a*b*c)=f a*f b*f c := by
  rw [map_mul,map_mul]

theorem squareWord_outer_conjugate :
    (MulAut.conj (canonicalWord e6Data K [0,5,1])) (squareWord K) =
      outerSquareParameter K 0 * outerSquareParameter K 1 * outerSquareParameter K 2 := by
  let F := (MulAut.conj (canonicalWord e6Data K [0,5,1])).toMonoidHom
  have h0 : F (bracketParameter K 0 1)=outerSquareParameter K 0 := parameter_conjugate K 0
  have h1 : F (bracketParameter K 1 1)=outerSquareParameter K 1 := parameter_conjugate K 1
  have h2 : F (bracketParameter K 2 1)=outerSquareParameter K 2 := parameter_conjugate K 2
  have hm := map_three F (bracketParameter K 0 1) (bracketParameter K 1 1)
    (bracketParameter K 2 1)
  change F (squareWord K) = _
  exact (congrArg F (squareWord_eq K)).trans (hm.trans
    (congrArg₂ (fun a c => a*c) (congrArg₂ (fun a c => a*c) h0 h1) h2))

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketSquareSupports

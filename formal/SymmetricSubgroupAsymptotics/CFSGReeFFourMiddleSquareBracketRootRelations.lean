import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootData
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootRelations
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute

/-! Actual selected-root relations for the three central factors in the
middle-square commutator. Integral Chevalley signs are removed only under
an explicit characteristic-two assumption. No matrix diagnostic is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootRelations
open CFSGReeFFourMiddleSquareBracketRootData CFSGIntegerMatrixPairing
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinateRootPairCommute
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def yRoot (i : Fin 4) : Roots A := ⟨yVector i, norm_two.1 i⟩
def uRoot (j : Fin 3) : Roots A := ⟨uVector j, norm_two.2.1 j⟩
def bracketRoot (j : Fin 3) : Roots A := ⟨bracketVector j, norm_two.2.2 j⟩

abbrev yParameter (K : Type) [CommRing K] (i : Fin 4) (a : K) :=
  selectedRootElement A hd hs hp ho K (yRoot i) a
abbrev uParameter (K : Type) [CommRing K] (j : Fin 3) (a : K) :=
  selectedRootElement A hd hs hp ho K (uRoot j) a
abbrev bracketParameter (K : Type) [CommRing K] (j : Fin 3) (a : K) :=
  selectedRootElement A hd hs hp ho K (bracketRoot j) a

private theorem positive_y : ∀ i : Fin 4, ∀ t : Fin 6, 0 ≤ yVector i t := by decide +kernel
private theorem positive_u : ∀ j : Fin 3, ∀ t : Fin 6, 0 ≤ uVector j t := by decide +kernel
private theorem paired : ∀ j : Fin 3,
    integerPairing A (yVector j.castSucc) (uVector j) = -1 := by decide +kernel
private theorem off_diagonal : ∀ i : Fin 4, ∀ j : Fin 3, i ≠ j.castSucc →
    integerPairing A (yVector i) (uVector j) = 0 ∨
      integerPairing A (yVector i) (uVector j) = 1 := by decide +kernel
private theorem y_bracket : ∀ i : Fin 4, ∀ j : Fin 3,
    integerPairing A (yVector i) (bracketVector j) = 0 ∨
      integerPairing A (yVector i) (bracketVector j) = 1 := by decide +kernel
private theorem u_bracket : ∀ i j : Fin 3,
    integerPairing A (uVector i) (bracketVector j) = 0 ∨
      integerPairing A (uVector i) (bracketVector j) = 1 := by decide +kernel
private theorem bracket_bracket : ∀ i j : Fin 3, i ≠ j →
    integerPairing A (bracketVector i) (bracketVector j) = 0 ∨
      integerPairing A (bracketVector i) (bracketVector j) = 1 := by decide +kernel

private theorem sumRoot_eq (j : Fin 3) :
    sumRoot A hs (yRoot j.castSucc) (uRoot j) (paired j) = bracketRoot j := by
  apply Subtype.ext
  funext t
  exact sum_bracket j t

private theorem sign_cast_one {K : Type} [CommRing K] [CharP K 2]
    (e : ℤ) (he : e = 1 ∨ e = -1) : (e : K) = 1 := by
  rcases he with rfl | rfl <;> simp only [Int.cast_one, Int.cast_neg, CharTwo.neg_eq]

theorem paired_commutator (K : Type) [CommRing K] [CharP K 2]
    (j : Fin 3) (a b : K) :
    ⁅yParameter K j.castSucc a, uParameter K j b⁆ = bracketParameter K j (a*b) := by
  obtain ⟨e, he, h⟩ := positive_pair_commutator_sign A hd hs hp ho
    (yRoot j.castSucc) (uRoot j) (positive_y j.castSucc) (positive_u j) (paired j)
  have hh := h K a b
  rw [sumRoot_eq, sign_cast_one e he, one_mul] at hh
  exact hh

theorem cross_commute (K : Type) [CommRing K] (i : Fin 4) (j : Fin 3)
    (hij : i ≠ j.castSucc) (a b : K) : Commute (yParameter K i a) (uParameter K j b) :=
  pair_commute A hd hs hp ho K (yRoot i) (uRoot j) (off_diagonal i j hij) a b

theorem y_bracket_commute (K : Type) [CommRing K] (i : Fin 4) (j : Fin 3) (a b : K) :
    Commute (yParameter K i a) (bracketParameter K j b) :=
  pair_commute A hd hs hp ho K (yRoot i) (bracketRoot j) (y_bracket i j) a b

theorem u_bracket_commute (K : Type) [CommRing K] (i j : Fin 3) (a b : K) :
    Commute (uParameter K i a) (bracketParameter K j b) :=
  pair_commute A hd hs hp ho K (uRoot i) (bracketRoot j) (u_bracket i j) a b

theorem bracket_commute (K : Type) [CommRing K] (i j : Fin 3) (a b : K) :
    Commute (bracketParameter K i a) (bracketParameter K j b) := by
  by_cases hij : i = j
  · subst j
    exact selectedRootElement_commute A hd hs hp ho K (bracketRoot i) a b
  · exact pair_commute A hd hs hp ho K (bracketRoot i) (bracketRoot j)
      (bracket_bracket i j hij) a b

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootRelations

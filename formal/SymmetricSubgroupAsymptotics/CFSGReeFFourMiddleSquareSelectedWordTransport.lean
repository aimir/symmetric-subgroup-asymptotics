import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits

/-! Literal characteristic-two Weyl-word transport to the SAME selected
E6 root parameter. The target lattice equality is retained explicitly;
there is no choice of a replacement finite-field root parametrization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareSelectedWordTransport
open CFSGReeFFourInversionSuffixSignPilot CFSGNormTwoCoordinateLatticeWord
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateWordRootElementSign
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGSerreQuadraticMatrix
open CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticWeylWord
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem sign_cast_one {K : Type} [CommRing K] [CharP K 2]
    (e : ℤ) (he : e = 1 ∨ e = -1) : (e : K) = 1 := by
  rcases he with rfl | rfl <;> simp only [Int.cast_one, Int.cast_neg, CharTwo.neg_eq]

private theorem wordRoot_eq (w : List (Fin 6)) (k l : Roots A)
    (h : vectorWord w k.val = l.val) : wordRoot A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w k = l := by
  apply Subtype.ext
  have he := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w) k.val
  change CFSGSignedCartanReflections.latticeWord A w *ᵥ k.val =
    wordLinear A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w k.val at he
  rw [wordLinear_root] at he
  exact he.symm.trans ((vectorWord_eq w k.val).symm.trans h)

theorem selected_word_one (K : Type) [CommRing K] [CharP K 2]
    (w : List (Fin 6)) (k l : Roots A) (h : vectorWord w k.val = l.val) :
    (MulAut.conj (canonicalWord e6Data K w))
      (selectedRootElement A hd hs hp ho K k 1) =
        selectedRootElement A hd hs hp ho K l 1 := by
  obtain ⟨e,he,hw⟩ := word_selected_root_sign A hd hs hp ho w k
  have hh := hw K 1
  rw [wordRoot_eq w k l h,sign_cast_one e he,one_mul] at hh
  exact hh

theorem simple_one (K : Type) [CommRing K] [CharP K 2] (i : Fin 6) :
    canonicalRoot e6Data K false i 1 = selectedRootElement A hd hs hp ho K (E6Index i) 1 := by
  obtain ⟨e,he,hh⟩ := selected_simple_root_sign A hd hs hp ho i
  have h := hh K 1
  rw [sign_cast_one e he,one_mul] at h
  exact h.symm

theorem word_simple_one (K : Type) [CommRing K] [CharP K 2]
    (w : List (Fin 6)) (i : Fin 6) (l : Roots A)
    (h : vectorWord w (Pi.single i (1 : ℤ)) = l.val) :
    canonicalWord e6Data K w * canonicalRoot e6Data K false i 1 *
      (canonicalWord e6Data K w)⁻¹ = selectedRootElement A hd hs hp ho K l 1 := by
  rw [simple_one]
  apply selected_word_one K w (E6Index i) l
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareSelectedWordTransport

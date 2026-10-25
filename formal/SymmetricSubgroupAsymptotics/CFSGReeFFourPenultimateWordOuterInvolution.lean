import SymmetricSubgroupAsymptotics.CFSGReeFFourShortMenuPeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareSelectedWordTransport
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareOriginalWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! The sole non-opposite binary relative position whose full positive
intersection can have order two retains the WHOLE actual outer involution.
The integral word exchanges its E6 end-node parameters and fixes the third.
All coefficient-field and original fixed-group statements retain abstract m;
no individual E6 parameter is asserted exceptional-fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPenultimateWordOuterInvolution
open CFSGReeFFourInversionPeelingWords CFSGReeFFourShortMenuPeeling
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourInversionSuffixSignPilot
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourOuterThreeWord
open CFSGReeFFourOuterFixedRoot CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFieldParameters
open CFSGOpposedSubgroupPeelingChain CFSGOpposedSubgroupPeelingMembership
open CFSGFFourOriginalMiddleWords CFSGFFourE6PositiveRootUnits
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckOrthogonalWeyl
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

/-- The literal inverse suffix for the length-seven, middle-first word. -/
def penultimateRawWord : List (Fin 6) := suffixWord true 7 7

theorem outer_lattice_transport :
    vectorWord penultimateRawWord (Pi.single (0 : Fin 6) (1 : ℤ)) = Pi.single 5 1 ∧
    vectorWord penultimateRawWord (Pi.single (5 : Fin 6) (1 : ℤ)) = Pi.single 0 1 ∧
    vectorWord penultimateRawWord (Pi.single (1 : Fin 6) (1 : ℤ)) = Pi.single 1 1 := by
  constructor
  · funext j
    fin_cases j <;> decide +kernel
  constructor
  · funext j
    fin_cases j <;> decide +kernel
  · funext j
    fin_cases j <;> decide +kernel

private theorem fullSuffix_eq_inversePrefix {G : Type*} [Group G]
    (w : ℕ → G) (n : ℕ) : inverseSuffix w n n = (wordPrefix w n)⁻¹ := by
  induction n with
  | zero => simp only [inverseSuffix, wordPrefix, inv_one]
  | succ n ih => rw [inverseSuffix, ih, wordPrefix, mul_inv_rev]

private theorem penultimate_suffix (m : ℕ) :
    inverseSuffix (step m true) 7 7 = shortModelWord m (14 : Fin 16) := by
  have hw : wordPrefix (step m true) 7 = (shortModelWord m (14 : Fin 16))⁻¹ :=
    short_prefix_eq_inverse m (14 : Fin 16)
  rw [fullSuffix_eq_inversePrefix, hw, inv_inv]

theorem raw_penultimate (m : ℕ) :
    fixedRawHom m (shortModelWord m (14 : Fin 16)) =
      canonicalWord e6Data (Field m) penultimateRawWord := by
  have h := fixedRawHom_inverseSuffix m true 7 7
  rw [penultimate_suffix, word_eq_canonicalWord] at h
  exact h

private abbrev R (m : ℕ) (i : Fin 6) := canonicalRoot e6Data (Field m) false i 1

private theorem raw_outer (m : ℕ) :
    fixedRawHom m (outerInvolution m) = R m 0*R m 5*R m 1 := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (outerWord m 1) = _
  simp only [outerWord, map_mul, rawHom_root, map_one, folded_positive_root]
  rfl

private theorem raw_outer_conjugate (m : ℕ) :
    canonicalWord e6Data (Field m) penultimateRawWord *
      (R m 0*R m 5*R m 1) *
        (canonicalWord e6Data (Field m) penultimateRawWord)⁻¹ = R m 0*R m 5*R m 1 := by
  let F := (MulAut.conj (canonicalWord e6Data (Field m) penultimateRawWord)).toMonoidHom
  have h0 : F (R m 0) = R m 5 :=
    (word_simple_one (Field m) penultimateRawWord 0 (E6Index 5)
      outer_lattice_transport.1).trans (simple_one (Field m) 5).symm
  have h5 : F (R m 5) = R m 0 :=
    (word_simple_one (Field m) penultimateRawWord 5 (E6Index 0)
      outer_lattice_transport.2.1).trans (simple_one (Field m) 0).symm
  have h1 : F (R m 1) = R m 1 :=
    (word_simple_one (Field m) penultimateRawWord 1 (E6Index 1)
      outer_lattice_transport.2.2).trans (simple_one (Field m) 1).symm
  have hc : Commute (R m 0) (R m 5) :=
    orthogonal_signed_roots A hs hp E6Base E6Index (Field m) 0 5
      (by rw [E6_cartan]; decide) false false 1 1
  change F (R m 0*R m 5*R m 1) = _
  rw [map_mul, map_mul, h0, h5, h1, hc.eq]

theorem penultimate_conjugates_outer (m : ℕ) :
    shortModelWord m (14 : Fin 16) * outerInvolution m *
      (shortModelWord m (14 : Fin 16))⁻¹ = outerInvolution m := by
  have hraw : fixedRawHom m
      (shortModelWord m (14 : Fin 16) * outerInvolution m *
        (shortModelWord m (14 : Fin 16))⁻¹) = fixedRawHom m (outerInvolution m) := by
    rw [map_mul, map_mul, map_inv, raw_penultimate, raw_outer]
    exact raw_outer_conjugate m
  apply Subtype.ext
  exact rawHom_injective (Field m) hraw

end SymmetricSubgroupAsymptotics.CFSGReeFFourPenultimateWordOuterInvolution

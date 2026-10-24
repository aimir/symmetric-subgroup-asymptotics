import SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalEmbedding
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits

/-! The literal long folded Levi parameter raises the two orthogonal
central X factors into their complementary Y factors. This is an actual
root-word commutator, with integral signs removed only in characteristic
two. It is the bounded generator step before a centre7 action formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviRootActions
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGExceptionalHeisenbergRootRelations CFSGExceptionalHeisenbergProduct
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSignedRootCollecting
open CFSGNormTwoCoordinateRaisedRoot CFSGNormTwoCoordinateRootCollectingTransport
open CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits
local instance fFourBinaryLongLeviRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def firstIndex : Fin 2 → Fin 10 := ![6,8]
def secondIndex : Fin 2 → Fin 10 := ![8,6]

private theorem long_pairing (i : Fin 2) :
    integerPairing A (configuration.xRoot (firstIndex i)).val.val
      (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val = -1 := by
  fin_cases i <;> decide

private theorem long_raised (i : Fin 2) :
    raisedRoot A hd hs hp ho (configuration.xRoot (firstIndex i)).val 3 (long_pairing i) =
      (configuration.yRoot (secondIndex i)).val := by
  apply Subtype.ext
  change configuration.x (firstIndex i)+(Pi.single 3 (1 : ℤ) : Fin 6 → ℤ) =
    configuration.y (secondIndex i)
  fin_cases i <;> decide

private theorem sign_cast_one {K : Type} [CommRing K] [CharP K 2]
    (e : ℤ) (he : e=1 ∨ e= -1) : (e : K)=1 := by
  rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]

private abbrev firstParameter (K : Type) [CommRing K] (i : Fin 10) (t : K) :
    (Matrix Index Index K)ˣ :=
  xHom A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private abbrev secondParameter (K : Type) [CommRing K] (i : Fin 10) (t : K) :
    (Matrix Index Index K)ˣ :=
  yNegative A hd hs hp ho configuration K i (Multiplicative.ofAdd t)

theorem long_positive_commutator (K : Type) [CommRing K] [CharP K 2]
    (i : Fin 2) (a t : K) :
    canonicalRoot realizationData K false 2 a *
      firstParameter K (firstIndex i) t *
      (canonicalRoot realizationData K false 2 a)⁻¹ *
      (firstParameter K (firstIndex i) t)⁻¹ =
      secondParameter K (secondIndex i) (a*t) := by
  obtain ⟨e,he,hcomm⟩ := simple_positive_commutator_sign A hd hs hp ho
    (configuration.xRoot (firstIndex i)).val (configuration.positive_x (firstIndex i))
    3 (long_pairing i)
  have h := hcomm K a t
  rw [long_raised,sign_cast_one e he,one_mul,mul_comm t a] at h
  have hfold : canonicalRoot realizationData K false 2 a = canonicalRoot e6Data K false 3 a := by
    rw [folded_positive_root]
    rfl
  rw [hfold]
  change positiveRootCommutator A hd hs hp ho K (configuration.xRoot (firstIndex i)).val 3 a t =
    selectedRootElement A hd hs hp ho K (configuration.yRoot (secondIndex i)).val
      (((pairSign A hd hs hp ho configuration (secondIndex i) : ℤ) : K) * (-(a*t)))
  rw [sign_cast_one _ (pairSign_unit A hd hs hp ho configuration (secondIndex i)),
    CharTwo.neg_eq,one_mul]
  exact h

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviRootActions

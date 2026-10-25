import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveFunctionalIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionSupport

/-! The actual longest middle A3 word sends all six zero-outside positive
roots negative. Its positive remainder therefore lies in the strict
outside-height kernel. No fixed-factor lifting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveRemainderSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGE6GeckMiddleRootSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckSignedRootColumns
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGReeFFourMiddleInversionSupport
open CFSGNormTwoCoordinatePositiveFunctionalIntersection CFSGReeFFourMiddlePositivePreserving
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGSerreQuadraticWeylWord CFSGGradedMatrixSubgroups
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local instance : DecidableEq (Roots A) := Classical.decEq _

private def vectorWord : List (Fin 6) → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [],v => v
  | i::w,v => vectorWord w v -
      integerPairing A (vectorWord w v) (Pi.single i 1) • Pi.single i 1

private theorem wordRoot_val_eq (w : List (Fin 6)) (k : Roots A) :
    (wordRoot A hs hp b₀ s₀ w k).val = vectorWord w k.val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change ((rootPairing A hs hp).reflectionPerm (s₀ i)
      (wordRoot A hs hp b₀ s₀ w k)).val = _
    rw [reflection_val,ih]
    rfl

private theorem six_middle_negative (i : Fin 6) :
    ¬ ∀ j, 0 ≤ vectorWord blockWord (middleVector i) j := by
  fin_cases i <;> decide +kernel

theorem middle_zero_goes_negative (k : PositiveRoot A)
    (hk : outsideHeight k.val.val = 0) :
    ¬ ∀ j,0 ≤ (wordRoot A hs hp b₀ s₀ blockWord k.val).val j := by
  obtain ⟨i,hi⟩ := (positive_root_zero_outside_iff k).mp hk
  rw [wordRoot_val_eq,hi]
  exact six_middle_negative i

theorem middle_positive_outside_one (k : PositiveRoot A)
    (hk : ∀ j,0 ≤ (wordRoot A hs hp b₀ s₀ blockWord k.val).val j) :
    1 ≤ outsideHeight k.val.val := by
  have hn := outsideHeight_nonnegative k
  have hne : outsideHeight k.val.val ≠ 0 := fun h => middle_zero_goes_negative k h hk
  omega

theorem middle_positive_remainder_le_strict (K : Type) [Field K] [Finite K] :
    Positive K ⊓ (Positive K).comap
      (MulAut.conj (canonicalWord rawData K blockWord)).toMonoidHom ≤
      strictUnits middleWeight :=
  positive_intersection_le_strict A hd hs hp ho K blockWord outsideHeight
    middle_positive_outside_one

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveRemainderSupport

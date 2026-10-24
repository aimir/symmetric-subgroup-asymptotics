import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylFunctionalIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositivePreserving
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordPositive

/-! The middle inversion roots have zero outside functional. The actual
inversion subgroup therefore preserves those lattice blocks, by genuine
sign-part generation. No count or coordinate coverage is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionSupport
open CFSGReeFFourMiddlePositivePreserving CFSGE6GeckMiddleRootSupport
open CFSGNormTwoCoordinateWeylFunctionalIntersection CFSGNormTwoCoordinateZeroFunctionalSupport
open CFSGNormTwoCoordinateOutsideWordPositive CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoGeckWeylWordDegree CFSGIntegralNormTwoSigns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGGradedMatrixSubgroups CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local instance : DecidableEq (Roots A) := Classical.decEq _

def blockWord : List (Fin 6) := [2,4,3,2,4,3]

theorem middle_negative_zero_outside (k : PositiveRoot A)
    (hk : ¬∀ j,0≤(wordRoot A hs hp b₀ s₀ blockWord k.val).val j) :
    outsideHeight k.val.val=0 := by
  have hn := (norm_two_coordinates_one_sign A hs hp
    (fun i => by rw [hd i]; exact even_two) ho _
    (wordRoot A hs hp b₀ s₀ blockWord k.val).property).resolve_left hk
  have hz (j : Fin 6) (hj : j=0 ∨ j=1 ∨ j=5) : k.val.val j=0 := by
    have hw : ∀ i ∈ blockWord,i≠j := by
      rcases hj with rfl | rfl | rfl <;> decide +kernel
    have he := wordRoot_outside_coordinate A hd hs hp ho blockWord k.val j hw
    have hjn := hn j
    rw [he] at hjn
    have hjp := k.property j
    omega
  rw [outsideHeight_apply,hz 0 (Or.inl rfl),hz 1 (Or.inr (Or.inl rfl)),
    hz 5 (Or.inr (Or.inr rfl))]
  rfl

def middleInversion (K : Type) [Field K] : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) :=
  Positive K ⊓ (Negative K).comap
    (MulAut.conj (canonicalWord rawData K blockWord)).toMonoidHom

theorem middleInversion_le_preserving (K : Type) [Field K] [Finite K] :
    middleInversion K ≤ preservingUnits middleWeight := by
  exact (inversion_le_zeroFunctionalGroup A hd hs hp ho K blockWord outsideHeight
    middle_negative_zero_outside).trans
    (zeroFunctionalGroup_le_preserving A hd hs hp ho K outsideHeight)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionSupport

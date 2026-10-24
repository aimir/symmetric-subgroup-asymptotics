import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveSubgroup
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveMatrixWordValues
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootSupport
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit

/-! The literal four-coordinate middle subgroup preserves the blocks
of the outside-coordinate functional. This follows from integer root
degrees of its six actual factors, before any field reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositivePreserving
open CFSGReeFFourMiddlePositiveSubgroup CFSGReeFFourMiddleWordInjective
open CFSGReeFFourPositiveMatrixWordValues CFSGReeFFourFieldParameters
open CFSGE6GeckMiddleRootSupport CFSGE6GeckMiddleRootDegrees
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylRootMembership CFSGGradedQuadraticUnit
open CFSGGradedMatrixSubgroups
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

def middleWeight (j : GeckIndex) : ℤ := outsideHeight (latticeWeight A hs hp E6Base j)

private theorem word_preserving (K : Type) [Field K] (w : List (Fin 6)) (i : Fin 6)
    (hz : outsideHeight (wordRoot A hs hp E6Base E6Index w (E6Index i)).val = 0) (t : K) :
    rootWord A hd hs hp ho K w i t ∈ preservingUnits middleWeight := by
  exact preserves_of_height_zero (latticeWeight A hs hp E6Base)
    (wordRoot A hs hp E6Base E6Index w (E6Index i)).val outsideHeight.toAddMonoidHom
    (rootWord A hd hs hp ho K w i t)
    (word_conjugate_quadraticGrade A hs hp E6Base E6Index K w i t) hz

private theorem coordinateMiddleWord_preserving (m : ℕ) (a b c d : Field m) :
    coordinateMiddleWord m a b c d ∈ preservingUnits middleWeight := by
  have hsimp (i : Fin 6) (hi : i=2 ∨ i=3 ∨ i=4) (t : Field m) :
      rootWord A hd hs hp ho (Field m) [] i t ∈ preservingUnits middleWeight := by
    apply word_preserving (Field m) [] i _ t
    rcases hi with rfl | rfl | rfl <;> rfl
  have hR := word_preserving (Field m) [2,4] 3 (by rw [highest_root_degree]; rfl) d
  have hP := word_preserving (Field m) [3] 2 (by rw [paired_first_degree]; rfl) c
  have hQ := word_preserving (Field m) [3] 4 (by rw [paired_second_degree]; rfl) c
  exact (preservingUnits middleWeight).mul_mem
    ((preservingUnits middleWeight).mul_mem
      ((preservingUnits middleWeight).mul_mem
        ((preservingUnits middleWeight).mul_mem (hsimp 2 (Or.inl rfl) a)
          (hsimp 4 (Or.inr (Or.inr rfl)) a))
        (hsimp 3 (Or.inr (Or.inl rfl)) b)) hR)
    ((preservingUnits middleWeight).mul_mem hP hQ)

theorem middlePositiveSubgroup_le_preserving (m : ℕ) :
    (middlePositiveSubgroup m).map (Positive (Field m)).subtype ≤
      preservingUnits middleWeight := by
  intro g hg
  obtain ⟨u,hu,rfl⟩ := hg
  obtain ⟨a,b,c,d,rfl⟩ := hu
  have he : (matrixMiddleWord (Field m) a b c d).val = coordinateMiddleWord m a b c d :=
    (rawHom_middleWord m a b c d).symm.trans (rawHom_middleWord_eq_coordinate m a b c d)
  change (matrixMiddleWord (Field m) a b c d).val ∈ preservingUnits middleWeight
  rw [he]
  exact coordinateMiddleWord_preserving m a b c d

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositivePreserving

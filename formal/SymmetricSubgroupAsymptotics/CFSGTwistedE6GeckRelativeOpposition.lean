import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeOppositionLattice
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord

/-! The displayed E6 relative opposition word is genuinely fixed and
belongs to J. It conjugates the actual full fixed upper subgroup onto
its opposite, using the checked ambient root-word containment. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6RelativeOppositionLattice CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6FixedWordClassification CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckIntegralWord CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoCoordinateOppositeWord CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGCentralTwistedCommutatorLift

def relativeOpposition (K : Type) [Field K] : (Matrix GeckIndex GeckIndex K)ˣ :=
  wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K oppositionWord

theorem relativeOpposition_fixed (K : Type) [Field K] (sigma : K ≃+* K) :
    unitTwist K sigma (relativeOpposition K) = relativeOpposition K := by
  simpa only [relativeOpposition, oppositionWord, word_eq_canonicalWord] using
    relative_word_fixed K sigma oppositionRelativeWord

theorem relativeOpposition_mem_generated (K : Type) [Field K] (sigma : K ≃+* K) :
    relativeOpposition K ∈ fixedRootGenerated K sigma :=
  relativeWord_mem_generated K sigma oppositionRelativeWord

theorem positive_image_le_negative (K : Type) [Field K] :
    (Positive K).map (MulAut.conj (relativeOpposition K)).toMonoidHom ≤
      rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K true := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact negative_word_mem CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K oppositionWord i t (opposition_simple_nonpositive i)

theorem positive_image_eq_negative (K : Type) [Field K] [Finite K] :
    (Positive K).map (MulAut.conj (relativeOpposition K)).toMonoidHom =
      rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K true := by
  have hi : Positive K ⊓ (Positive K).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom = ⊥ := by
    apply le_antisymm _ bot_le
    exact (inf_le_inf le_rfl (positive_image_le_negative K)).trans
      (le_of_eq (positive_inf_negative CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index coordinateHeight
        (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
          E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K))
  exact word_positive_map_eq_negative_of_disjoint CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K oppositionWord hi

private theorem fixed_conjugation_map {G : Type*} [Group G]
    (tau : MulAut G) (W : G) (hW : tau W = W) :
    (fixedSubgroup tau).map (MulAut.conj W).toMonoidHom = fixedSubgroup tau := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change tau (W * y * W⁻¹) = W * y * W⁻¹
    change tau y = y at hy
    rw [map_mul, map_mul, map_inv, hW, hy]
  · intro hx
    change tau x = x at hx
    refine ⟨W⁻¹ * x * W, ?_, ?_⟩
    · change tau (W⁻¹ * x * W) = W⁻¹ * x * W
      rw [map_mul, map_mul, map_inv, hW, hx]
    · change W * (W⁻¹ * x * W) * W⁻¹ = x
      group

theorem fixed_positive_image_eq_fixed_negative (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) :
    (signedFixed K sigma false).map (MulAut.conj (relativeOpposition K)).toMonoidHom =
      signedFixed K sigma true := by
  change ((Positive K) ⊓ fixedSubgroup (unitTwist K sigma)).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (relativeOpposition K)).injective,
    positive_image_eq_negative, fixed_conjugation_map _ _ (relativeOpposition_fixed K sigma)]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition

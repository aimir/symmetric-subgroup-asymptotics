import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceNormalization
import SymmetricSubgroupAsymptotics.CFSGFiniteHermitianSimilitudeRigidity

/-! Projection of a literal Hermitian dual vector onto the opposite
coordinate half. It retains every pairing with the standard singular
space and its entire image is pair-zero. This provides separating
singular vectors without a Witt or dimension-formula hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

def unitaryOppositeProjection (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) : Fin (r + 1) → q.Extension 2 :=
  fun i => if r < 2 * i.rev.val + 1 then 0 else x i

private theorem signedReversal_mulVec (q : CFSG.PrimePower) (r : ℕ)
    (y : Fin (r + 1) → q.Extension 2) (i : Fin (r + 1)) :
    ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i =
      signWeight (q.Extension 2) r i * y i.rev := by
  simp [Matrix.mulVec, dotProduct, signedReversalUnit_apply, ite_mul, eq_comm]

theorem unitaryOppositeProjection_pair_standard (q : CFSG.PrimePower) (r : ℕ)
    (x y : Fin (r + 1) → q.Extension 2) (hy : y ∈ unitaryStandardSingularSpace q r) :
    unitaryNaturalPair q r (unitaryOppositeProjection q r x) y = unitaryNaturalPair q r x y := by
  change (∑ i, definingFieldAutomorphism q 2 (unitaryOppositeProjection q r x i) *
      (((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i)) =
    ∑ i, definingFieldAutomorphism q 2 (x i) *
      (((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i)
  apply Finset.sum_congr rfl
  intro i _
  rw [signedReversal_mulVec]
  by_cases hi : r < 2 * i.rev.val + 1
  · rw [hy i.rev hi, mul_zero, mul_zero, mul_zero]
  · simp only [unitaryOppositeProjection, if_neg hi]

theorem unitaryOppositeProjection_pair_zero (q : CFSG.PrimePower) (r : ℕ)
    (x y : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r (unitaryOppositeProjection q r x)
      (unitaryOppositeProjection q r y) = 0 := by
  change (∑ i, definingFieldAutomorphism q 2 (unitaryOppositeProjection q r x i) *
      (((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ
        unitaryOppositeProjection q r y) i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [signedReversal_mulVec]
  by_cases hi : r < 2 * i.rev.val + 1
  · simp only [unitaryOppositeProjection, if_pos hi, map_zero, zero_mul]
  · have hr : r < 2 * i.val + 1 := by
      have hv : i.rev.val = r - i.val := by rw [Fin.val_rev]; omega
      have hib := i.isLt
      omega
    simp only [unitaryOppositeProjection, Fin.rev_rev, if_pos hr, mul_zero]

theorem exists_unitaryOpposite_dual (q : CFSG.PrimePower) (r : ℕ)
    (f : Module.Dual (q.Extension 2) (Fin (r + 1) → q.Extension 2)) :
    ∃ y : Fin (r + 1) → q.Extension 2, unitaryNaturalPair q r y y = 0 ∧
      ∀ z ∈ unitaryStandardSingularSpace q r, unitaryNaturalPair q r y z = f z := by
  obtain ⟨x, hx⟩ := CFSGFiniteHermitianSimilitudeRigidity.hermitianDual_surjective
    (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) f
  refine ⟨unitaryOppositeProjection q r x, unitaryOppositeProjection_pair_zero q r x x, ?_⟩
  intro z hz
  rw [unitaryOppositeProjection_pair_standard q r x z hz]
  exact congrArg (fun g : Module.Dual (q.Extension 2) (Fin (r + 1) → q.Extension 2) => g z) hx

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

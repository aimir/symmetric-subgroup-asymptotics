import SymmetricSubgroupAsymptotics.CFSGHyperbolicTransverseCorrection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootProductOrthogonality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailLinearExtension

/-! The literal twice-tail is corrected into the orthogonal complement
of a second plane companion. Its original coordinates give a left
inverse and preserve the exact original residual Gram norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBResidualCorrection
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBTailCoordinates CFSGHyperbolicTransverseCorrection
variable (K : Type) [Field K] [Finite K]

private theorem tailIndex_ne_positive_head (n : ℕ) (i : Index n) :
    tailIndex n i ≠ pos (n + 1) 0 := by
  intro he
  have hh : CFSGOrthogonalBTailCoordinates.tailEquiv n (Sum.inl i) = CFSGOrthogonalBTailCoordinates.tailEquiv n (Sum.inr 0) := he
  cases (CFSGOrthogonalBTailCoordinates.tailEquiv n).injective hh

omit [Finite K] in
theorem twiceTailRestriction_first (s : ℕ) :
    twiceTailRestriction K s (positiveVector (K := K) s 0) = 0 := by
  funext i
  change (Pi.single (pos (s + 3) 0) (1 : K) : Index (s + 3) → K)
    (tailIndex (s + 2) (tailIndex (s + 1) i)) = 0
  simp only [Pi.single_apply, if_neg (tailIndex_ne_positive_head (s + 2) _)]

omit [Finite K] in
theorem twiceTailRestriction_second (s : ℕ) :
    twiceTailRestriction K s (positiveVector (K := K) s (secondIndex s)) = 0 := by
  funext i
  change (Pi.single (pos (s + 3) (secondIndex s)) (1 : K) : Index (s + 3) → K)
    (tailIndex (s + 2) (tailIndex (s + 1) i)) = 0
  have hn : tailIndex (s + 2) (tailIndex (s + 1) i) ≠
      pos (s + 3) (secondIndex s) := by
    change tailIndex (s + 2) (tailIndex (s + 1) i) ≠ tailIndex (s + 2) (pos (s + 2) 0)
    exact (tailIndex_injective (s + 2)).ne (tailIndex_ne_positive_head (s + 1) i)
  simp only [Pi.single_apply, if_neg hn]

def residualMap (s : ℕ) (w : Index (s + 3) → K) :
    (Index (s + 1) → K) →ₗ[K] (Index (s + 3) → K) :=
  correction (gram K (s + 3)).toBilin' (positiveVector (K := K) s (secondIndex s)) w
    (twiceTailExtension K s)

theorem residualMap_leftInverse (s : ℕ) (w : Index (s + 3) → K) (z : Index (s + 1) → K) :
    twiceTailRestriction K s (residualMap K s w z) = z :=
  correction_leftInverse _ _ _ _ _ (twiceTail_leftInverse K s) (twiceTailRestriction_second K s) z

theorem residualMap_norm (s : ℕ) (w : Index (s + 3) → K) (z : Index (s + 1) → K) :
    (gram K (s + 3)).toBilin' (residualMap K s w z) (residualMap K s w z) =
      (gram K (s + 1)).toBilin' z z := by
  have hee : (gram K (s + 3)).toBilin'
      (positiveVector (K := K) s (secondIndex s)) (positiveVector (K := K) s (secondIndex s)) = 0 := by
    rw [positiveVector_pairing]
    simp [positiveVector, pos, neg]
  have he (t : Index (s + 1) → K) : (gram K (s + 3)).toBilin'
      (positiveVector (K := K) s (secondIndex s)) (twiceTailExtension K s t) = 0 := by
    rw [positiveVector_pairing, twiceTail_negative_second, mul_zero]
  have he' (t : Index (s + 1) → K) : (gram K (s + 3)).toBilin'
      (twiceTailExtension K s t) (positiveVector (K := K) s (secondIndex s)) = 0 :=
    (gram_pairing_symmetric (s + 3) _ _).trans (he t)
  exact (correction_pairing _ _ _ _ hee he he' z z).trans (twiceTail_norm K s z)

omit [Finite K] in
theorem residualMap_perp_companion (s : ℕ) (w : Index (s + 3) → K)
    (hw : (gram K (s + 3)).toBilin' w (positiveVector (K := K) s (secondIndex s)) ≠ 0)
    (z : Index (s + 1) → K) :
    (gram K (s + 3)).toBilin' w (residualMap K s w z) = 0 :=
  correction_orthogonal _ _ _ _ hw z

theorem residualMap_perp_positive (s : ℕ) (w : Index (s + 3) → K)
    (z : Index (s + 1) → K) (i : Fin (s + 3)) (hi : i = 0 ∨ i = secondIndex s) :
    (gram K (s + 3)).toBilin' (positiveVector (K := K) s i) (residualMap K s w z) = 0 := by
  apply correction_orthogonal_to
  · rw [positiveVector_pairing]
    simp [positiveVector, pos, neg]
  · intro t
    rcases hi with rfl | rfl
    · rw [positiveVector_pairing, twiceTail_negative_zero, mul_zero]
    · rw [positiveVector_pairing, twiceTail_negative_second, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBResidualCorrection

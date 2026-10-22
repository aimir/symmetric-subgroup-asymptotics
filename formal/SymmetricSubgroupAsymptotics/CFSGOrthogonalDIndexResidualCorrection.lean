import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailLinearExtension
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticCorrection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic

/-! A literal twice-tail is corrected against an original companion
vector. It retains an exact original-coordinate left inverse, preserves
the SAME quadratic form, and is orthogonal to both positive head axes.
No Witt decomposition or full orthogonal-group theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGHyperbolicTransverseCorrection
open CFSGOrthogonalDIndexQuadraticCorrection
variable (K : Type) [Field K]

theorem positive_polar (r : ℕ) (i : Fin r) (v : Index r → K) :
    (splitQuadraticForm K r).polarBilin (Pi.single (Sum.inl i) 1) v = v (Sum.inr i) := by
  rw [splitQuadraticForm_polar]
  simp [polar, leftPart, rightPart, dotProduct, Pi.single_apply, ite_mul, mul_ite]

theorem positive_quadratic (r : ℕ) (i : Fin r) :
    splitQuadraticForm K r (Pi.single (Sum.inl i) 1) = 0 := by
  rw [splitQuadraticForm_apply]
  simp [splitQ, leftPart, rightPart, dotProduct, Pi.single_apply]

private theorem tailIndex_ne_positive_head (n : ℕ) (i : Index n) :
    tailIndex n i ≠ Sum.inl (0 : Fin (n + 1)) := by
  intro he
  have hh : tailEquiv n (Sum.inl i) = tailEquiv n (Sum.inr 0) := he
  cases (tailEquiv n).injective hh

theorem twiceTailRestriction_first (n : ℕ) :
    twiceTailRestriction K n (Pi.single (Sum.inl (0 : Fin (n + 2))) 1) = 0 := by
  funext i
  change (Pi.single (Sum.inl (0 : Fin (n + 2))) (1 : K) : Index (n + 2) → K)
    (tailIndex (n + 1) (tailIndex n i)) = 0
  simp only [Pi.single_apply, if_neg (tailIndex_ne_positive_head (n + 1) _)]

theorem twiceTailRestriction_second (n : ℕ) :
    twiceTailRestriction K n (Pi.single (Sum.inl (tailSecondIndex n)) 1) = 0 := by
  funext i
  change (Pi.single (Sum.inl (tailSecondIndex n)) (1 : K) : Index (n + 2) → K)
    (tailIndex (n + 1) (tailIndex n i)) = 0
  have hn : tailIndex (n + 1) (tailIndex n i) ≠ Sum.inl (tailSecondIndex n) := by
    change tailIndex (n + 1) (tailIndex n i) ≠ tailIndex (n + 1) (Sum.inl 0)
    exact (tailIndex_injective (n + 1)).ne (tailIndex_ne_positive_head n i)
  simp only [Pi.single_apply, if_neg hn]

def residualMap (n : ℕ) (w : Index (n + 2) → K) :
    (Index n → K) →ₗ[K] (Index (n + 2) → K) :=
  correction (splitQuadraticForm K (n + 2)).polarBilin
    (Pi.single (Sum.inl (tailSecondIndex n)) 1) w (twiceTailExtension K n)

theorem residualMap_leftInverse (n : ℕ) (w : Index (n + 2) → K) (z : Index n → K) :
    twiceTailRestriction K n (residualMap K n w z) = z :=
  correction_leftInverse _ _ _ _ _ (twiceTail_leftInverse K n) (twiceTailRestriction_second K n) z

theorem residualMap_injective (n : ℕ) (w : Index (n + 2) → K) :
    Function.Injective (residualMap K n w) := by
  intro z z' he
  have hh := congrArg (twiceTailRestriction K n) he
  simpa only [residualMap_leftInverse] using hh

theorem residualMap_quadratic (n : ℕ) (w : Index (n + 2) → K) (z : Index n → K) :
    splitQuadraticForm K (n + 2) (residualMap K n w z) = splitQuadraticForm K n z := by
  have he : splitQuadraticForm K (n + 2) (Pi.single (Sum.inl (tailSecondIndex n)) 1) = 0 :=
    positive_quadratic K (n + 2) (tailSecondIndex n)
  have hje (t : Index n → K) : (splitQuadraticForm K (n + 2)).polarBilin
      (twiceTailExtension K n t) (Pi.single (Sum.inl (tailSecondIndex n)) 1) = 0 := by
    have hs : (splitQuadraticForm K (n + 2)).polarBilin (twiceTailExtension K n t)
        (Pi.single (Sum.inl (tailSecondIndex n)) 1) =
        (splitQuadraticForm K (n + 2)).polarBilin (Pi.single (Sum.inl (tailSecondIndex n)) 1)
          (twiceTailExtension K n t) :=
      QuadraticMap.polar_comm (splitQuadraticForm K (n + 2) : (Index (n + 2) → K) → K) _ _
    exact hs.trans ((positive_polar K (n + 2) (tailSecondIndex n) _).trans
      (twiceTail_negative_second K n t))
  change splitQuadraticForm K (n + 2) (correction (splitQuadraticForm K (n + 2)).polarBilin
    (Pi.single (Sum.inl (tailSecondIndex n)) 1) w (twiceTailExtension K n) z) = _
  rw [correction_quadratic _ _ _ _ he hje z, splitQuadraticForm_apply, splitQuadraticForm_apply]
  exact twiceTail_norm K n z

theorem residualMap_perp_companion (n : ℕ) (w : Index (n + 2) → K)
    (hw : (splitQuadraticForm K (n + 2)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex n)) 1) ≠ 0) (z : Index n → K) :
    (splitQuadraticForm K (n + 2)).polarBilin w (residualMap K n w z) = 0 :=
  correction_orthogonal _ _ _ _ hw z

theorem residualMap_perp_positive (n : ℕ) (w : Index (n + 2) → K) (z : Index n → K)
    (i : Fin (n + 2)) (hi : i = 0 ∨ i = tailSecondIndex n) :
    (splitQuadraticForm K (n + 2)).polarBilin (Pi.single (Sum.inl i) 1)
      (residualMap K n w z) = 0 := by
  apply correction_orthogonal_to
  · rw [positive_polar]
    simp only [Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, if_false]
  · intro t
    rcases hi with rfl | rfl
    · rw [positive_polar, twiceTail_negative_zero]
    · rw [positive_polar, twiceTail_negative_second]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection

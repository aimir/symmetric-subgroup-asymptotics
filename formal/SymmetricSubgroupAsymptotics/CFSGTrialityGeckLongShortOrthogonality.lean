import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
import SymmetricSubgroupAsymptotics.CFSGTrialityD4InvariantRoots

/-! A positive short orbit orthogonal to each signed long relative root.
The nine literal D4 pairings are the selected centralizer-count pilot;
there is no exceptional group census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongShortOrthogonality
open CFSGIntegerMatrixPairing CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckSectionRootLabels CFSGTrialityD4InvariantRoots

def centralizerShort : Fin 3 → Fin 3 := ![2,1,0]

theorem short_long_pairing (s k : Fin 3) :
    integerPairing (CartanMatrix.D 4) (shortLabel (centralizerShort s) k).val
      (longRoot s).val = 0 := by
  fin_cases s <;> fin_cases k <;>
    norm_num [centralizerShort,shortLabel,shortRoot,longRoot,shortCoordinates,longCoordinates,
      cycle,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,integerPairing,Matrix.toBilin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      CFSGTrialityD4PositiveRootOrbits.cartan_eq]

theorem short_signed_long_pairing (neg : Bool) (s k : Fin 3) :
    integerPairing (CartanMatrix.D 4) (shortLabel (centralizerShort s) k).val
      (signedLongRoot neg s).val = 0 := by
  classical
  cases neg
  · exact short_long_pairing s k
  · have hn := CFSGNormTwoGeckColumns.negative_val (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) CFSGTrialityD4NormTwo.D4_positive_definite (longRoot s)
    have hp := congrArg (fun v : Fin 4 → ℤ =>
      integerPairing (CartanMatrix.D 4) (shortLabel (centralizerShort s) k).val v) hn
    have hz : integerPairing (CartanMatrix.D 4)
        (shortLabel (centralizerShort s) k).val (-(longRoot s).val) = 0 := by
      rw [map_neg,short_long_pairing,neg_zero]
    simpa only [signedLongRoot,if_true,negativeRoot] using hp.trans hz


end SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongShortOrthogonality

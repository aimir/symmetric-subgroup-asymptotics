import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixGroupTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! The actual triality-fixed positive element consisting of the three
outer simple roots at parameter one and the central simple root at one.
All four simple leading coordinates are exactly one, in every field;
there is no trace, norm, or division-by-three condition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRegularFixedPositive
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckFixedRootWords
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGSerreQuadraticMatrix

def regularPositive (K : Type) [Field K] : Positive K :=
  positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K 0 1 *
    positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K 2 1 *
    positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K 3 1 *
    positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K 1 1

theorem regularPositive_val (K : Type) [Field K] (σ : K ≃+* K) :
    (regularPositive K).val = shortOrbit K σ false 1 * canonicalRoot rawData K false 1 1 := by
  simp only [regularPositive, Subgroup.coe_mul, positiveRoot, shortOrbit, map_one]
  rfl

theorem regularPositive_fixed (K : Type) [Field K] (σ : K ≃+* K) :
    positiveTwist K σ (regularPositive K) = regularPositive K := by
  apply Subtype.ext
  rw [positiveTwist_val, regularPositive_val K σ, map_mul,
    shortOrbit_fixed K σ false 1 (by simp), unitTwist_raw_root, map_one σ]
  rfl

theorem regularPositive_leading (K : Type) [Field K] (i : Fin 4) :
    leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K (regularPositive K).val i = 1 := by
  change (leadingHom (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (regularPositive K)).toAdd i = 1
  simp only [regularPositive, map_mul, leadingHom_positiveRoot]
  change ((Pi.single 0 (1 : K) + Pi.single 2 1 + Pi.single 3 1 + Pi.single 1 1 : Fin 4 → K) i) = 1
  fin_cases i <;> simp

def regularMatrix (K : Type) [Field K] : MatrixGroup K := positiveInclusion K (regularPositive K)

theorem regularMatrix_positive (K : Type) [Field K] : (regularMatrix K).val ∈ Positive K :=
  (regularPositive K).property

theorem regularMatrix_fixed (K : Type) [Field K] (σ : K ≃+* K) :
    matrixGroupTwist K σ (regularMatrix K) = regularMatrix K := by
  apply Subtype.ext
  change unitTwist K σ (regularPositive K).val = (regularPositive K).val
  have hh := congrArg (fun u : Positive K => u.val) (regularPositive_fixed K σ)
  dsimp only at hh
  rw [positiveTwist_val] at hh
  exact hh

theorem regularMatrix_leading (K : Type) [Field K] (i : Fin 4) :
    leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K (regularMatrix K).val i ≠ 0 := by
  change leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (regularPositive K).val i ≠ 0
  rw [regularPositive_leading]
  exact one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRegularFixedPositive

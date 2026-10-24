import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalHom
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailVectorAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankQuadraticForm
import SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalHom

/-! The literal D tail embedding normalizes the literal whole point
radical, acting on its parameter by the SAME natural tail matrix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalNormalizer

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDPointRadicalHom
open CFSGOrthogonalDIndexTailCoordinates CFSGOrthogonalDIndexPositiveSpace
open CFSGSplitQuadraticPoleCoordinates CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexAllRankQuadraticForm
variable (K : Type) [Field K]

theorem tail_coordinates (s : ℕ) (g : elementaryRootGroup K (s + 2))
    (v : Index (s + 3) → K) :
    coordinates K (s + 2)
      (((tailElementaryHom K (s + 2) (by omega) g).val : Mat K (s + 3)) *ᵥ v) =
      QuadraticHyperbolicRadicalHom.levi (naturalLinearHom K (s + 2) g)
        (coordinates K (s + 2) v) := by
  apply Prod.ext
  · exact tailElementaryHom_head_positive K (s + 2) (by omega) g v
  · apply Prod.ext
    · exact tailElementaryHom_tail_action K (s + 2) (by omega) g v
    · exact tailElementaryHom_head_negative K (s + 2) (by omega) g v

theorem tail_preserves_quadratic (s : ℕ) (g : elementaryRootGroup K (s + 2))
    (z : Index (s + 2) → K) :
    splitQuadraticForm K (s + 2) (naturalLinearHom K (s + 2) g z) =
      splitQuadraticForm K (s + 2) z := by
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
  exact elementary_preserves_splitQ_all_ranks K (s + 2) (by omega) g z

theorem tail_radical_intertwine (s : ℕ) (g : elementaryRootGroup K (s + 2))
    (z : Index (s + 2) → K) (v : Index (s + 3) → K) :
    ((tailElementaryHom K (s + 2) (by omega) g).val : Mat K (s + 3)) *ᵥ
        poleShear K (s + 2) z v =
      poleShear K (s + 2) (naturalLinearHom K (s + 2) g z)
        (((tailElementaryHom K (s + 2) (by omega) g).val : Mat K (s + 3)) *ᵥ v) := by
  apply (coordinateEquiv K (s + 2)).injective
  change coordinates K (s + 2) _ = coordinates K (s + 2) _
  rw [tail_coordinates, coordinates_poleShear, coordinates_poleShear, tail_coordinates]
  exact QuadraticHyperbolicRadicalHom.levi_transform
    (splitQuadraticForm K (s + 2)) (naturalLinearHom K (s + 2) g)
    (tail_preserves_quadratic K s g) z (coordinates K (s + 2) v)

theorem tail_radical_commutation (s : ℕ) (g : elementaryRootGroup K (s + 2))
    (z : Index (s + 2) → K) :
    tailElementaryHom K (s + 2) (by omega) g * radicalHom K s (Multiplicative.ofAdd z) =
      radicalHom K s (Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z)) *
        tailElementaryHom K (s + 2) (by omega) g := by
  have he : ∀ v : Index (s + 3) → K,
      (((tailElementaryHom K (s + 2) (by omega) g).val : Mat K (s + 3)) *
        ((radicalHom K s (Multiplicative.ofAdd z)).val : Mat K (s + 3))) *ᵥ v =
      (((radicalHom K s (Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z))).val :
        Mat K (s + 3)) *
        ((tailElementaryHom K (s + 2) (by omega) g).val : Mat K (s + 3))) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      radicalHom_apply, radicalHom_apply]
    exact tail_radical_intertwine K s g z v
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h := congrFun (he (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem radical_tail_conjugation (s : ℕ) (g : elementaryRootGroup K (s + 2))
    (z : Index (s + 2) → K) :
    radicalHom K s (Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z)) =
      tailElementaryHom K (s + 2) (by omega) g *
        radicalHom K s (Multiplicative.ofAdd z) *
          (tailElementaryHom K (s + 2) (by omega) g)⁻¹ := by
  have h := congrArg (fun x : elementaryRootGroup K (s + 3) =>
    x * (tailElementaryHom K (s + 2) (by omega) g)⁻¹)
    (tail_radical_commutation K s g z)
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using h.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalNormalizer

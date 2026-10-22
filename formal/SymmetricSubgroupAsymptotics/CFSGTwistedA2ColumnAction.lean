import SymmetricSubgroupAsymptotics.CFSGTwistedA2IsometricColumns
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentWeyl

/-! First-column action bookkeeping for the literal rank-one words.
This preserves the actual matrices and avoids implicit function-coercion
rewrites during Gaussian elimination. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices
variable (K : Type) [Field K]

def firstColumn (M : Mat K 2) : Fin 3 → K := fun i => M i 0

theorem firstColumn_mul (A B : Mat K 2) :
    firstColumn K (A * B) = A.mulVec (firstColumn K B) := rfl

theorem weyl_second_vector (t : K) (ht : t ≠ 0) :
    (((weylNatural K t).val : Mat K 2)).mulVec ![0, 0, 1] =
      t • (![1, 0, 0] : Fin 3 → K) := by
  rw [weylNatural_array K t ht]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul]

theorem upper_clear_column (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (M : Mat K 2)
    (hform : (σ.toRingHom.mapMatrix M).transpose *
        (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) * M =
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2)) (h20 : M 2 0 ≠ 0) :
    ∃ a b, NormCondition σ a b ∧
      firstColumn K (((upperNatural K σ a b).val : Mat K 2) * M) =
        M 2 0 • (![0, 0, 1] : Fin 3 → K) := by
  obtain ⟨a, b, hab, hc⟩ := exists_upper_clear_vector σ hσ (firstColumn K M)
    (isometric_first_column σ M hform) h20
  refine ⟨a, b, hab, ?_⟩
  rw [firstColumn_mul, upperNatural_val]
  exact hc

theorem weyl_after_column_clear (σ : K ≃+* K) (t : K) (ht : t ≠ 0)
    (M : Mat K 2) (a b : K)
    (hc : firstColumn K (((upperNatural K σ a b).val : Mat K 2) * M) =
      M 2 0 • (![0, 0, 1] : Fin 3 → K)) :
    firstColumn K ((((weylNatural K t).val : Mat K 2) *
        ((upperNatural K σ a b).val : Mat K 2)) * M) =
      (t * M 2 0) • (![1, 0, 0] : Fin 3 → K) := by
  rw [mul_assoc, firstColumn_mul, hc, Matrix.mulVec_smul, weyl_second_vector K t ht,
    smul_smul, mul_comm (M 2 0) t]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays

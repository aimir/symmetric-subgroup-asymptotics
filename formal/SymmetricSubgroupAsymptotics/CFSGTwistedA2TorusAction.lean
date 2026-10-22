import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentGroup

/-! Exact diagonal action on the two genuine unipotent parameter layers.
The first weight is z²/σz and the central weight is zσz, with kσk=n. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
open CFSGTwistedANaturalMatrices CFSGTwistedA2UnipotentArrays
variable (K : Type) [Field K] (σ : K ≃+* K)

def firstWeight (z : K) : K := z ^ 2 / σ z

def centralWeight (z : K) : K := z * σ z

theorem centralWeight_fixed (hσ : Function.Involutive σ) (z : K) :
    σ (centralWeight K σ z) = centralWeight K σ z := by
  rw [centralWeight, map_mul, hσ, mul_comm]

theorem firstWeight_norm (hσ : Function.Involutive σ) (z : K) (hz : z ≠ 0) :
    firstWeight K σ z * σ (firstWeight K σ z) = centralWeight K σ z := by
  simp only [firstWeight, centralWeight, map_div₀, map_pow, hσ z]
  field_simp [hz, (map_ne_zero σ).mpr hz] <;> ring

set_option maxHeartbeats 600000 in
theorem torus_conjugate_upper (hσ : Function.Involutive σ) (z : K) (hz : z ≠ 0)
    (a b : K) :
    torusNatural K σ z * upperNatural K σ a b * (torusNatural K σ z)⁻¹ =
      upperNatural K σ (firstWeight K σ z * a) (centralWeight K σ z * b) := by
  apply Subtype.ext
  apply Units.ext
  change ((torusNatural K σ z).val : Mat K 2) *
      ((upperNatural K σ a b).val : Mat K 2) *
        (↑((torusNatural K σ z).val⁻¹) : Mat K 2) = _
  rw [torusNatural_unit K σ z hz, upperNatural_val, upperNatural_val]
  change Matrix.diagonal (torusWeights K σ z) * upperArray σ a b *
    Matrix.diagonal (torusInverseWeights K σ z) =
      upperArray σ (firstWeight K σ z * a) (centralWeight K σ z * b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, upperArray,
      torusWeights, torusInverseWeights, firstWeight, centralWeight,
      map_mul, map_div₀, map_pow, hσ z] <;>
    field_simp [hz, (map_ne_zero σ).mpr hz] <;> ring

end SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus

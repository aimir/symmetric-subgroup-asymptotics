import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentScalarRigidity
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentNatural
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel

/-! Equality in the actual natural action is enough to transport literal
upper arrays. The genuine scalar action kernel is removed by nilpotence,
including in characteristic three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices
variable (K : Type) [Field K]

theorem elementary_action_eq_scalar (x y : NaturalElementary K 2)
    (he : naturalElementaryAction K 2 x = naturalElementaryAction K 2 y) :
    ∃ c : K, (x.val : Mat K 2) = c • (y.val : Mat K 2) := by
  have hk : x * y⁻¹ ∈ (naturalElementaryAction K 2).ker := by
    change naturalElementaryAction K 2 (x * y⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [naturalElementaryAction_ker K 2 (by decide)] at hk
  obtain ⟨c, hc⟩ := (naturalElementary_center_iff_scalar K 2 (by decide) (x * y⁻¹)).mp hk
  refine ⟨c, ?_⟩
  calc
    (x.val : Mat K 2) = ((x * y⁻¹).val : Mat K 2) * (y.val : Mat K 2) := by
      change (x.val : Mat K 2) =
        ((x.val : Mat K 2) * (↑(y.val⁻¹) : Mat K 2)) * (y.val : Mat K 2)
      rw [mul_assoc, Units.inv_mul, mul_one]
    _ = c • (y.val : Mat K 2) := by rw [hc, smul_mul_assoc, one_mul]

theorem upper_conjugate_of_action_eq (σ : K ≃+* K) (u : NaturalElementary K 2)
    (a b c d : K)
    (he : naturalElementaryAction K 2 (u * upperNatural K σ a b * u⁻¹) =
      naturalElementaryAction K 2 (upperNatural K σ c d)) :
    (u.val : Mat K 2) * upperArray σ a b * (↑(u.val⁻¹) : Mat K 2) =
      upperArray σ c d := by
  obtain ⟨s, hs⟩ := elementary_action_eq_scalar K _ _ he
  change (u.val : Mat K 2) * (upperNatural K σ a b).val.val *
      (↑(u.val⁻¹) : Mat K 2) = s • (upperNatural K σ c d).val.val at hs
  rw [upperNatural_val, upperNatural_val] at hs
  have hsone := upperArray_scalar_of_conjugate σ a b c d u.val s hs
  simpa only [hsone, one_smul] using hs

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays

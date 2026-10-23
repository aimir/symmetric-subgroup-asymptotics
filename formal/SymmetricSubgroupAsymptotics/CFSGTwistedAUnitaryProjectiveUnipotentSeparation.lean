import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveCover
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRootLabels

/-! Equal original projective images of genuine defining-characteristic
p-elements are equal natural matrices. The scalar ambiguity is proved
from the actual cover kernel and eliminated by literal p-powers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryMatrixSupport

theorem unitaryProjectiveCover_eq_scalar (q : CFSG.PrimePower) (s : ℕ)
    (x y : naturalFixed (s + 3) q)
    (he : unitaryProjectiveCover q s x = unitaryProjectiveCover q s y) :
    ∃ c : q.Extension 2, (x.val.val : Mat (q.Extension 2) (s + 3)) = c • y.val.val := by
  have hk : unitaryProjectiveCover q s (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (unitaryProjectiveCover_kernel_iff_scalar q s (x * y⁻¹)).mp hk
  refine ⟨c, ?_⟩
  calc
    (x.val.val : Mat (q.Extension 2) (s + 3)) =
        ((x * y⁻¹).val.val : Mat (q.Extension 2) (s + 3)) * y.val.val := by
      change (x.val.val : Mat (q.Extension 2) (s + 3)) =
        ((x.val.val : Mat (q.Extension 2) (s + 3)) *
          (↑(y.val.val⁻¹) : Mat (q.Extension 2) (s + 3))) * y.val.val
      rw [mul_assoc, Units.inv_mul, mul_one]
    _ = c • y.val.val := by rw [hc, smul_mul_assoc, one_mul]

theorem unitaryProjectiveCover_eq_of_p_powers (q : CFSG.PrimePower) (s : ℕ)
    (x y : naturalFixed (s + 3) q)
    (hx : ∃ a : ℕ, x ^ (q.prime ^ a) = 1)
    (hy : ∃ b : ℕ, y ^ (q.prime ^ b) = 1)
    (he : unitaryProjectiveCover q s x = unitaryProjectiveCover q s y) : x = y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨c, hc⟩ := unitaryProjectiveCover_eq_scalar q s x y he
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hxu : x.val.val ^ (q.prime ^ a) = 1 :=
    congrArg (fun t : naturalFixed (s + 3) q => t.val.val) ha
  have hyu : y.val.val ^ (q.prime ^ b) = 1 :=
    congrArg (fun t : naturalFixed (s + 3) q => t.val.val) hb
  have hc1 : c = 1 := scalar_eq_one_of_p_powers q.prime x.val.val y.val.val a b c hxu hyu hc
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa only [hc1, one_smul] using hc

theorem naturalCentralRootLine_p_power (q : CFSG.PrimePower) (s : ℕ)
    (x : naturalFixed (s + 3) q) (hx : x ∈ naturalCentralRootLine q (s + 1)) :
    ∃ a : ℕ, x ^ (q.prime ^ a) = 1 := by
  rw [naturalCentralRootLine_eq_center_image] at hx
  obtain ⟨u, _, rfl⟩ := hx
  obtain ⟨a, ha⟩ := naturalUnipotent_isPGroup (s + 3) q u
  refine ⟨a, ?_⟩
  have he := congrArg (upperFixedHom q (s + 3)) ha
  simpa only [map_pow, map_one] using he

theorem conjugateNaturalCentralRootLine_p_power (q : CFSG.PrimePower) (s : ℕ)
    (g x : naturalFixed (s + 3) q) (hx : x ∈ conjugateNaturalCentralRootLine q (s + 1) g) :
    ∃ a : ℕ, x ^ (q.prime ^ a) = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨a, ha⟩ := naturalCentralRootLine_p_power q s u hu
  refine ⟨a, ?_⟩
  change (g * u * g⁻¹) ^ (q.prime ^ a) = 1
  rw [conj_pow, ha, mul_one, mul_inv_cancel]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

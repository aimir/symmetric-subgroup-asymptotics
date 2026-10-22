import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryScalarPowers
import SymmetricSubgroupAsymptotics.CFSGTwistedAUpperUnipotent
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel
import Mathlib.Algebra.Group.Conj

/-! Original action equality transports actual upper elements without
scalar ambiguity. The SAME-source action kernel is genuinely scalar,
and the two actual upper elements are genuine defining-characteristic
p-elements. No ambient simplicity or full-unitary recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryMatrixSupport

theorem natural_action_eq_scalar (K : Type) [Field K] (r : ℕ) (hr : 1 ≤ r)
    (x y : NaturalElementary K r)
    (he : naturalElementaryAction K r x = naturalElementaryAction K r y) :
    ∃ c : K, (x.val : Mat K r) = c • (y.val : Mat K r) := by
  have hk : x * y⁻¹ ∈ (naturalElementaryAction K r).ker := by
    change naturalElementaryAction K r (x * y⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [naturalElementaryAction_ker K r hr] at hk
  obtain ⟨c, hc⟩ := (naturalElementary_center_iff_scalar K r hr (x * y⁻¹)).mp hk
  refine ⟨c, ?_⟩
  calc
    (x.val : Mat K r) = ((x * y⁻¹).val : Mat K r) * (y.val : Mat K r) := by
      change (x.val : Mat K r) =
        ((x.val : Mat K r) * (↑(y.val⁻¹) : Mat K r)) * (y.val : Mat K r)
      rw [mul_assoc, Units.inv_mul, mul_one]
    _ = c • (y.val : Mat K r) := by rw [hc, smul_mul_assoc, one_mul]

theorem upper_conjugate_of_action_eq (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (w : NaturalElementary (q.Extension 2) r) (u v : naturalUnipotent r q)
    (he : naturalElementaryAction (q.Extension 2) r (w * u.val * w⁻¹) =
      naturalElementaryAction (q.Extension 2) r v.val) :
    w * u.val * w⁻¹ = v.val := by
  obtain ⟨c, hc⟩ := natural_action_eq_scalar (q.Extension 2) r hr _ _ he
  obtain ⟨a, ha⟩ := naturalUnipotent_isPGroup r q u
  obtain ⟨b, hb⟩ := naturalUnipotent_isPGroup r q v
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hu : u.val.val ^ (q.prime ^ a) = 1 :=
    congrArg (fun x : naturalUnipotent r q => x.val.val) ha
  have hv : v.val.val ^ (q.prime ^ b) = 1 :=
    congrArg (fun x : naturalUnipotent r q => x.val.val) hb
  have hconj : (w.val * u.val.val * w.val⁻¹) ^ (q.prime ^ a) = 1 := by
    rw [conj_pow, hu, mul_one, mul_inv_cancel]
  have hone : c = 1 := scalar_eq_one_of_p_powers q.prime _ v.val.val a b c hconj hv hc
  apply Subtype.ext
  apply Units.ext
  simpa only [hone, one_smul] using hc

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

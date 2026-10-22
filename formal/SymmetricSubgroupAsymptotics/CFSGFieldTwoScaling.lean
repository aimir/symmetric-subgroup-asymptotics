import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! Over a two-element field both the field-automorphism factor and
all integral diagonal-scaling cokernels are trivial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFieldTwoScaling
open CFSGIntegerMatrixPowerHom
variable (K : Type*) [Field K] [Finite K]

theorem fieldAut_card_le_one (hK : Nat.card K = 2) : Nat.card (K ≃+* K) ≤ 1 := by
  have h := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb K
  have he : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  have hreal : (Nat.card (K ≃+* K) : ℝ) ≤ 1 := by
    simpa only [hK, Nat.cast_ofNat, he] using h
  exact_mod_cast hreal

theorem scaling_index_le_one {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hK : Nat.card K = 2) :
    (powerHom A : (I → Kˣ) →* (I → Kˣ)).range.index ≤ 1 := by
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have hp : Nat.card (I → Kˣ) = 1 := by rw [Nat.card_fun, hu, one_pow]
  have hd := (powerHom A : (I → Kˣ) →* (I → Kˣ)).range.index_dvd_card
  rw [hp] at hd
  exact Nat.le_of_dvd (by decide) hd

end SymmetricSubgroupAsymptotics.CFSGFieldTwoScaling

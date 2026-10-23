import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-! The scalar weight z^2/sigma(z) for an involutive field
automorphism. Its kernel lies in the actual cube roots of unity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGInvolutiveScalarWeights
variable {K : Type*} [Field K]

def weightHom (sigma : K ≃+* K) : Kˣ →* Kˣ where
  toFun z := z ^ 2 * (Units.map sigma.toMonoidHom z)⁻¹
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_pow, map_mul, mul_inv_rev]
    ac_rfl

theorem weightHom_val (sigma : K ≃+* K) (z : Kˣ) :
    (weightHom sigma z : K) = (z : K) ^ 2 / sigma z := by
  simp [weightHom, div_eq_mul_inv]

theorem kernel_cube (sigma : K ≃+* K) (h : Function.Involutive sigma)
    (z : Kˣ) (hz : z ∈ (weightHom sigma).ker) : z ^ 3 = 1 := by
  have hv : (weightHom sigma z : K) = 1 := congrArg (fun u : Kˣ => (u : K)) hz
  rw [weightHom_val] at hv
  have hs : (z : K) ^ 2 = sigma z :=
    (div_eq_one_iff_eq ((map_ne_zero sigma).mpr (Units.ne_zero z))).mp hv
  have hh := congrArg sigma hs
  rw [map_pow, h, ← hs, ← pow_mul] at hh
  apply Units.ext
  change (z : K) ^ 3 = 1
  apply mul_right_cancel₀ (Units.ne_zero z)
  simpa only [← pow_succ, one_mul] using hh

theorem kernel_card_le_gcd [Finite K] (sigma : K ≃+* K) (h : Function.Involutive sigma) :
    Nat.card (weightHom sigma).ker ≤ (Nat.card K - 1).gcd 3 := by
  let f : (weightHom sigma).ker → (powMonoidHom 3 : Kˣ →* Kˣ).ker :=
    fun z => ⟨z.val, kernel_cube sigma h z.val z.property⟩
  have hf : Function.Injective f := by
    intro z w he
    have hv : z.val = w.val := congrArg (fun a : (powMonoidHom 3 : Kˣ →* Kˣ).ker => a.val) he
    exact Subtype.ext hv
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [IsCyclic.card_powMonoidHom_ker, Nat.card_units] using hc

theorem range_card_mul_gcd_lower [Finite K] (sigma : K ≃+* K)
    (h : Function.Involutive sigma) :
    Nat.card K - 1 ≤ (Nat.card K - 1).gcd 3 * Nat.card (weightHom sigma).range := by
  have he : Nat.card Kˣ = Nat.card (weightHom sigma).ker * Nat.card (weightHom sigma).range := by
    rw [← (weightHom sigma).ker.card_mul_index, Subgroup.index_ker]
  have hc := Nat.mul_le_mul_right (Nat.card (weightHom sigma).range) (kernel_card_le_gcd sigma h)
  rwa [← he, Nat.card_units] at hc

end SymmetricSubgroupAsymptotics.CFSGInvolutiveScalarWeights

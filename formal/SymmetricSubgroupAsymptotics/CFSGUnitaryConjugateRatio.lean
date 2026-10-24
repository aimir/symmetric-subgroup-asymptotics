import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The actual quadratic-field conjugate ratio has q+1 unit values.
Its kernel consists of the literal fixed-subfield units, and every
ratio has norm one. No cyclic-generator choice or Hilbert-90 callback
is needed for this image count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField CFSGTwistedANaturalMatrices

def unitaryConjugateRatioHom (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ where
  toFun a := Units.map (definingFieldAutomorphism q 2).toMonoidHom a * a⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

theorem unitaryConjugateRatioHom_val (q : CFSG.PrimePower) (a : (q.Extension 2)ˣ) :
    (unitaryConjugateRatioHom q a : q.Extension 2) = definingFieldAutomorphism q 2 a / a := by
  simp [unitaryConjugateRatioHom, div_eq_mul_inv]

theorem unitaryConjugateRatio_norm (q : CFSG.PrimePower) (a : (q.Extension 2)ˣ) :
    definingFieldAutomorphism q 2 (unitaryConjugateRatioHom q a : q.Extension 2) *
      (unitaryConjugateRatioHom q a : q.Extension 2) = 1 := by
  rw [unitaryConjugateRatioHom_val]
  have hs : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 (a : q.Extension 2)) =
      (a : q.Extension 2) := extension_two_pow_twice q a
  rw [map_div₀, hs]
  field_simp [Units.ne_zero a, (map_ne_zero (definingFieldAutomorphism q 2)).mpr (Units.ne_zero a)]

theorem unitaryConjugateRatio_ker_iff (q : CFSG.PrimePower) (a : (q.Extension 2)ˣ) :
    a ∈ (unitaryConjugateRatioHom q).ker ↔ definingFieldAutomorphism q 2 a = a := by
  constructor
  · intro ha
    have hv := congrArg (fun z : (q.Extension 2)ˣ => (z : q.Extension 2)) ha
    change (unitaryConjugateRatioHom q a : q.Extension 2) = 1 at hv
    rw [unitaryConjugateRatioHom_val] at hv
    exact (div_eq_one_iff_eq (Units.ne_zero a)).mp hv
  · intro ha
    change unitaryConjugateRatioHom q a = 1
    apply Units.ext
    rw [unitaryConjugateRatioHom_val, ha]
    exact div_self (Units.ne_zero a)

theorem unitaryConjugateRatio_kernel_card (q : CFSG.PrimePower) :
    Nat.card (unitaryConjugateRatioHom q).ker = q.order - 1 := by
  let e : (unitaryConjugateRatioHom q).ker ≃ (fixedField q)ˣ := {
    toFun a := Units.mk0
      (⟨(a.val : q.Extension 2), (unitaryConjugateRatio_ker_iff q a.val).mp a.property⟩ : fixedField q)
      (by
        intro ha
        exact Units.ne_zero a.val (congrArg Subtype.val ha))
    invFun a := ⟨Units.map (fixedField q).subtype.toMonoidHom a, by
      rw [unitaryConjugateRatio_ker_iff]
      exact a.val.property⟩
    left_inv a := by apply Subtype.ext; apply Units.ext; rfl
    right_inv a := by apply Units.ext; apply Subtype.ext; rfl }
  rw [Nat.card_congr e, Nat.card_units, fixedField_card]

theorem unitaryConjugateRatio_range_card (q : CFSG.PrimePower) :
    Nat.card (unitaryConjugateRatioHom q).range = q.order + 1 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have he : Nat.card (q.Extension 2)ˣ = Nat.card (unitaryConjugateRatioHom q).ker *
      Nat.card (unitaryConjugateRatioHom q).range := by
    rw [← (unitaryConjugateRatioHom q).ker.card_mul_index, Subgroup.index_ker]
  rw [Nat.card_units, extension_two_card, unitaryConjugateRatio_kernel_card] at he
  have hf : q.order ^ 2 - 1 = (q.order - 1) * (q.order + 1) := by
    have h1 : q.order - 1 + 1 = q.order := Nat.sub_add_cancel (by omega)
    have h2 : q.order ^ 2 - 1 + 1 = q.order ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  apply Nat.eq_of_mul_eq_mul_left (show 0 < q.order - 1 by omega)
  exact he.symm.trans hf

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

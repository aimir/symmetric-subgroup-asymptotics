import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusParameters
import Mathlib.GroupTheory.Index

/-! The literal paired torus parameter image has index at most two in
fixed-field units times norm-one units. This is actual finite-field
algebra and does not assert a parabolic or fixed-group decomposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusIndex
open CFSGTwistedDRelativeTorusParameters CFSGTwistedDNormOneUnits
open CFSGTwistedA2FixedField CFSGTwistedANaturalMatrices

theorem kernel_card_le_two (q : CFSG.PrimePower) :
    Nat.card (torusParameterHom q).ker ≤ 2 := by
  classical
  let code : (torusParameterHom q).ker → Bool := fun c => decide ((c.val : q.Extension 2) = 1)
  have hi : Function.Injective code := by
    intro c d he
    have hc := kernel_square_one q c.val c.property
    have hd := kernel_square_one q d.val d.property
    change decide ((c.val : q.Extension 2) = 1) = decide ((d.val : q.Extension 2) = 1) at he
    have hiff : ((c.val : q.Extension 2) = 1 ↔ (d.val : q.Extension 2) = 1) := decide_eq_decide.mp he
    by_cases hc1 : (c.val : q.Extension 2) = 1
    · have hd1 := hiff.mp hc1
      exact Subtype.ext (Units.ext (hc1.trans hd1.symm))
    · have hd1 : (d.val : q.Extension 2) ≠ 1 := fun h => hc1 (hiff.mpr h)
      have hcneg : (c.val : q.Extension 2) = -1 := (sq_eq_one_iff.mp hc).resolve_left hc1
      have hdneg : (d.val : q.Extension 2) = -1 := (sq_eq_one_iff.mp hd).resolve_left hd1
      exact Subtype.ext (Units.ext (hcneg.trans hdneg.symm))
  simpa using Nat.card_le_card_of_injective code hi

theorem parameter_card_le_extension_units (q : CFSG.PrimePower) :
    Nat.card ((fixedField q)ˣ × normOneUnits q) ≤ Nat.card (q.Extension 2)ˣ := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : Nat.card (fixedField q)ˣ = q.order - 1 := by
    rw [Nat.card_units, fixedField_card]
  have he : Nat.card (q.Extension 2)ˣ = q.order ^ 2 - 1 := by
    rw [Nat.card_units, extension_two_card]
  have hm : (q.order - 1) * (q.order + 1) = q.order ^ 2 - 1 := by
    have hs : q.order - 1 + 1 = q.order := Nat.sub_add_cancel (by omega)
    have ht : q.order ^ 2 - 1 + 1 = q.order ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  calc
    Nat.card ((fixedField q)ˣ × normOneUnits q) =
      Nat.card (fixedField q)ˣ * Nat.card (normOneUnits q) := Nat.card_prod _ _
    _ ≤ (q.order - 1) * (q.order + 1) := by
      rw [hf]
      exact Nat.mul_le_mul_left _ (normOneUnits_card_le q)
    _ = Nat.card (q.Extension 2)ˣ := hm.trans he.symm

theorem torus_parameter_index_le_two (q : CFSG.PrimePower) :
    (torusParameterHom q).range.index ≤ 2 := by
  let f := torusParameterHom q
  have hk := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hk
  have hm : Nat.card f.range * f.range.index ≤ Nat.card f.range * 2 := by
    calc
      Nat.card f.range * f.range.index =
        Nat.card ((fixedField q)ˣ × normOneUnits q) := f.range.card_mul_index
      _ ≤ Nat.card (q.Extension 2)ˣ := parameter_card_le_extension_units q
      _ = Nat.card f.ker * Nat.card f.range := hk.symm
      _ ≤ 2 * Nat.card f.range := Nat.mul_le_mul_right _ (kernel_card_le_two q)
      _ = Nat.card f.range * 2 := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hm Nat.card_pos

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusIndex

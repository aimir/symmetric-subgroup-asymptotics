import SymmetricSubgroupAsymptotics.CFSGTrialityNormTorusScalars
import Mathlib.Tactic.Linarith

/-! The literal three-factor Frobenius norm is onto the actual cubic
fixed field, on elements and on units. Finite-field norm surjectivity
and the proved cardinalities identify the norm without an additional
group-theoretic or fixed-point-surjectivity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityCubicNormSurjectivity
open CFSGTrialityNormTorusScalars CFSGTrialityFixedField CFSGTrialityTripleFixedRoots
open CFSGSerreOrdinaryTwists

theorem norm_exponent (q : CFSG.PrimePower) :
    (q.order^3 - 1) / (q.order - 1) = q.order^2 + q.order + 1 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hs : q.order - 1 + 1 = q.order := Nat.sub_add_cancel (by omega)
  have hp : 1 ≤ q.order^3 := Nat.one_le_pow _ _ (by omega)
  have ht : q.order^3 - 1 + 1 = q.order^3 := Nat.sub_add_cancel hp
  have hm : (q.order^2 + q.order + 1) * (q.order - 1) = q.order^3 - 1 := by nlinarith
  rw [← hm, Nat.mul_div_cancel _ (by omega : 0 < q.order - 1)]

theorem normFieldHom_val (q : CFSG.PrimePower) (a : q.Extension 3) :
    ((normFieldHom q a : fixedField q) : q.Extension 3) = a^(q.order^2 + q.order + 1) := by
  change a * a^q.order * (a^q.order)^q.order = _
  rw [← pow_mul]
  calc
    _ = a^(1 + q.order + q.order*q.order) := by rw [pow_add, pow_add, pow_one]
    _ = _ := by congr 1; ring

theorem normFieldHom_surjective (q : CFSG.PrimePower) :
    Function.Surjective (normFieldHom q) := by
  intro c
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective (fixedField q) (q.Extension 3) c
  have hp := FiniteField.algebraMap_norm_eq_pow
    (K := fixedField q) (K' := q.Extension 3) (x := a)
  rw [ha] at hp
  change (c : q.Extension 3) =
    a^((Nat.card (q.Extension 3) - 1) / (Nat.card (fixedField q) - 1)) at hp
  rw [extension_three_card, fixedField_card, norm_exponent] at hp
  refine ⟨a, Subtype.ext ?_⟩
  exact (normFieldHom_val q a).trans hp.symm

theorem normUnits_surjective (q : CFSG.PrimePower) :
    Function.Surjective (normUnits q) := by
  intro c
  obtain ⟨a, ha⟩ := normFieldHom_surjective q (c : fixedField q)
  have ha0 : a ≠ 0 := by
    intro he
    have hz : normFieldHom q a = 0 := by
      rw [he]
      apply Subtype.ext
      simp [normFieldHom]
    exact c.ne_zero (ha.symm.trans hz)
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  exact ha

end SymmetricSubgroupAsymptotics.CFSGTrialityCubicNormSurjectivity

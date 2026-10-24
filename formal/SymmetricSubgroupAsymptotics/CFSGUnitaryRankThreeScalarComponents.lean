import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeAxisColumns
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-! Scalar components of literal fixed-field columns. A component
intersection forces the scalar ratio to be fixed. Binary fixed fields
have only the nonzero scalar one; two nonfixed scalar components are
disjoint in every field. No subgroup or norm-shell census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedA2FixedField

theorem rankOneFixedColumn_card (q : CFSG.PrimePower) :
    Nat.card (rankOneFixedColumn q) = q.order ^ 2 - 1 := by
  classical
  let V := Fin 2 → rankOneFixedField q
  letI : Fintype V := Fintype.ofFinite V
  have hc : Nat.card {x : V // x ≠ 0} = Nat.card V - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun x : V => x = 0))
  have hF : Nat.card (rankOneFixedField q) = q.order := fixedField_card q
  change Nat.card {x : V // x ≠ 0} = _
  rw [hc, Nat.card_fun, Nat.card_fin, hF]

theorem exists_unitaryConjugateRatio_not_fixed (q : CFSG.PrimePower) :
    ∃ z : (unitaryConjugateRatioHom q).range,
      definingFieldAutomorphism q 2 (z.val : q.Extension 2) ≠ (z.val : q.Extension 2) := by
  classical
  by_contra hn
  push Not at hn
  have hs (z : (unitaryConjugateRatioHom q).range) : z.val = 1 ∨ z.val = -1 := by
    have hnorm : definingFieldAutomorphism q 2 (z.val : q.Extension 2) *
        (z.val : q.Extension 2) = 1 := by
      obtain ⟨u, hu⟩ := z.property
      rw [← hu]
      exact unitaryConjugateRatio_norm q u
    have hsq : z.val ^ 2 = (1 : (q.Extension 2)ˣ) ^ 2 := by
      apply Units.ext
      change (z.val : q.Extension 2) ^ 2 = (1 : q.Extension 2) ^ 2
      rw [pow_two, one_pow]
      exact (congrArg (fun a : q.Extension 2 => a * (z.val : q.Extension 2)) (hn z).symm).trans hnorm
    exact Units.eq_or_eq_neg_of_sq_eq_sq _ _ hsq
  let f : (unitaryConjugateRatioHom q).range → Bool := fun z => if z.val = 1 then true else false
  have hf : Function.Injective f := by
    intro z w he
    by_cases hz : z.val = 1 <;> by_cases hw : w.val = 1
    · exact Subtype.ext (hz.trans hw.symm)
    · change (if z.val = 1 then true else false) = (if w.val = 1 then true else false) at he
      rw [if_pos hz, if_neg hw] at he
      cases he
    · change (if z.val = 1 then true else false) = (if w.val = 1 then true else false) at he
      rw [if_neg hz, if_pos hw] at he
      cases he
    · exact Subtype.ext (((hs z).resolve_left hz).trans ((hs w).resolve_left hw).symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [unitaryConjugateRatio_range_card] at hc
  have hBool : Nat.card Bool = 2 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hBool] at hc
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  omega

theorem scalarColumn_intersection_forces_fixed (q : CFSG.PrimePower)
    (a d : q.Extension 2) (ha : a ≠ 0) (x y : rankOneFixedColumn q)
    (he : rankOneScalarColumn q a x = rankOneScalarColumn q (d * a) y) :
    definingFieldAutomorphism q 2 d = d := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, y.val i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact y.property (funext hn)
  have hiK : (y.val i : q.Extension 2) ≠ 0 := fun h => hi (Subtype.ext h)
  have hh := congrFun he i
  change a * (x.val i : q.Extension 2) = (d * a) * (y.val i : q.Extension 2) at hh
  have hxy : (x.val i : q.Extension 2) = d * (y.val i : q.Extension 2) := by
    apply mul_left_cancel₀ ha
    exact hh.trans (by ring)
  have hs := congrArg (definingFieldAutomorphism q 2) hxy
  change definingFieldAutomorphism q 2 (x.val i : q.Extension 2) =
    definingFieldAutomorphism q 2 (d * (y.val i : q.Extension 2)) at hs
  rw [map_mul, (show definingFieldAutomorphism q 2 (x.val i : q.Extension 2) =
    (x.val i : q.Extension 2) from (x.val i).property),
    (show definingFieldAutomorphism q 2 (y.val i : q.Extension 2) =
      (y.val i : q.Extension 2) from (y.val i).property)] at hs
  exact mul_right_cancel₀ hiK (hs.symm.trans hxy)

private theorem field_card_two_nonzero_eq_one {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) (x : F) (hx : x ≠ 0) : x = 1 := by
  letI : Fintype F := Fintype.ofFinite F
  have hs : x ^ 2 = x := by
    simpa only [← Nat.card_eq_fintype_card, hF] using FiniteField.pow_card x
  have hp : x * (x - 1) = 0 := by linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hx)

theorem binary_ratio_scalarColumn_injective (q : CFSG.PrimePower) (hq : q.order = 2)
    (a : q.Extension 2) (ha : a ≠ 0) :
    Function.Injective (fun p : (unitaryConjugateRatioHom q).range × rankOneFixedColumn q =>
      rankOneScalarColumn q ((p.1.val : q.Extension 2) * a) p.2) := by
  classical
  intro p t he
  change rankOneScalarColumn q ((p.1.val : q.Extension 2) * a) p.2 =
    rankOneScalarColumn q ((t.1.val : q.Extension 2) * a) t.2 at he
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, p.2.val i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact p.2.property (funext hn)
  have hiK : (p.2.val i : q.Extension 2) ≠ 0 := fun h => hi (Subtype.ext h)
  have hc := congrFun he i
  change ((p.1.val : q.Extension 2) * a) * (p.2.val i : q.Extension 2) =
    ((t.1.val : q.Extension 2) * a) * (t.2.val i : q.Extension 2) at hc
  have hti : t.2.val i ≠ 0 := by
    intro ht
    have htK : (t.2.val i : q.Extension 2) = 0 := congrArg Subtype.val ht
    rw [htK, mul_zero] at hc
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero p.1.val) ha) hiK hc
  have hF : Nat.card (rankOneFixedField q) = 2 := (fixedField_card q).trans hq
  have hp1 := field_card_two_nonzero_eq_one hF (p.2.val i) hi
  have ht1 := field_card_two_nonzero_eq_one hF (t.2.val i) hti
  have hpK : (p.2.val i : q.Extension 2) = 1 := congrArg Subtype.val hp1
  have htK : (t.2.val i : q.Extension 2) = 1 := congrArg Subtype.val ht1
  rw [hpK, htK, mul_one, mul_one] at hc
  have hz : p.1 = t.1 := Subtype.ext (Units.ext (mul_right_cancel₀ ha hc))
  apply Prod.ext hz
  apply rankOneScalarColumn_injective q ((p.1.val : q.Extension 2) * a)
    (mul_ne_zero (Units.ne_zero p.1.val) ha)
  simpa only [hz] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

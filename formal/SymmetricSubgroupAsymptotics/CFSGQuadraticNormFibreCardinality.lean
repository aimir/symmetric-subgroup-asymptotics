import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.Ring

/-! Exact fibres of the literal quadratic-extension norm, with values
in its actual Frobenius fixed field. Cyclic-unit kernel counting gives
q+1 at each nonzero value; no unitary group is identified or counted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticNormFibreCardinality
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField CFSGTwistedANaturalMatrices
open CFSGTwistedA2UnipotentArrays CFSGTwistedDNormOneUnits

def normMap (q : CFSG.PrimePower) : q.Extension 2 →*₀ fixedField q where
  toFun a := ⟨a*definingFieldAutomorphism q 2 a, by
    change definingFieldAutomorphism q 2 (a*definingFieldAutomorphism q 2 a)=
      a*definingFieldAutomorphism q 2 a
    have hs : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a)=a :=
      extension_two_pow_twice q a
    rw [map_mul,hs]
    exact mul_comm _ _⟩
  map_zero' := Subtype.ext (by
    change (0 : q.Extension 2)*definingFieldAutomorphism q 2 0=0
    simp only [zero_mul])
  map_one' := Subtype.ext (by
    change (1 : q.Extension 2)*definingFieldAutomorphism q 2 1=1
    simp only [map_one,one_mul])
  map_mul' a b := Subtype.ext (by
    change (a*b)*definingFieldAutomorphism q 2 (a*b)=
      (a*definingFieldAutomorphism q 2 a)*(b*definingFieldAutomorphism q 2 b)
    rw [map_mul]
    ring)

theorem normMap_surjective (q : CFSG.PrimePower) : Function.Surjective (normMap q) := by
  intro c
  obtain ⟨a,ha⟩ := exists_norm_eq_fixed q c.val c.property
  exact ⟨a,Subtype.ext ha⟩

private theorem normMap_eq_zero_iff (q : CFSG.PrimePower) (a : q.Extension 2) :
    normMap q a=0 ↔ a=0 := by
  constructor
  · intro ha
    have hh := congrArg (fun c : fixedField q => c.val) ha
    change a*definingFieldAutomorphism q 2 a=0 at hh
    rcases mul_eq_zero.mp hh with h | h
    · exact h
    · exact (definingFieldAutomorphism q 2).injective (h.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

private def normUnitsHom (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* (fixedField q)ˣ :=
  Units.map (normMap q).toMonoidHom

private theorem normUnitsHom_value (q : CFSG.PrimePower) (u : (q.Extension 2)ˣ) :
    ((normUnitsHom q u : fixedField q) : q.Extension 2) =
      (u : q.Extension 2)^(q.order+1) := by
  change (u : q.Extension 2)*definingFieldAutomorphism q 2 (u : q.Extension 2)=_
  rw [definingFieldAutomorphism_apply,pow_succ]
  ring

private theorem normUnitsHom_surjective (q : CFSG.PrimePower) :
    Function.Surjective (normUnitsHom q) := by
  intro c
  obtain ⟨a,ha⟩ := normMap_surjective q (c : fixedField q)
  have ha0 : a ≠ 0 := by
    intro he
    exact Units.ne_zero c (ha.symm.trans ((normMap_eq_zero_iff q a).mpr he))
  refine ⟨Units.mk0 a ha0,?_⟩
  apply Units.ext
  exact ha

private theorem normUnitsHom_kernel_card (q : CFSG.PrimePower) :
    Nat.card (normUnitsHom q).ker=q.order+1 := by
  have hk : (normUnitsHom q).ker=normOneUnits q := by
    ext u
    change normUnitsHom q u=1 ↔ u^(q.order+1)=1
    constructor
    · intro hu
      have hh := congrArg (fun c : (fixedField q)ˣ => ((c : fixedField q) : q.Extension 2)) hu
      change ((normUnitsHom q u : fixedField q) : q.Extension 2)=1 at hh
      rw [normUnitsHom_value] at hh
      exact Units.ext hh
    · intro hu
      apply Units.ext
      apply Subtype.ext
      calc
        _ = (u : q.Extension 2)^(q.order+1) := normUnitsHom_value q u
        _ = 1 := congrArg (fun z : (q.Extension 2)ˣ => (z : q.Extension 2)) hu
  rw [hk]
  change Nat.card (powMonoidHom (q.order+1) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker=_
  rw [IsCyclic.card_powMonoidHom_ker,Nat.card_units,extension_two_card]
  apply Nat.gcd_eq_right
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  refine ⟨q.order-1,?_⟩
  have hp : q.order-1+1=q.order := by omega
  have hs : q.order^2-1+1=q.order^2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  nlinarith

theorem normMap_zero_fibre_card (q : CFSG.PrimePower) :
    Nat.card {a : q.Extension 2 // normMap q a=0}=1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (normMap_eq_zero_iff q))]
  simp

private def nonzeroFibreUnitsEquiv (q : CFSG.PrimePower) (c : fixedField q) (hc : c ≠ 0) :
    {a : q.Extension 2 // normMap q a=c} ≃
      {u : (q.Extension 2)ˣ // normUnitsHom q u=Units.mk0 c hc} where
  toFun a := ⟨Units.mk0 a.val (by
    intro ha
    exact hc (a.property.symm.trans ((normMap_eq_zero_iff q a.val).mpr ha))), by
      apply Units.ext
      exact a.property⟩
  invFun u := ⟨u.val.val,congrArg (fun z : (fixedField q)ˣ => (z : fixedField q)) u.property⟩
  left_inv _ := rfl
  right_inv u := Subtype.ext (Units.ext rfl)

theorem normMap_nonzero_fibre_card (q : CFSG.PrimePower) (c : fixedField q) (hc : c ≠ 0) :
    Nat.card {a : q.Extension 2 // normMap q a=c}=q.order+1 := by
  rw [Nat.card_congr (nonzeroFibreUnitsEquiv q c hc)]
  exact (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective
    (normUnitsHom_surjective q) (Units.mk0 c hc))).trans (normUnitsHom_kernel_card q)

end SymmetricSubgroupAsymptotics.CFSGQuadraticNormFibreCardinality

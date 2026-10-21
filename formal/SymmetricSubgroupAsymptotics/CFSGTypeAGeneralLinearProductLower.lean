import SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! A uniform elementary lower bound for the actual GL order product.
It includes degree three over the field of two elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearProductLower

private theorem product_gt_square (q d : ℕ) (hq : 2≤q) (hd : 2≤d) :
    (q^(d+1)-1)^2<∏ i : Fin (d+1), (q^(d+1)-q^i.val) := by
  have hdouble : q^d+q^d≤q^(d+1) := by
    calc
      q^d+q^d=q^d*2 := (Nat.mul_two _).symm
      _≤q^d*q := Nat.mul_le_mul_left _ hq
      _=q^(d+1) := (pow_succ q d).symm
  have hfactor (i : Fin d) : q^d≤q^(d+1)-q^(i.val+1) := by
    have hi : q^(i.val+1)≤q^d := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.le_sub_of_add_le ((Nat.add_le_add_left hi _).trans hdouble)
  have hprod : q^(d*d)≤∏ i : Fin d, (q^(d+1)-q^(i.val+1)) := by
    have hh := Finset.prod_le_prod' (s:=Finset.univ)
      (fun (i : Fin d) _ => hfactor i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul] using hh
  have hexp : d+1≤d*d := by nlinarith
  have hp : q^(d+1)≤q^(d*d) := Nat.pow_le_pow_right (by omega) hexp
  have hpos : 1<q^(d+1) := one_lt_pow' (by omega : 1<q) (by omega)
  have htail : q^(d+1)-1<∏ i : Fin d, (q^(d+1)-q^(i.val+1)) := by
    exact (by omega : q^(d+1)-1<q^(d+1)).trans_le (hp.trans hprod)
  have hh := Nat.mul_lt_mul_of_pos_left htail (by omega : 0<q^(d+1)-1)
  rw [Fin.prod_univ_succ]
  simpa only [Fin.val_zero,pow_zero,Fin.val_succ,pow_two] using hh

theorem generalLinear_card_gt_power_sub_one_square (F : Type*) [Field F] [Finite F]
    (n : ℕ) (hn : 3≤n) :
    (Nat.card F^n-1)^2<Nat.card (Matrix.GeneralLinearGroup (Fin n) F) := by
  letI : Fintype F := Fintype.ofFinite F
  have hq : 2≤Fintype.card F := by
    have hh : 1<Nat.card F := Finite.one_lt_card
    rw [Nat.card_eq_fintype_card] at hh
    omega
  cases n with
  | zero => omega
  | succ d =>
    rw [Matrix.card_GL_field]
    simpa only [Nat.card_eq_fintype_card] using product_gt_square (Fintype.card F) d hq (by omega)

end SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearProductLower

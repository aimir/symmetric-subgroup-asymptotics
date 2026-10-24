import SymmetricSubgroupAsymptotics.NilpotentTraceOneNormLift
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Group

/-! Every selfadjoint unit of a finite commutative characteristic-two
star ring is an actual norm when a trace-one element exists. Odd powers
and the checked nilpotent norm lift give the construction. No norm
surjectivity or classification theorem is a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FiniteTraceOneUnitNorm
open NilpotentTraceOneNormLift

variable {R : Type*} [CommRing R] [CharP R 2] [StarRing R]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem exists_norm_of_odd_power_order (u : R) (hu : u+star u=1)
    (s : Rˣ) (hs : star (s:R)=(s:R)) (k m : ℕ) (hm : Odd m)
    (horder : s^(2^k*m)=1) : ∃ T : R, T*star T=(s:R) := by
  obtain ⟨l, hl⟩ := hm
  have hexp : (l+1)+(l+1)=m+1 := by omega
  let U : Rˣ := (s^m)⁻¹
  have hU : U^(2^k)=1 := by
    change ((s^m)⁻¹)^(2^k)=1
    rw [inv_pow, ←pow_mul, Nat.mul_comm m (2^k), horder, inv_one]
  have hUv : (U:R)^(2^k)=1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun a : Rˣ => (a:R)) hU
  have hUs : star (U:R)=(U:R) := by
    have hsu : star s=s := Units.ext hs
    have he : star U=U := by simp only [U, star_inv, star_pow, hsu]
    simpa only [Units.coe_star] using congrArg (fun a : Rˣ => (a:R)) he
  let z : R := (U:R)-1
  have hzs : star z=z := by simp only [z, star_sub, hUs, star_one]
  have hzn : z^(2^k)=0 := by
    dsimp only [z]
    rw [sub_pow_char_pow, hUv, one_pow, sub_self]
  obtain ⟨T, hT⟩ := exists_norm_eq_one_add u z hu hzs k hzn
  have hT' : T*star T=(U:R) := by
    calc
      _ = 1+z := hT
      _ = _ := by dsimp only [z]; ring
  let a : R := (s:R)^(l+1)
  have ha : star a=a := by simp only [a, star_pow, hs]
  have hmul : s^(l+1)*s^(l+1)*U=s := by
    rw [←pow_add, hexp, pow_succ]
    dsimp only [U]
    group
  refine ⟨a*T, ?_⟩
  calc
    _ = (a*a)*(T*star T) := by rw [star_mul, ha]; ring
    _ = (a*a)*(U:R) := congrArg (fun x:R => (a*a)*x) hT'
    _ = (s:R) := by
      simpa only [a, Units.val_mul, Units.val_pow_eq_pow_val] using
        congrArg (fun a:Rˣ => (a:R)) hmul

theorem exists_unit_norm [Finite R] (u : R) (hu : u+star u=1)
    (s : Rˣ) (hs : star (s:R)=(s:R)) :
    ∃ T : Rˣ, (T:R)*star (T:R)=(s:R) := by
  letI : Finite Rˣ := Finite.of_injective (fun a : Rˣ => (a:R)) Units.val_injective
  letI : Fintype Rˣ := Fintype.ofFinite _
  obtain ⟨k,m,hm,he⟩ := Nat.exists_eq_two_pow_mul_odd
    (Nat.ne_of_gt (Fintype.card_pos (α:=Rˣ)))
  have horder : s^(2^k*m)=1 := by
    rw [←he]
    exact pow_card_eq_one
  obtain ⟨T,hT⟩ := exists_norm_of_odd_power_order u hu s hs k m hm horder
  have huT : IsUnit (T*star T) := by rw [hT]; exact s.isUnit
  obtain ⟨t,ht⟩ := isUnit_of_mul_isUnit_left huT
  exact ⟨t, ht.symm ▸ hT⟩

end SymmetricSubgroupAsymptotics.FiniteTraceOneUnitNorm

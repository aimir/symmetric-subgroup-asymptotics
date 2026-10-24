import SymmetricSubgroupAsymptotics.SLTwoProjectiveClassHalving
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpClassCube

/-! Odd-characteristic projective class halving, on the original PSL2
model. A small prime-power interval is discharged by arithmetic rather
than finite action enumeration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube
open PrimitiveSocleRawStructure

private theorem odd_small_exponent_one (p e : ℕ) (hp : p.Prime) (he : 0<e)
    (hpodd : p≠2) (hlo : 13 ≤ p^e) (hhi : p^e ≤ 16) : e=1 := by
  by_contra hne
  have he2 : 2 ≤ e := by omega
  have hp3 : 3 ≤ p := by have h:=hp.two_le; omega
  have hp5 : p<5 := by
    by_contra h
    have hb := (Nat.pow_le_pow_left (by omega : 5 ≤ p) 2).trans
      (Nat.pow_le_pow_right hp.pos he2)
    norm_num at hb
    omega
  have hpne4 : p≠4 := by intro h; subst p; exact (by decide : ¬Nat.Prime 4) hp
  have hp_eq : p=3 := by omega
  subst p
  have he3 : e<3 := by
    by_contra h
    have hb := Nat.pow_le_pow_right (by decide : 0<3) (by omega : 3 ≤ e)
    norm_num at hb
    omega
  have heq : e=2 := by omega
  subst e
  norm_num at hlo

theorem twice_class_card_le (q : CFSG.PrimePower) (hp : q.prime≠2) :
    2*Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ q.order+5 := by
  have hchar : ringChar q.Field≠2 := by simpa only [ringChar.eq q.Field q.prime] using hp
  simpa only [q.card_field] using
    SLTwoProjectiveClassHalving.twice_projective_class_card_le q.Field hchar

theorem half_field_square_le_order (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ((q.order+1)/2)^2 ≤ Nat.card (CFSG.Models.A 1 q) := by
  have h : q.order*(q.order-1)*(q.order+1) ≤ 2*Nat.card (CFSG.Models.A 1 q) := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.twice_projective_card_ge_classical_order (F:=q.Field)
  have hlo : 2*q.order^2 ≤ q.order*(q.order-1)*(q.order+1) := by
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left q.order (show 2 ≤ q.order-1 by omega))
      (Nat.le_succ q.order)
    convert hb using 1 <;> ring
  have hsq : q.order^2 ≤ Nat.card (CFSG.Models.A 1 q) := by omega
  exact (Nat.pow_le_pow_left (show (q.order+1)/2 ≤ q.order by omega) 2).trans hsq

theorem component_class_cube (q : CFSG.PrimePower) (hq : 13 ≤ q.order)
    (hp : q.prime≠2) :
    (Nat.card (ConjClasses (CFSG.Models.A 1 q))*Nat.card (Outer (CFSG.Models.A 1 q)))^3 ≤
      5^((q.order+1)/2-1) := by
  by_cases hbig : 17 ≤ q.order
  · exact CFSGTypeARankOneSharpClassCube.component_class_cube q hbig
  · have he : q.exponent=1 := odd_small_exponent_one q.prime q.exponent q.prime_isPrime
      q.exponent_pos hp hq (show q.order ≤ 16 by omega)
    have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ 10 := by
      have h := twice_class_card_le q hp
      omega
    have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2 := by
      have h := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
      omega
    have hbound := Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3
    have hpow : 5^6 ≤ 5^((q.order+1)/2-1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact hbound.trans ((by decide : (10*2)^3 ≤ 5^6).trans hpow)

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube

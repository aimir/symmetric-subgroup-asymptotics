import SymmetricSubgroupAsymptotics.CFSGPSLTwoOddTorusCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube
import Mathlib.Data.Nat.Prime.Int

/-! Actual order, class and outer data for the original nine-element
field model. No exceptional A6 identification is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneCardNine
open PrimitiveSocleRawStructure

theorem parameters (q : CFSG.PrimePower) (hq : q.order=9) : q.prime=3 ∧ q.exponent=2 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
    q.exponent_pos.ne' (by decide : (2:ℕ)≠0) (show q.prime^q.exponent=3^2 from hq)

theorem card_eq (q : CFSG.PrimePower) (hq : q.order=9) :
    Nat.card (CFSG.Models.A 1 q)=360 := by
  have hp := (parameters q hq).1
  have hchar : ringChar q.Field≠2 := by rw [ringChar.eq q.Field q.prime,hp]; decide
  have h := CFSGPSLTwoOddTorusCardinality.twice_projective_card_eq (F:=q.Field) hchar
  change 2*Nat.card (CFSG.Models.A 1 q)=(Nat.card q.Field-1)*Nat.card q.Field*(Nat.card q.Field+1) at h
  rw [q.card_field,hq] at h
  omega

theorem class_card_le (q : CFSG.PrimePower) (hq : q.order=9) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ 7 := by
  have hp := (parameters q hq).1
  have h := CFSGTypeARankOneOddClassCube.twice_class_card_le q (by omega)
  omega

theorem outer_card_le (q : CFSG.PrimePower) (hq : q.order=9) :
    Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 4 := by
  have he := (parameters q hq).2
  have h := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
  omega

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneCardNine

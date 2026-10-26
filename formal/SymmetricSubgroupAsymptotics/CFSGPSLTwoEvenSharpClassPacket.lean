import SymmetricSubgroupAsymptotics.SLTwoCharacteristicTwoClassBound
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality
import Mathlib.Data.Nat.Prime.Int

/-! Actual characteristic-two rank-one classes and the field-eight
packet. The SAME full-centre PSL2 quotient is used. No minimum-index9
claim is made: the existing characteristic bound gives8, and8 divides504. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenSharpClassPacket
open PrimitiveSocleRawStructure CFSGPSLTwoRootCoordinates

theorem typeA_rank_one_class_card_le (q : CFSG.PrimePower) (hp : q.prime=2) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q))≤q.order+1 := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 2) q.Field) :=
    Finite.of_injective (fun g:Matrix.SpecialLinearGroup (Fin 2) q.Field=>g.val)
      Subtype.val_injective
  letI : Finite (ConjClasses (Matrix.SpecialLinearGroup (Fin 2) q.Field)) :=
    Finite.of_surjective (@ConjClasses.mk (Matrix.SpecialLinearGroup (Fin 2) q.Field) _)
      ConjClasses.mk_surjective
  have hchar : ringChar q.Field=2 := (ringChar.eq q.Field q.prime).trans hp
  have hh := Nat.card_le_card_of_surjective (ConjClasses.map (projection (F:=q.Field)))
    (ConjClasses.map_surjective (projection_surjective (F:=q.Field)))
  exact hh.trans (by simpa only [q.card_field] using
    SLTwoCharacteristicTwoClassBound.class_card_le_field_add_one q.Field hchar)

theorem eight_parameters (q : CFSG.PrimePower) (hq : q.order=8) :
    q.prime=2 ∧ q.exponent=3 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
    q.exponent_pos.ne' (by decide : (3:ℕ)≠0)
    (show q.prime^q.exponent=2^3 from hq)

theorem eight_class_card_le_nine (q : CFSG.PrimePower) (hq : q.order=8) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q))≤9 := by
  have hh := typeA_rank_one_class_card_le q (eight_parameters q hq).1
  omega

theorem eight_outer_card_le_three (q : CFSG.PrimePower) (hq : q.order=8) :
    Nat.card (Outer (CFSG.Models.A 1 q))≤3 := by
  have hh := CFSGPSLTwoEvenOuterBound.typeA_rank_one_outer_card q (eight_parameters q hq).1
  have hf := (eight_parameters q hq).2
  omega

theorem eight_component_class_card_le_twentySeven (q : CFSG.PrimePower) (hq : q.order=8) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q))≤27 :=
  (Nat.mul_le_mul (eight_class_card_le_nine q hq)
    (eight_outer_card_le_three q hq)).trans_eq (by decide : 9*3=27)

theorem eight_order_eq_504 (q : CFSG.PrimePower) (hq : q.order=8) :
    Nat.card (CFSG.Models.A 1 q)=504 := by
  have hp := (eight_parameters q hq).1
  have hchar : ringChar q.Field=2 := (ringChar.eq q.Field q.prime).trans hp
  change Nat.card (PSL (F:=q.Field))=504
  rw [CFSGPSLTwoGeometry.projective_card_eq_torus_mul,
    CFSGPSLTwoEvenOuterBound.pairTorus_card_eq_units hchar,
    Nat.card_units,q.card_field,hq]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenSharpClassPacket

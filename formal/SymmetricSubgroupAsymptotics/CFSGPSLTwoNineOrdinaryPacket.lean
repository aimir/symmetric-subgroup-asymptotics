import SymmetricSubgroupAsymptotics.CFSGTypeARankOneCardNine
import SymmetricSubgroupAsymptotics.SimpleOrderThreeSixty

/-! Actual original PSL2(9) class/outer and proper-index data for the
ordinary small-fibre recurrence. Order360, classes<=7 andOut<=4 were
proved on the literal model. Faithful simple cosets give index>=6;
index7 is excluded by actual order divisibility, whileindex6 is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoNineOrdinaryPacket
open PrimitiveSocleRawStructure

theorem component_class_card_le_twentyEight (q : CFSG.PrimePower) (hq : q.order=9) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q))≤28 :=
  (Nat.mul_le_mul (CFSGTypeARankOneCardNine.class_card_le q hq)
    (CFSGTypeARankOneCardNine.outer_card_le q hq)).trans_eq (by decide : 7*4=28)

theorem proper_index_ge_six (q : CFSG.PrimePower) (hq : q.order=9)
    [IsSimpleGroup (CFSG.Models.A 1 q)]
    (K : Subgroup (CFSG.Models.A 1 q)) (hK : K≠⊤) : 6≤K.index := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 2) q.Field) :=
    Finite.of_injective (fun g:Matrix.SpecialLinearGroup (Fin 2) q.Field=>g.val)
      Subtype.val_injective
  letI : Finite (CFSG.Models.A 1 q) := by
    change Finite (Matrix.SpecialLinearGroup (Fin 2) q.Field ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) q.Field))
    infer_instance
  exact SimpleOrderThreeSixty.proper_index_ge_six
    (CFSGTypeARankOneCardNine.card_eq q hq) K hK

theorem proper_index_ne_seven (q : CFSG.PrimePower) (hq : q.order=9)
    (K : Subgroup (CFSG.Models.A 1 q)) : K.index≠7 := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 2) q.Field) :=
    Finite.of_injective (fun g:Matrix.SpecialLinearGroup (Fin 2) q.Field=>g.val)
      Subtype.val_injective
  letI : Finite (CFSG.Models.A 1 q) := by
    change Finite (Matrix.SpecialLinearGroup (Fin 2) q.Field ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) q.Field))
    infer_instance
  exact SimpleOrderThreeSixty.proper_index_ne_seven
    (CFSGTypeARankOneCardNine.card_eq q hq) K

end SymmetricSubgroupAsymptotics.CFSGPSLTwoNineOrdinaryPacket

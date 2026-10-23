import SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound

/-! The literal original Suzuki matrices provide a sixteen-power
order upper bound. The checked original central-root action and actual
outer reconstruction then give a seventeen-power budget at EVERY
proper subgroup index, without a group order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiProperIndexOrderBudget
open CFSGSuzukiFieldParameters PrimitiveSocleRawStructure

theorem suzuki_order_le_field_sixteen (m : ℕ) :
    Nat.card (CFSG.Models.Suzuki m) ≤ Nat.card (Field m)^16 := by
  let encode : CFSG.Models.Suzuki m → CFSG.Models.SuzukiConstruction.Mat m := fun g => g.val
  have hi : Function.Injective encode := by
    intro g h he
    exact Subtype.ext (Units.ext he)
  have hc := Nat.card_le_card_of_injective encode hi
  have hm : Nat.card (CFSG.Models.SuzukiConstruction.Mat m)=Nat.card (Field m)^16 := by
    change Nat.card (Fin 4 → Fin 4 → Field m)=_
    simp only [Nat.card_fun,Nat.card_fin,←pow_mul,Nat.reduceMul]
  exact hc.trans_eq hm

theorem suzuki_order_mul_outer_le_proper_index_seventeen (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (H : Subgroup (CFSG.Models.Suzuki m)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.Suzuki m)*Nat.card (Outer (CFSG.Models.Suzuki m)) ≤ H.index^17 := by
  have hi := CFSGSuzukiCentralPermutationDegree.field_card_le_proper_index m H hH
  have ho : Nat.card (Outer (CFSG.Models.Suzuki m)) ≤ Nat.card (Field m) := by
    apply (CFSGSuzukiOuterBound.outer_card_le m hm).trans
    rw [field_card]
    exact (2*m+1).lt_two_pow_self.le
  calc
    Nat.card (CFSG.Models.Suzuki m)*Nat.card (Outer (CFSG.Models.Suzuki m)) ≤
        Nat.card (Field m)^16*Nat.card (Field m) :=
      Nat.mul_le_mul (suzuki_order_le_field_sixteen m) ho
    _ ≤ H.index^16*H.index := Nat.mul_le_mul (Nat.pow_le_pow_left hi 16) hi
    _ = H.index^17 := (pow_succ _ 16).symm

end SymmetricSubgroupAsymptotics.CFSGSuzukiProperIndexOrderBudget

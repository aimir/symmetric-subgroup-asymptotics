import SymmetricSubgroupAsymptotics.CFSGSerreEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryEvenOrder

/-! The genuine natural elementary realization removes every type-C
model from the previous exact even-order residual, in all field
characteristics. Other model cases remain explicitly unresolved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def SymplecticIndex : CFSG.Index → Prop
  | .C _ _ _ _ => True
  | _ => False

theorem symplecticIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : SymplecticIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case C r q hr _ hsimple =>
    letI symplecticActualModelSimple : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    exact CFSGSymplecticSerreMatrices.typeC_even_card r q (by omega)

def RemainingEvenOrderModelAfterSymplectic (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterSerreTwo i ∧ ¬ SymplecticIndex i

theorem evenOrder_model_or_remaining_after_symplectic (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterSymplectic i := by
  by_cases hC : SymplecticIndex i
  · exact Or.inl (symplecticIndex_even_card i hC)
  rcases evenOrder_model_or_remaining_after_serre_two i hn with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hC⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_symplectic
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingEvenOrderModelAfterSymplectic i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_symplectic i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction

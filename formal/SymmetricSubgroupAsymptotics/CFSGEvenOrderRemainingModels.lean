import SymmetricSubgroupAsymptotics.CFSGSolvabilityReduction
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Concrete alternating and projective-linear branches of the even-order
reduction. The outstanding other model families remain explicit, so the
odd-order-solvability reduction cannot hide an extra Feit--Thompson premise. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem alternating_even_card (n : ℕ) (hn : 5 ≤ n) :
    Even (Nat.card (alternatingGroup (Fin n))) := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  have hfour : 4 ∣ n.factorial :=
    (by decide : 4 ∣ Nat.factorial 4).trans
      (Nat.factorial_dvd_factorial (by omega : 4 ≤ n))
  obtain ⟨k, hk⟩ := hfour
  refine ⟨k, ?_⟩
  omega

def RemainingEvenOrderModel : CFSG.Index → Prop
  | .cyclic _ _ => False
  | .alternating _ _ => False
  | .A _ _ _ _ => False
  | _ => True

theorem evenOrder_model_or_remaining (i : CFSG.Index) :
    ¬ IsMulCommutative i.Model →
      Even (Nat.card i.Model) ∨ RemainingEvenOrderModel i := by
  cases i <;> try exact fun _ => Or.inr trivial
  case cyclic p hp =>
    intro hn
    exfalso
    apply hn
    change IsMulCommutative (Multiplicative (ZMod p))
    infer_instance
  case alternating n hn =>
    intro _
    exact Or.inl (alternating_even_card n hn)
  case A r q hr hq =>
    intro _
    exact Or.inl (CFSGProjectiveLinearEvenOrder.typeA_even_card r q hr)

theorem odd_order_solvable_of_cfsg_and_remaining_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingEvenOrderModel i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction

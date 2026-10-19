import SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.TypeTags.Finite

/-! Cardinal bounds follow from actual central and active coordinate maps,
including their kernels. They do not identify a split extension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

include D

theorem order_le : Nat.card Q≤4^c*4^d*Nat.card T := by
  have hz : Nat.card D.active.ker≤4^c := by
    calc
      _ ≤ Nat.card (Fin c → Multiplicative (ZMod 4)) :=
        Nat.card_le_card_of_injective _ D.centralCoordinates_injective
      _ = _ := by rw [Nat.card_fun,Nat.card_congr Multiplicative.toAdd]; simp
  have hs : Nat.card ScalarFour=4 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  have hr : Nat.card D.active.range≤4^d := by
    calc
      _ ≤ Nat.card (Fin d → ScalarFour) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = _ := by rw [Nat.card_fun,Nat.card_fin,hs]
  have hk := D.active.ker.card_mul_index
  rw [Subgroup.index_ker] at hk
  have hk' : Nat.card D.top.ker≤4^c*4^d :=
    hk.symm.le.trans (Nat.mul_le_mul hz hr)
  have hq := D.top.ker.card_mul_index
  rw [Subgroup.index_ker,D.top.range_eq_top_of_surjective D.top_surjective,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at hq
  exact hq.symm.le.trans (Nat.mul_le_mul_right (Nat.card T) hk')

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates

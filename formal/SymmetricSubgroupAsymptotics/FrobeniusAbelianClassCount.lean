import SymmetricSubgroupAsymptotics.FrobeniusAbelianCommutingFibres
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact class count for an abelian kernel and abelian complement with
free action away from the kernel identity. Every joint quotient-pair
fibre is counted, including the exceptional identity pair. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FrobeniusAbelianClassCount
open FrobeniusAbelianCommutingFibres

variable {N H : Type*} [CommGroup N] [CommGroup H] (φ : H →* MulAut N)

def commutingEquiv :
    {p : (N ⋊[φ] H) × (N ⋊[φ] H) // Commute p.1 p.2} ≃
      (t : H × H) × Fibre φ t.1 t.2 where
  toFun p := ⟨(p.val.1.right,p.val.2.right),⟨(p.val.1.left,p.val.2.left),p.property⟩⟩
  invFun t := ⟨(⟨t.2.val.1,t.1.1⟩,⟨t.2.val.2,t.1.2⟩),t.2.property⟩
  left_inv _p := rfl
  right_inv _t := rfl

variable [Finite N] [Finite H]
    (hfree : ∀ (h : H), h≠1 → ∀ n : N, φ h n=n → n=1)

include hfree in
theorem commuting_card :
    Nat.card {p : (N ⋊[φ] H) × (N ⋊[φ] H) // Commute p.1 p.2} =
      (Nat.card N)^2+((Nat.card H)^2-1)*Nat.card N := by
  letI : Fintype N := Fintype.ofFinite _
  letI : Fintype H := Fintype.ofFinite _
  rw [Nat.card_congr (commutingEquiv φ),Nat.card_sigma]
  have hrest : (∑t ∈ (Finset.univ : Finset (H × H)).erase (1,1),
      Nat.card (Fibre φ t.1 t.2)) = ((Nat.card H)^2-1)*Nat.card N := by
    calc
      (∑t ∈ (Finset.univ : Finset (H × H)).erase (1,1), Nat.card (Fibre φ t.1 t.2)) =
          ∑_t ∈ (Finset.univ : Finset (H × H)).erase (1,1), Nat.card N := by
        apply Finset.sum_congr rfl
        intro t ht
        have hne : t ≠ (1,1) := (Finset.mem_erase.mp ht).1
        rw [fibre_card φ hfree,if_neg]
        rintro ⟨h1,h2⟩
        exact hne (Prod.ext h1 h2)
      _ = ((Nat.card H)^2-1)*Nat.card N := by
        rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ (1,1)),
          Finset.card_univ,nsmul_eq_mul]
        simp only [Fintype.card_prod,Nat.card_eq_fintype_card,pow_two,Nat.cast_id]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (H × H))
    (fun t => Nat.card (Fibre φ t.1 t.2)) (Finset.mem_univ (1,1)),hrest]
  rw [fibre_card φ hfree,if_pos ⟨rfl,rfl⟩]

include hfree in
theorem class_count :
    Nat.card H*Nat.card (ConjClasses (N ⋊[φ] H))+1 =
      Nat.card N+(Nat.card H)^2 := by
  have hcount := commuting_card φ hfree
  rw [card_comm_eq_card_conjClasses_mul_card,SemidirectProduct.card] at hcount
  have hn : 0 < Nat.card N := Nat.card_pos
  have hh : 0 < Nat.card H := Nat.card_pos
  have hs : (Nat.card H)^2-1+1=(Nat.card H)^2 :=
    Nat.sub_add_cancel (by nlinarith)
  have he : (Nat.card H*Nat.card (ConjClasses (N ⋊[φ] H))+1)*Nat.card N =
      (Nat.card N+(Nat.card H)^2)*Nat.card N := by nlinarith
  exact Nat.le_antisymm (Nat.le_of_mul_le_mul_right he.le hn)
    (Nat.le_of_mul_le_mul_right he.ge hn)

end SymmetricSubgroupAsymptotics.FrobeniusAbelianClassCount

import SymmetricSubgroupAsymptotics.AbelianActionCommutingFibreBound
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Tactic.Ring

/-! Class counts from fixed-space capacities in an abelian semidirect
product with arbitrary complement. Joint commuting quotient pairs are
retained throughout; no Frobenius or abelian-complement premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianActionClassBound
open AbelianActionCommutingFibreBound
variable {N H : Type*} [CommGroup N] [Group H] (phi : H →* MulAut N)

abbrev CommutingPairs (G : Type*) [Group G] := {p : G×G // Commute p.1 p.2}

def commutingEquiv : CommutingPairs (N ⋊[phi] H) ≃
    (t : CommutingPairs H) × Fibre phi t.val.1 t.val.2 where
  toFun p := ⟨⟨(p.val.1.right,p.val.2.right),congrArg SemidirectProduct.right p.property⟩,
    ⟨(p.val.1.left,p.val.2.left),p.property⟩⟩
  invFun t := ⟨(⟨t.2.val.1,t.1.val.1⟩,⟨t.2.val.2,t.1.val.2⟩),t.2.property⟩
  left_inv _p := rfl
  right_inv _t := rfl

variable [Finite N] [Finite H]

theorem commuting_card_le (c : ℕ)
    (hfixed : ∀ h : H, h≠1 → Nat.card {n : N // phi h n=n} ≤ c) :
    Nat.card (CommutingPairs (N ⋊[phi] H)) ≤
      (Nat.card N)^2+Nat.card (CommutingPairs H)*(Nat.card N*c) := by
  letI : Fintype N := Fintype.ofFinite _
  letI : Fintype H := Fintype.ofFinite _
  let t0 : CommutingPairs H := ⟨(1,1),rfl⟩
  rw [Nat.card_congr (commutingEquiv phi),Nat.card_sigma]
  have hpoint (t : CommutingPairs H) : Nat.card (Fibre phi t.val.1 t.val.2) ≤
      (if t=t0 then (Nat.card N)^2 else 0)+Nat.card N*c := by
    by_cases he : t=t0
    · rw [if_pos he]
      have hc : Nat.card (Fibre phi t.val.1 t.val.2) ≤ (Nat.card N)^2 := by
        simpa only [Nat.card_prod,pow_two] using
          Nat.card_le_card_of_injective (fun p : Fibre phi t.val.1 t.val.2 => p.val)
            Subtype.val_injective
      exact hc.trans (Nat.le_add_right _ _)
    · rw [if_neg he,zero_add]
      apply fibre_card_le_off_identity phi c hfixed
      rintro ⟨h1,h2⟩
      exact he (Subtype.ext (Prod.ext h1 h2))
  have hs := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset (CommutingPairs H))) => hpoint t)
  have hi : (∑ t : CommutingPairs H, if t=t0 then (Nat.card N)^2 else 0)=(Nat.card N)^2 := by
    simp
  rw [Finset.sum_add_distrib,hi] at hs
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card] using hs

theorem class_card_mul_complement_le (c : ℕ)
    (hfixed : ∀ h : H, h≠1 → Nat.card {n : N // phi h n=n} ≤ c) :
    Nat.card H*Nat.card (ConjClasses (N ⋊[phi] H)) ≤
      Nat.card N+c*(Nat.card H*Nat.card (ConjClasses H)) := by
  have hc := commuting_card_le phi c hfixed
  rw [card_comm_eq_card_conjClasses_mul_card,SemidirectProduct.card,
    card_comm_eq_card_conjClasses_mul_card] at hc
  have hbound : (Nat.card H*Nat.card (ConjClasses (N ⋊[phi] H)))*Nat.card N ≤
      (Nat.card N+c*(Nat.card H*Nat.card (ConjClasses H)))*Nat.card N := by
    simpa only [pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
      Nat.add_mul,Nat.mul_add] using hc
  exact Nat.le_of_mul_le_mul_right hbound (Nat.card_pos (α := N))

theorem class_card_le_fixed (c : ℕ)
    (hfixed : ∀ h : H, h≠1 → Nat.card {n : N // phi h n=n} ≤ c) :
    Nat.card (ConjClasses (N ⋊[phi] H)) ≤ Nat.card N+c*Nat.card (ConjClasses H) := by
  have hc := commuting_card_le phi c hfixed
  rw [card_comm_eq_card_conjClasses_mul_card,SemidirectProduct.card,
    card_comm_eq_card_conjClasses_mul_card] at hc
  have hn : 0 < Nat.card N := Nat.card_pos
  have hh : 0 < Nat.card H := Nat.card_pos
  have hscale : (Nat.card N)^2 ≤ (Nat.card N)^2*Nat.card H :=
    Nat.le_mul_of_pos_right _ hh
  have hbound : Nat.card (ConjClasses (N ⋊[phi] H))*(Nat.card N*Nat.card H) ≤
      (Nat.card N+c*Nat.card (ConjClasses H))*(Nat.card N*Nat.card H) := by
    apply hc.trans
    calc
      (Nat.card N)^2+(Nat.card (ConjClasses H)*Nat.card H)*(Nat.card N*c) ≤
          (Nat.card N)^2*Nat.card H+(Nat.card (ConjClasses H)*Nat.card H)*(Nat.card N*c) :=
        Nat.add_le_add_right hscale _
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hbound (Nat.mul_pos hn hh)

end SymmetricSubgroupAsymptotics.AbelianActionClassBound

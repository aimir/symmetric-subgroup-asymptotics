import SymmetricSubgroupAsymptotics.AbelianActionCommutingFibreBound
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Ring

/-! Joint commuting-fibre capacity of the SAME two quotient elements.
The capacity is the index of an actual motion image in the abelian
kernel. No independent fixed-space maximum or splitting premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianJointMotionFibres
open FrobeniusAbelianMotion AbelianActionCommutingFibreBound
variable {N H : Type*} [CommGroup N] [Group H] (φ : H →* MulAut N)

def jointMotion (h k : H) : N × N →* N where
  toFun p := motion (φ h) p.2*(motion (φ k) p.1)⁻¹
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul,Prod.snd_mul,map_mul,mul_inv_rev]
    simp only [mul_assoc,mul_comm,mul_left_comm]

theorem jointMotion_apply (h k : H) (a b : N) :
    jointMotion φ h k (a,b) = motion (φ h) b*(motion (φ k) a)⁻¹ := rfl

theorem commute_iff_motion_eq (h k : H) (hcomm : Commute h k) (a b : N) :
    Commute (⟨a,h⟩ : N ⋊[φ] H) (⟨b,k⟩ : N ⋊[φ] H) ↔
      motion (φ h) b = motion (φ k) a := by
  constructor
  · exact motion_eq_of_commute φ h k a b
  · intro he
    change (⟨a,h⟩ : N ⋊[φ] H)*(⟨b,k⟩ : N ⋊[φ] H) =
      (⟨b,k⟩ : N ⋊[φ] H)*(⟨a,h⟩ : N ⋊[φ] H)
    apply SemidirectProduct.ext
    · change a*φ h b = b*φ k a
      change φ h b*b⁻¹ = φ k a*a⁻¹ at he
      have hb : φ h b = (φ k a*a⁻¹)*b := mul_inv_eq_iff_eq_mul.mp he
      rw [hb]
      have ha : a*(φ k a*a⁻¹) = φ k a := by
        calc
          a*(φ k a*a⁻¹) = φ k a*(a*a⁻¹) := by ac_rfl
          _ = φ k a := by rw [mul_inv_cancel,mul_one]
      rw [←mul_assoc,ha]
      exact mul_comm _ _
    · exact hcomm.eq

def commutingFibreEquivKernel (h k : H) (hcomm : Commute h k) :
    Fibre φ h k ≃ (jointMotion φ h k).ker where
  toFun p := ⟨p.val,by
    change motion (φ h) p.val.2*(motion (φ k) p.val.1)⁻¹ = 1
    exact mul_inv_eq_one.mpr (motion_eq_of_commute φ h k _ _ p.property)⟩
  invFun p := ⟨p.val,by
    apply (commute_iff_motion_eq φ h k hcomm _ _).mpr
    exact mul_inv_eq_one.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem commuting_fibre_card [Finite N] (h k : H) (hcomm : Commute h k) :
    Nat.card (Fibre φ h k) = Nat.card N*(jointMotion φ h k).range.index := by
  rw [Nat.card_congr (commutingFibreEquivKernel φ h k hcomm)]
  let f := jointMotion φ h k
  change Nat.card f.ker = Nat.card N*f.range.index
  have hi : f.ker.index = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hk := f.ker.card_mul_index
  rw [hi,Nat.card_prod] at hk
  have hr := f.range.card_mul_index
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range))
  calc
    Nat.card f.ker*Nat.card f.range = Nat.card N*Nat.card N := hk
    _ = Nat.card N*(Nat.card f.range*f.range.index) := congrArg (fun n : ℕ => Nat.card N*n) hr.symm
    _ = (Nat.card N*f.range.index)*Nat.card f.range := by ring

end SymmetricSubgroupAsymptotics.AbelianJointMotionFibres

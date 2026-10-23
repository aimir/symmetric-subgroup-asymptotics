import SymmetricSubgroupAsymptotics.FrobeniusAbelianClassCount
import SymmetricSubgroupAsymptotics.FrobeniusComplementCard
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! The proved exact Frobenius class identity and ACTUAL free complement
orbit give k(N semidirect H)<=|N|. Neither an orbit-size nor a class bound
is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrobeniusAbelianClassBound

variable {N H : Type*} [CommGroup N] [CommGroup H] [Finite N] [Finite H]
    [Nontrivial N] (φ : H →* MulAut N)
    (hfree : ∀ (h : H), h≠1 → ∀ n : N, φ h n=n → n=1)

include hfree in
theorem class_card_le_kernel : Nat.card (ConjClasses (N ⋊[φ] H)) ≤ Nat.card N := by
  have hcount := FrobeniusAbelianClassCount.class_count φ hfree
  have hc := FrobeniusComplementCard.complement_card_le_pred φ hfree
  have hh : 0 < Nat.card H := Nat.card_pos
  let r := Nat.card H-1
  have hr : Nat.card H=r+1 := by dsimp only [r]; omega
  rw [hr] at hcount hc
  have hnr : r+2 ≤ Nat.card N := by omega
  have hprod := Nat.mul_le_mul_left r hnr
  by_contra hk
  have hk' : Nat.card N+1 ≤ Nat.card (ConjClasses (N ⋊[φ] H)) := by omega
  have hkprod := Nat.mul_le_mul_left (r+1) hk'
  nlinarith

end SymmetricSubgroupAsymptotics.FrobeniusAbelianClassBound

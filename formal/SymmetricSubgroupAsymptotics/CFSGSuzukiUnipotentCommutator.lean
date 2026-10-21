import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentGroup
import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameterMaps
import Mathlib.GroupTheory.Commutator.Basic

/-! Actual commutators in the pinned Suzuki unipotent group. For m>=1,
every central unipotent is a single commutator of actual unipotents. -/
set_option autoImplicit false
noncomputable section
open scoped Classical CharTwo commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters

theorem unipotentElement_commutator (m : ℕ) (a b c d : Field m) :
    ⁅unipotentElement m a b, unipotentElement m c d⁆ =
      unipotentElement m 0 (theta m a * c + theta m c * a) := by
  simp only [commutatorElement_def, unipotentElement_inv, unipotentElement_mul, map_add]
  congr 1 <;> ring_nf <;> simp

theorem exists_twist_difference_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    ∃ t : Field m, theta m t + t ≠ 0 := by
  by_contra h
  have hall : ∀ t : Field m, t = 0 ∨ t = 1 := by
    intro t
    exact (theta_add_self_eq_zero_iff m t).mp (not_not.mp (not_exists.mp h t))
  have hi : Function.Injective (fun t : Field m => if t = 0 then false else true) := by
    intro a b hab
    rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp_all
  have hc := Nat.card_le_card_of_injective _ hi
  have hc' : 2 ^ (2 * m + 1) ≤ 2 := by
    simpa only [field_card, Nat.card_eq_fintype_card, Fintype.card_bool] using hc
  have hl : 4 ≤ 2 ^ (2 * m + 1) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ 2 * m + 1)
  omega

/-- Surjectivity here concerns the literal central parameter, rather than
an abstract isomorphic two-group or a normal-generation substitute. -/
theorem every_central_parameter_is_commutator (m : ℕ) (hm : 1 ≤ m) (z : Field m) :
    ∃ a c : Field m,
      ⁅unipotentElement m a 0, unipotentElement m c 0⁆ = unipotentElement m 0 z := by
  obtain ⟨t, ht⟩ := exists_twist_difference_ne_zero m hm
  obtain ⟨a, ha⟩ := (thetaProduct_bijective m).surjective (z / (theta m t + t))
  refine ⟨a, a * t, ?_⟩
  rw [unipotentElement_commutator]
  have he : theta m a * (a * t) + theta m (a * t) * a = z := by
    rw [map_mul]
    calc
      theta m a * (a * t) + (theta m a * theta m t) * a =
          thetaProduct m a * (theta m t + t) := by dsimp only [thetaProduct]; ring
      _ = (z / (theta m t + t)) * (theta m t + t) := congrArg (fun x => x * (theta m t + t)) ha
      _ = z := div_mul_cancel₀ z ht
  exact congrArg (unipotentElement m 0) he

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent

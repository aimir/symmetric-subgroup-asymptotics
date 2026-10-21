import SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleStars

/-! Actual star relations and point-conjugacy compatibility. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingStarRelations
open Equiv Equiv.Perm CFSGAlternatingStarGenerators
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem product_square (a b c d : α) (h : [a,b,c,d].Nodup) :
    (cycle a b c*cycle a b d)^2=1 := by
  ext x
  simp only [pow_two,cycle,Perm.mul_apply,Perm.one_apply,swap_apply_def]
  grind

theorem product_ne_one (a b c d : α) (h : [a,b,c,d].Nodup) :
    cycle a b c*cycle a b d≠1 := by
  intro he
  have hx := congrArg (fun p : Perm α => p a) he
  simp only [cycle,Perm.mul_apply,Perm.one_apply,swap_apply_def] at hx
  grind

theorem cycle_conjugation (σ : Perm α) (a b c : α) :
    σ*cycle a b c*σ⁻¹=cycle (σ a) (σ b) (σ c) := by
  unfold cycle
  calc
    σ*(swap a b*swap b c)*σ⁻¹ = (σ*swap a b)*swap b c*σ⁻¹ := by
      simp only [mul_assoc]
    _ = (swap (σ a) (σ b)*σ)*swap b c*σ⁻¹ := by
      rw [mul_swap_eq_swap_mul σ a b]
    _ = swap (σ a) (σ b)*(σ*swap b c)*σ⁻¹ := by
      simp only [mul_assoc]
    _ = swap (σ a) (σ b)*(swap (σ b) (σ c)*σ)*σ⁻¹ := by
      rw [mul_swap_eq_swap_mul σ b c]
    _ = swap (σ a) (σ b)*swap (σ b) (σ c) := by
      simp only [mul_assoc,mul_inv_cancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGAlternatingStarRelations

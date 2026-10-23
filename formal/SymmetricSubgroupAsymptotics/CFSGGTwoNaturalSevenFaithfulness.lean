import SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointAction
import Mathlib.Tactic.LinearCombination

/-! The already defined literal native seven-space action is faithful
in characteristic three. An arbitrary eight-vector becomes a member of
the invariant hyperplane after adding a scalar multiple of the fixed
axis. This uses characteristic three explicitly and no simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalSevenFaithfulness
open CFSGGTwoSerreMatrices CFSGGTwoInvariantAxis CFSGGTwoAxisCoordinates
open CFSGGTwoSingularPointAction
variable (K : Type) [Field K] [CharP K 3]

theorem natural_eq_one_of_hyperplane_fixed (g : naturalGroup K)
    (hfix : ∀v : axisHyperplane K,(g.val:Mat K) *ᵥ v.val=v.val) : g=1 := by
  have hv (v : Index → K) : (g.val:Mat K) *ᵥ v=v := by
    let a : K := v (pos 3)-v (neg 3)
    let w : Index → K := v+a • axis K
    have hthree : a+a+a=0 := by
      calc
        _=(3:K)*a := by ring
        _=0 := by
          have hc : (3:K)=0 := CharP.cast_eq_zero K 3
          rw [hc,zero_mul]
    have hrel : v (pos 3)+a=v (neg 3)-a := by
      dsimp only [a] at hthree ⊢
      linear_combination hthree
    have hw : w∈axisHyperplane K := by
      change w (pos 3)=w (neg 3)
      dsimp only [w]
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,axis,Pi.sub_apply,
        Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,
        if_true,if_false,sub_zero,zero_sub,mul_one,mul_neg,neg_zero,sub_eq_add_neg,
        Pi.neg_apply,add_zero,zero_add] using hrel
    have he := hfix ⟨w,hw⟩
    change (g.val:Mat K) *ᵥ (v+a • axis K)=v+a • axis K at he
    rw [Matrix.mulVec_add,Matrix.mulVec_smul,natural_fixes_axis] at he
    exact add_right_cancel he
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  change (g.val:Mat K) *ᵥ v=(1:Mat K) *ᵥ v
  simpa only [Matrix.one_mulVec] using hv v

theorem natural_eq_one_of_hyperplane_action_eq_one (g : naturalGroup K)
    (hg : hyperplaneLinearHom K g=1) : g=1 := by
  apply natural_eq_one_of_hyperplane_fixed K g
  intro v
  have he := congrArg (fun e : axisHyperplane K ≃ₗ[K] axisHyperplane K => (e v).val) hg
  change (g.val:Mat K) *ᵥ v.val=v.val at he
  exact he

theorem hyperplaneLinearHom_injective : Function.Injective (hyperplaneLinearHom K) := by
  intro g h he
  have hk : hyperplaneLinearHom K (g⁻¹*h)=1 := by
    rw [map_mul,map_inv,he,inv_mul_cancel]
  exact inv_mul_eq_one.mp (natural_eq_one_of_hyperplane_action_eq_one K (g⁻¹*h) hk)

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalSevenFaithfulness

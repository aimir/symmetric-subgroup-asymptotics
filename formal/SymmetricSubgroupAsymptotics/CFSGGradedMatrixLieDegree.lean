import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Abel

/-! The bracket of two literal homogeneous matrices has the sum degree. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieDegree
open CFSGGradedMatrixSupport
variable {I V K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [CommRing K]

theorem supported_lie (weight : I→V) (d e : V) (M N : Matrix I I K)
    (hM : Supported weight (fun v=>v+d) M) (hN : Supported weight (fun v=>v+e) N) :
    Supported weight (fun v=>v+(d+e)) ⁅M,N⁆ := by
  have hMN : Supported weight (fun v=>v+(d+e)) (M*N) := by
    apply supported_congr (supported_mul hM hN)
    intro v
    dsimp only [Function.comp_apply]
    abel
  have hNM : Supported weight (fun v=>v+(d+e)) (N*M) := by
    apply supported_congr (supported_mul hN hM)
    intro v
    dsimp only [Function.comp_apply]
    abel
  intro i j hij
  rw [Ring.lie_def,Matrix.sub_apply,hMN i j hij,hNM i j hij,sub_self]

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieDegree

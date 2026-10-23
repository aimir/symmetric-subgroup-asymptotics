import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-! Conjugating a literal positive A2 relation gives its opposite-simple
incidence. The Weyl self-root and square-sign equalities are retained as
the exact interfaces used by the actual root-word consumers. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGA2MixedCommutator

theorem mixed_of_positive {K G : Type*} [Ring K] [Group G]
    (u v n : K→G) (W : G)
    (hcomm : ∀ a b, ⁅u a,v b⁆=W*v (a*b)*W⁻¹)
    (hself : ∀ a, W*u a*W⁻¹=n (-a))
    (hsign : ∀ a, W^2*v a=v (-a)*W^2) (a b : K) :
    ⁅n a,W*v b*W⁻¹⁆=v (a*b) := by
  let e : MulAut G := MulAut.conj W
  have he := congrArg e (hcomm (-a) b)
  have hleft : e ⁅u (-a),v b⁆=⁅n a,W*v b*W⁻¹⁆ := by
    change e (u (-a)*v b*(u (-a))⁻¹*(v b)⁻¹)=_
    rw [map_mul,map_mul,map_mul,map_inv,map_inv]
    change (W*u (-a)*W⁻¹)*(W*v b*W⁻¹)*
      (W*u (-a)*W⁻¹)⁻¹*(W*v b*W⁻¹)⁻¹=_
    rw [hself,neg_neg]
    rfl
  have hright : e (W*v ((-a)*b)*W⁻¹)=v (a*b) := by
    change W*(W*v ((-a)*b)*W⁻¹)*W⁻¹=_
    calc
      _=(W^2*v ((-a)*b))*(W^2)⁻¹ := by simp only [pow_two]; group
      _=(v (-((-a)*b))*W^2)*(W^2)⁻¹ := by rw [hsign]
      _=v (-((-a)*b)) := by group
      _=v (a*b) := by rw [neg_mul,neg_neg]
  exact hleft.symm.trans (he.trans hright)

end SymmetricSubgroupAsymptotics.CFSGA2MixedCommutator

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-! A nontrivial normal subgroup of a finite p-group meets its actual
centre nontrivially. The proof uses the original conjugation action on
the normal subgroup and the checked p-group fixed-point congruence. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGPGroupNormalCenterIntersection
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_nontrivial_normal_center (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (hN : N≠⊥) :
    ∃z : G,z∈N ∧ z∈Subgroup.center G ∧ z≠1 := by
  letI : Nontrivial N := (N.nontrivial_iff_ne_bot).mpr hN
  have hpN : p∣Nat.card N := by
    obtain ⟨n,hn,he⟩ := (hG.to_subgroup N).nontrivial_iff_card.mp inferInstance
    exact he.symm ▸ dvd_pow_self p (ne_of_gt hn)
  have hone : (1 : N)∈MulAction.fixedPoints (ConjAct G) N := by
    apply MulAction.mem_fixedPoints.mpr
    intro g
    exact smul_one g
  obtain ⟨z,hz,hne⟩ := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point
    N hpN hone
  refine ⟨z.val,z.property,?_,?_⟩
  · apply Subgroup.mem_center_iff.mpr
    intro g
    have he := congrArg (fun n : N=>n.val) ((MulAction.mem_fixedPoints.mp hz) (ConjAct.toConjAct g))
    change g*z.val*g⁻¹=z.val at he
    calc
      g*z.val=(g*z.val*g⁻¹)*g := by group
      _=z.val*g := congrArg (fun x : G=>x*g) he
  · intro he
    apply hne
    apply Subtype.ext
    exact he.symm

theorem normal_eq_bot_of_center_intersection (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal]
    (hcap : ∀z : G,z∈N→z∈Subgroup.center G→z=1) : N=⊥ := by
  by_contra hn
  obtain ⟨z,hz,hzc,hzne⟩ := exists_nontrivial_normal_center hG N hn
  exact hzne (hcap z hz hzc)

end SymmetricSubgroupAsymptotics.CFSGPGroupNormalCenterIntersection

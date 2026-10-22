import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Logic.Function.Basic

/-! Finite collection by successive actual subgroup remainders. This
elementary induction does not require the layers or factors to commute. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteLayerCollection
variable {G : Type*} [Group G] (N : ℕ→Subgroup G) (C : ℕ→Type*)
    [∀n,Nonempty (C n)] (w : ∀n,C n→G)

theorem collect_with_remainder
    (hstep : ∀n,∀x∈N n,∃c : C n,∃y∈N (n+1),x=w n c*y)
    (x : G) (hx : x∈N 0) (m : ℕ) :
    ∃c : ∀n,C n,∃y∈N m,x=((List.range m).map (fun n=>w n (c n))).prod*y := by
  classical
  induction m with
  | zero =>
    exact ⟨(fun n=>Classical.choice (inferInstance : Nonempty (C n))),x,hx,by simp⟩
  | succ m ih =>
    obtain ⟨c,y,hy,he⟩ := ih
    obtain ⟨d,z,hz,hyz⟩ := hstep m y hy
    let c' : ∀n,C n := Function.update c m d
    have hprod : ((List.range m).map (fun n=>w n (c' n))).prod=
        ((List.range m).map (fun n=>w n (c n))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro n hn
      have hne : n≠m := Nat.ne_of_lt (List.mem_range.mp hn)
      rw [show c' n=c n from Function.update_of_ne hne d c]
    refine ⟨c',z,hz,?_⟩
    rw [List.range_succ,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,hprod]
    have hc : c' m=d := Function.update_self m d c
    rw [hc,he,hyz,mul_assoc]

theorem collect_when_final_bot
    (hstep : ∀n,∀x∈N n,∃c : C n,∃y∈N (n+1),x=w n c*y)
    (x : G) (hx : x∈N 0) (m : ℕ) (hm : N m=⊥) :
    ∃c : ∀n,C n,x=((List.range m).map (fun n=>w n (c n))).prod := by
  obtain ⟨c,y,hy,he⟩ := collect_with_remainder N C w hstep x hx m
  rw [hm,Subgroup.mem_bot] at hy
  exact ⟨c,by simpa only [hy,mul_one] using he⟩

end SymmetricSubgroupAsymptotics.CFSGFiniteLayerCollection

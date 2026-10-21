import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import SymmetricSubgroupAsymptotics.PerfectSubdirect

/-! A normal subgroup of a finite product of centerless simple groups is
perfect. Zero coordinate images are discarded and all remaining original
coordinates are onto simple factors; the checked subdirect-perfect theorem
retains every correlation and proves the result. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

/-- Normal coordinate images in simple groups are either zero or onto.
The latter coordinates still separate the actual source elements. -/
theorem perfect_of_normal_simple_coordinate_ranges
    {I : Type} [Fintype I] (S : I→Type) [∀ i,Group (S i)] [∀ i,IsSimpleGroup (S i)]
    (hnc : ∀ i,¬IsMulCommutative (S i))
    (G : Type) [Group G] (f : ∀ i,G→*S i)
    (hn : ∀ i,(f i).range.Normal)
    (hi : Function.Injective (fun g i => f i g)) : Group.IsPerfect G := by
  let J := {i : I // (f i).range=⊤}
  apply nonabelian_simple_subdirect_perfect (fun j : J => S j.val)
    (fun j => hnc j.val) G (fun j => f j.val)
    (fun j => MonoidHom.range_eq_top.mp j.property)
  intro a b hab
  apply hi
  funext i
  by_cases htop : (f i).range=⊤
  · exact congrFun hab (⟨i,htop⟩ : J)
  · have hbot : (f i).range=⊥ :=
      ((hn i).eq_bot_or_eq_top).resolve_right htop
    have ha : f i a=1 := by
      have hx : f i a∈(f i).range := ⟨a,rfl⟩
      rw [hbot] at hx
      exact Subgroup.mem_bot.mp hx
    have hb : f i b=1 := by
      have hx : f i b∈(f i).range := ⟨b,rfl⟩
      rw [hbot] at hx
      exact Subgroup.mem_bot.mp hx
    exact ha.trans hb.symm

namespace SemisimpleNormalChart
variable {G : Type} [Group G] {E : Subgroup G} (C : SemisimpleNormalChart E)
include C

/-- The intersection with a normal subgroup of the original ambient group
is perfect as its actual subgroup carrier. -/
theorem normal_subgroup_perfect (N : Subgroup E) [N.Normal] : Group.IsPerfect N := by
  letI (i : C.ι) : IsSimpleGroup (C.factor i) := C.simple i
  let m (i : C.ι) : E→*C.factor i :=
    (Pi.evalMonoidHom C.factor i).comp C.equiv.toMonoidHom
  let f (i : C.ι) : N→*C.factor i := (m i).comp N.subtype
  have hnc (i : C.ι) : ¬IsMulCommutative (C.factor i) := by
    intro hc
    obtain ⟨x,hx⟩ := exists_ne (1 : C.factor i)
    exact hx (C.centerless i x (fun y => (isMulCommutative_iff.mp hc) x y))
  have hm (i : C.ι) : Function.Surjective (m i) := by
    intro x
    refine ⟨C.equiv.symm (Pi.mulSingle i x),?_⟩
    change C.equiv (C.equiv.symm (Pi.mulSingle i x)) i=x
    rw [C.equiv.apply_symm_apply,Pi.mulSingle_eq_same]
  have hn (i : C.ι) : (f i).range.Normal := by
    have hr : (f i).range=N.map (m i) := by
      rw [MonoidHom.range_comp,Subgroup.range_subtype]
    rw [hr]
    exact Subgroup.Normal.map inferInstance (m i) (hm i)
  apply perfect_of_normal_simple_coordinate_ranges C.factor hnc N f hn
  intro a b hab
  apply Subtype.ext
  apply C.equiv.injective
  funext i
  exact congrFun hab i

theorem normal_intersection_perfect (N : Subgroup G) [N.Normal] :
    Group.IsPerfect (N.subgroupOf E) := C.normal_subgroup_perfect (N.subgroupOf E)

end SemisimpleNormalChart
end SymmetricSubgroupAsymptotics

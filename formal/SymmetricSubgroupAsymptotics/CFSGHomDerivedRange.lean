import Mathlib.GroupTheory.Commutator.Basic

/-! The image of a literal derived subgroup contains image commutators
and is stable under conjugation by elements of the original image. -/
set_option autoImplicit false
set_option Elab.async false
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGHomDerivedRange
variable {G H : Type*} [Group G] [Group H] (f : G→*H)

def derivedMap : commutator G→*H := f.comp (commutator G).subtype

theorem commutator_mem (x y : G) : ⁅f x,f y⁆∈(derivedMap f).range := by
  refine ⟨⟨⁅x,y⁆,?_⟩,map_commutatorElement f x y⟩
  rw [commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)

theorem conjugate_mem (g : G) (y : H) (hy : y∈(derivedMap f).range) :
    f g*y*(f g)⁻¹∈(derivedMap f).range := by
  obtain ⟨d,hd⟩ := hy
  refine ⟨⟨g*d.val*g⁻¹,
    (inferInstance : (commutator G).Normal).conj_mem d.val d.property g⟩,?_⟩
  change f (g*d.val*g⁻¹)=_
  have he : f d.val=y := hd
  rw [map_mul,map_mul,map_inv,he]

end SymmetricSubgroupAsymptotics.CFSGHomDerivedRange

import Mathlib.Algebra.Group.Subgroup.Ker

/-! Literal original subgroup AND character recovery from one global graph.
This applies before any RDT quotient selection; it does not require the
original subgroup to be full in its ambient physical product. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.SubgroupCharacterGraph

variable {A M : Type} [Group A] [Group M]

def hom (H : Subgroup A) (f : H →* M) : H →* (A × M) where
  toFun h := (h.val,f h)
  map_one' := by simp
  map_mul' _ _ := by simp

def graph (H : Subgroup A) (f : H →* M) : Subgroup (A × M) := (hom H f).range

theorem recover_subgroup (H : Subgroup A) (f : H →* M) :
    (graph H f).map (MonoidHom.fst A M)=H := by
  apply le_antisymm
  · rintro a ⟨z,⟨h,rfl⟩,rfl⟩
    exact h.property
  · intro a ha
    exact ⟨hom H f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,rfl⟩

def code : (Σ H : Subgroup A,H →* M) → Subgroup (A × M) := fun z => graph z.1 z.2

theorem code_injective : Function.Injective (@code A M _ _) := by
  rintro ⟨H,f⟩ ⟨K,g⟩ he
  have hHK : H=K := by
    have hh := congrArg (fun J : Subgroup (A × M) => J.map (MonoidHom.fst A M)) he
    exact (recover_subgroup H f).symm.trans (hh.trans (recover_subgroup K g))
  cases hHK
  change graph H f=graph H g at he
  have hfg : f=g := by
    apply MonoidHom.ext
    intro x
    have hx : hom H f x ∈ graph H g := by
      rw [← he]
      exact ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hx
    have hyx : y=x := Subtype.ext (congrArg Prod.fst hy)
    have hm := congrArg Prod.snd hy
    change g y=f x at hm
    rw [hyx] at hm
    exact hm.symm
  cases hfg
  rfl

end SymmetricSubgroupAsymptotics.MarkedC4.SubgroupCharacterGraph

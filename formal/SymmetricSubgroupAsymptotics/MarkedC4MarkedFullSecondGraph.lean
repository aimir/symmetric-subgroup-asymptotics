import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification
import Mathlib.Data.SetLike.Fintype

/-! A genuine marked Goursat/Hall injection.
A full-second subgroup together with its actual character has a literal
graph inside (A × C) × E. Both subgroup and character are recovered from
that graph, so the injection is constructed rather than an encoding premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.MarkedFullSecondGraph
open AbelianProductGraphClassification

variable {A E C : Type} [Group A] [Group E] [Group C]

def drop : ((A × C) × E) →* (A × E) where
  toFun z := (z.1.1,z.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def graphHom (H : FullSecond A E) (f : H.val →* C) : H.val →* ((A × C) × E) where
  toFun h := ((h.val.1,f h),h.val.2)
  map_one' := by simp
  map_mul' _ _ := by simp

def graph (H : FullSecond A E) (f : H.val →* C) : FullSecond (A × C) E := by
  refine ⟨(graphHom H f).range,top_unique ?_⟩
  intro e _
  have he : e ∈ H.val.map (MonoidHom.snd A E) := by rw [H.property]; trivial
  obtain ⟨x,hx,hxe⟩ := he
  exact ⟨graphHom H f ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,hxe⟩

theorem recover_subgroup (H : FullSecond A E) (f : H.val →* C) :
    (graph H f).val.map drop = H.val := by
  apply le_antisymm
  · rintro z ⟨w,⟨h,rfl⟩,rfl⟩
    exact h.property
  · intro z hz
    exact ⟨graphHom H f ⟨z,hz⟩,⟨⟨z,hz⟩,rfl⟩,rfl⟩

def code : (Σ H : FullSecond A E,H.val →* C) → FullSecond (A × C) E :=
  fun z => graph z.1 z.2

/-- The graph remembers the ORIGINAL subgroup and the complete character. -/
theorem code_injective : Function.Injective (@code A E C _ _ _) := by
  rintro ⟨H,f⟩ ⟨K,g⟩ he
  have hHK : H=K := by
    apply Subtype.ext
    have hh := congrArg (fun J : FullSecond (A × C) E => J.val.map drop) he
    exact (recover_subgroup H f).symm.trans (hh.trans (recover_subgroup K g))
  cases hHK
  change graph H f=graph H g at he
  have hfg : f=g := by
    apply MonoidHom.ext
    intro x
    have hx : graphHom H f x ∈ (graph H g).val := by
      rw [← he]
      exact ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hx
    have hyx : y=x := by
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z : (A × C) × E => z.1.1) hy)
        (congrArg (fun z : (A × C) × E => z.2) hy)
    have hc := congrArg (fun z : (A × C) × E => z.1.2) hy
    change g y=f x at hc
    rw [hyx] at hc
    exact hc.symm
  cases hfg
  rfl

theorem card_le [Finite A] [Finite E] [Finite C] :
    Nat.card (Σ H : FullSecond A E,H.val →* C) ≤ Nat.card (FullSecond (A × C) E) :=
  Nat.card_le_card_of_injective code code_injective

end SymmetricSubgroupAsymptotics.MarkedC4.MarkedFullSecondGraph

import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification
import Mathlib.Data.SetLike.Fintype

/-! The actual subgroup fibre over its retained second projection.
Every original subgroup with that projection is injectively identified with
a literal full-second subgroup. This supplies the real Hall encoding step;
no encoding or enumeration callback is accepted as a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualProjectionHallFibre
open AbelianProductGraphClassification

variable {A B : Type} [Group A] [Group B] (E : Subgroup B)
abbrev Fiber := {H : Subgroup (A × B) // H.map (MonoidHom.snd A B)=E}

def inclusion : (A × E) →* (A × B) := (MonoidHom.id A).prodMap E.subtype

/-- The retained source is the SAME actual second image, not an unrelated
maximal-cardinality group or a chosen abstract representative. -/
def code (H : Fiber (A := A) E) : FullSecond A E := by
  refine ⟨H.val.comap (inclusion E),top_unique ?_⟩
  intro e _
  have he : e.val ∈ H.val.map (MonoidHom.snd A B) := by
    rw [H.property]
    exact e.property
  obtain ⟨x,hx,hxe⟩ := he
  have hm : inclusion E (x.1,e)=x := Prod.ext rfl hxe.symm
  exact ⟨(x.1,e),hm.symm ▸ hx,rfl⟩

theorem recover (H : Fiber (A := A) E) :
    (code E H).val.map (inclusion E)=H.val := by
  apply le_antisymm
  · rintro z ⟨x,hx,rfl⟩
    exact hx
  · intro z hz
    have he : z.2 ∈ E := by
      rw [← H.property]
      exact ⟨z,hz,rfl⟩
    exact ⟨(z.1,⟨z.2,he⟩),hz,rfl⟩

theorem code_injective : Function.Injective (@code A B _ _ E) := by
  intro H K he
  apply Subtype.ext
  have hh := congrArg (fun J : FullSecond A E => J.val.map (inclusion E)) he
  exact (recover E H).symm.trans (hh.trans (recover E K))

/-- Exact fibre cardinality comparison, ready for the actual abelian Hall
bound with A replaced by selected physical abelian factors × C4^r. -/
theorem card_le [Finite A] [Finite B] :
    Nat.card (Fiber (A := A) E) ≤ Nat.card (FullSecond A E) :=
  Nat.card_le_card_of_injective (code E) (code_injective E)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualProjectionHallFibre

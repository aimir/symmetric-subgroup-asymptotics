import SymmetricSubgroupAsymptotics.BlockComponentSurjectiveSource
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! A second actual minimal block choice in the faithful original top
is pulled back to the original group. The intermediate components are
identified by lifting stabilizer elements through the actual top map,
so their primitivity comes from the second cover, not an assumption
about simultaneous minimal and maximal block choices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (E : OriginalMinimalBlock (A := D.Top) D.base)

abbrev action : MulAction A E.Points := MulAction.compHom _ D.topMap.rangeRestrict

def map : D.Points → E.Points := by
  letI := D.top_pretransitive
  exact E.map

theorem map_surjective : Function.Surjective (map D E) := by
  letI := D.top_pretransitive
  exact E.map_surjective

theorem map_equivariant :
    letI := action D E
    ∀ (g : A) (x : D.Points), map D E (g • x) = g • map D E x := by
  letI := D.top_pretransitive
  letI := action D E
  intro g x
  exact E.map_equivariant (D.topMap.rangeRestrict g) x

theorem component_eq (y : E.Points) :
    letI := D.top_pretransitive
    letI := action D E
    originalBlockComponent (A := A) (map D E) (map_equivariant D E) y =
      originalBlockComponent (A := D.Top) E.map E.map_equivariant y := by
  letI := D.top_pretransitive
  letI := action D E
  have hG : ∀ (g : A) (x : D.Points), map D E (g • x) = g • map D E x :=
    map_equivariant D E
  have hH : ∀ (g : D.Top) (x : D.Points), map D E (g • x) = g • map D E x :=
    E.map_equivariant
  exact BlockComponentSurjectiveSource.component_eq D.topMap.rangeRestrict
    D.topMap.rangeRestrict_surjective (fun _ _ => rfl) (fun _ _ => rfl) (map D E) hG hH y

theorem fibre_card_at (y : E.Points) :
    letI := D.top_pretransitive
    Nat.card (originalBlockFibre (map D E) y) = Nat.card E.Fibre := by
  letI := D.top_pretransitive
  exact E.fibre_card_at y

theorem component_preprimitive_at (y : E.Points) :
    letI := action D E
    MulAction.IsPreprimitive
      (originalBlockComponent (A := A) (map D E) (map_equivariant D E) y)
      (originalBlockFibre (map D E) y) := by
  letI := D.top_pretransitive
  letI := action D E
  rw [component_eq D E y]
  exact E.component_preprimitive_at y

end SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement

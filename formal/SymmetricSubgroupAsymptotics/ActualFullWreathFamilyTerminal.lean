import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import Mathlib.SetTheory.Cardinal.Finite

/-! The terminal local-chief quotient has exactly one full-component
subgroup over the original top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathFamilyTerminal
open PermutationalWreathProduct ActualFullWreathFamily

variable {R Q I : Type} [Group R] [Group Q] [MulAction Q I]

def whole : Family R Q I := by
  refine ⟨⊤,?_,?_⟩
  · apply top_unique
    intro q _
    exact ⟨⟨1,q⟩,Subgroup.mem_top _,rfl⟩
  · intro i r
    refine ⟨⟨⟨fun _ => r,1⟩,Subgroup.mem_top _⟩,?_,rfl⟩
    exact one_smul Q i

theorem subgroup_eq_top [Subsingleton R] (L : Family R Q I) : L.val=⊤ := by
  apply top_unique
  intro w _
  obtain ⟨g,hg⟩ := ActualFullWreathFamily.top_surjective L w.right
  have he : g.val=w := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact Subsingleton.elim _ _
    · exact hg
  rw [←he]
  exact g.property

theorem card_eq_one [Subsingleton R] : Nat.card (Family R Q I)=1 := by
  letI : Subsingleton (Family R Q I) := ⟨by
    intro L M
    apply Subtype.ext
    exact (subgroup_eq_top L).trans (subgroup_eq_top M).symm⟩
  exact Nat.card_of_subsingleton (whole (R := R) (Q := Q) (I := I))

end SymmetricSubgroupAsymptotics.ActualFullWreathFamilyTerminal

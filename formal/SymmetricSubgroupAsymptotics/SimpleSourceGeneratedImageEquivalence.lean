import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A classifier supplies simplicity of the ACTUAL source, not of a
historical model. Genuine seed-image containment and recovery then identify
its matrix image without any group order or target simplicity theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimpleSourceGeneratedImageEquivalence

variable {P N : Type*} [Group P] [Group N] [IsSimpleGroup P]

theorem injective_of_surjective (H : Subgroup N) [Nontrivial H]
    (f : P →* H) (hf : Function.Surjective f) : Function.Injective f := by
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact f.ker_eq_bot_iff.mp hk
  · have hone : f = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨y,hy⟩ := exists_ne (1 : H)
    obtain ⟨x,rfl⟩ := hf y
    exact (hy (by rw [hone]; rfl)).elim

def equiv_of_surjective (H : Subgroup N) [Nontrivial H]
    (f : P →* H) (hf : Function.Surjective f) : P ≃* H :=
  MulEquiv.ofBijective f ⟨injective_of_surjective H f hf,hf⟩

theorem range_le_of_generator_images (f : P →* N) (S : Set P)
    (hS : Subgroup.closure S = ⊤) (H : Subgroup N)
    (himages : ∀ x ∈ S, f x ∈ H) : f.range ≤ H := by
  have hle : Subgroup.closure S ≤ H.comap f :=
    (Subgroup.closure_le _).mpr himages
  intro y hy
  obtain ⟨x,rfl⟩ := hy
  have hx : x ∈ Subgroup.closure S := by rw [hS]; trivial
  exact hle hx

/-- Both containment directions are genuine word-level obligations.
In particular, H≤range alone does not imply this equivalence. -/
def equiv_of_generator_images_and_recovery (f : P →* N) (S : Set P)
    (hS : Subgroup.closure S = ⊤) (H : Subgroup N) [Nontrivial H]
    (himages : ∀ x ∈ S, f x ∈ H) (hrecovery : H ≤ f.range) : P ≃* H := by
  have hle := range_le_of_generator_images f S hS H himages
  let g : P →* H := f.codRestrict H (fun x => hle ⟨x,rfl⟩)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := hrecovery y.property
    exact ⟨x,Subtype.ext hx⟩
  exact equiv_of_surjective H g hg

end SymmetricSubgroupAsymptotics.SimpleSourceGeneratedImageEquivalence

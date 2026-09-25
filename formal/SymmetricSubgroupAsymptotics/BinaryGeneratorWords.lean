import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Map

/-! Literal generator-word certificates, independent of finite row tables. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G ι κ : Type*} [Group G]

/-- Positive words suffice in finite groups; every checked word is an
actual product in the original source, even for nonsplit extensions. -/
structure BinaryNormalGeneratorWords (source : ι → G) (target : κ → G) where
  words : ι → List κ
  equations : ∀ i, ((words i).map target).prod=source i

namespace BinaryNormalGeneratorWords
variable {source : ι → G} {target : κ → G}
    (W : BinaryNormalGeneratorWords source target)

include W

theorem closure_le : Subgroup.closure (Set.range source) ≤
    Subgroup.closure (Set.range target) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  rw [← W.equations i]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  exact Subgroup.subset_closure ⟨j,rfl⟩

end BinaryNormalGeneratorWords

/-- A source generator tuple is full when its faithful original image is
exactly the original generating tuple. -/
theorem binaryNormal_full_generators_of_equiv {H : Type*} [Group H]
    (original : ι → H) (rows : ι → G)
    (e : G ≃* Subgroup.closure (Set.range original))
    (he : ∀ j, (e (rows j) : H)=original j) :
    Subgroup.closure (Set.range rows)=⊤ := by
  let f : G →* H := (Subgroup.closure (Set.range original)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  apply Subgroup.map_injective hf
  rw [MonoidHom.map_closure]
  have him : f '' Set.range rows=Set.range original := by
    ext x
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and]
    simpa only [show ∀ j, f (rows j)=original j from he]
  rw [him]
  change _=Subgroup.map ((Subgroup.closure (Set.range original)).subtype.comp e.toMonoidHom) ⊤
  rw [← Subgroup.map_map,Subgroup.map_top_of_surjective _ e.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics

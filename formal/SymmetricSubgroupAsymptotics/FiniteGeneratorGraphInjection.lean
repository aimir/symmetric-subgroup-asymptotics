import SymmetricSubgroupAsymptotics.FiniteGeneratorGraphCertificate
import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates

/-! Transport a selected quotient-word graph to the exact original group.
The generation premise concerns the original kernel, not a replacement
component group. No ordinary conjugacy of the two actions is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace FiniteGeneratorGraphCertificate

variable {G H K I J : Type} [Group G] [Group H] [Group K]
  {source : J → G} {target : J → H}
  (C : FiniteGeneratorGraphCertificate (I := I) source target)

include C

/-- A graph certificate forces equality in a faithfully paired original
group as soon as its first coordinates agree. -/
theorem first_comp_injective (f : K →* G × H)
    (hf : Function.Injective f) (hmem : ∀ k, f k ∈ C.graph) :
    Function.Injective ((MonoidHom.fst G H).comp f) := by
  intro x y hxy
  apply hf
  have he : C.first ⟨f x, hmem x⟩ = C.first ⟨f y, hmem y⟩ := by
    apply Subtype.ext
    exact hxy
  exact congrArg Subtype.val (C.first_bijective.1 he)

/-- Exact generators suffice to place every original element in the graph.
This is suitable for the index-two Schreier generators of a block kernel. -/
theorem image_mem_graph_of_generated (f : K →* G × H) (g : J → K)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hfg : ∀ j, f (g j) = (source j, target j)) :
    ∀ k, f k ∈ C.graph := by
  have hle : Subgroup.closure (Set.range g) ≤ C.graph.comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change f (g j) ∈ C.graph
    rw [hfg]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  rw [hg] at hle
  intro k
  exact hle (Subgroup.mem_top k)

theorem first_comp_injective_of_generated (f : K →* G × H)
    (hf : Function.Injective f) (g : J → K)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hfg : ∀ j, f (g j) = (source j, target j)) :
    Function.Injective ((MonoidHom.fst G H).comp f) :=
  C.first_comp_injective f hf (C.image_mem_graph_of_generated f g hg hfg)

end FiniteGeneratorGraphCertificate

namespace ProductBlockFrame

/-- The selected graph certifies first-fibre faithfulness on the literal
kernel of the original physical block action. -/
theorem kernelCoordinate_zero_injective_of_graph
    {X F I J : Type} {U : Subgroup (Equiv.Perm X)}
    (B : ProductBlockFrame U (Fin 2) F)
    (g : J → B.top.ker)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (C : FiniteGeneratorGraphCertificate (I := I)
      (fun j => B.kernelCoordinate 0 (g j))
      (fun j => B.kernelCoordinate 1 (g j))) :
    Function.Injective (B.kernelCoordinate 0) := by
  exact C.first_comp_injective_of_generated B.twoKernelMap
    B.twoKernelMap_injective g hg (fun _ => rfl)

end ProductBlockFrame
end SymmetricSubgroupAsymptotics

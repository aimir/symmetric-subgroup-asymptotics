import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricThreeGeometry
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators

/-!
# S₃ geometry from a literal twelve-to-six-to-three binary pair tower

Two actual binary pair kernels make the composite kernel binary. Generator
point checks construct both frames; six short words in two retained
generators prove that the last image is S₃. No source-group enumeration
or top-cardinality certificate is required.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveBinaryTowerGeometry

open DegreeTwoTwelveSymmetricThreeGeometry

structure Tower (T : Subgroup (Equiv.Perm (Fin 12))) : Type where
  first : BinaryPairFrame T (Fin 6)
  second : BinaryPairFrame first.top.range (Fin 3)

namespace Tower

variable {T : Subgroup (Equiv.Perm (Fin 12))} (F : Tower T)

def beta : T →* Equiv.Perm (Fin 3) := F.second.top.comp F.first.top.rangeRestrict

theorem kernel_binary : IsPGroup 2 F.beta.ker := by
  have hfirst : IsPGroup 2 F.first.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact F.first.kernel_isPGroup
  exact F.second.kernel_isPGroup.comap_of_ker_isPGroup F.first.top.rangeRestrict hfirst

def project (x : Fin 12) : Fin 3 :=
  (F.second.frame.symm (F.first.frame.symm x).1).1

theorem equivariant (g : T) (x : Fin 12) :
    F.project (g • x) = F.beta g • F.project x := by
  obtain ⟨v, rfl⟩ := F.first.frame.surjective x
  have hsecond := F.second.intertwine (F.first.top.rangeRestrict g)
    (F.second.frame.symm v.1)
  change (F.second.frame.symm
    (F.first.frame.symm ((g : Equiv.Perm (Fin 12)) (F.first.frame v))).1).1 = _
  rw [F.first.intertwine]
  simpa only [project, beta, MonoidHom.comp_apply, F.first.frame.symm_apply_apply,
    F.second.frame.apply_symm_apply, MonoidHom.coe_rangeRestrict] using hsecond

def toTopGeometry {D : DegreeTwoPairTopFiniteInterface 12}
    (F : Tower D.top) (honto : Function.Surjective F.beta) : TopGeometry D where
  beta := F.beta
  onto := honto
  kernel_binary := F.kernel_binary
  project := F.project
  equivariant := F.equivariant

end Tower

section Generators

variable {ι : Type}
  (frame1 : Fin 6 × ZMod 2 ≃ Fin 12)
  (frame2 : Fin 3 × ZMod 2 ≃ Fin 6)
  (generators : ι → Equiv.Perm (Fin 12))
  (tops6 : ι → Equiv.Perm (Fin 6)) (tops3 : ι → Equiv.Perm (Fin 3))
  (h1 : ∀ i, BinaryPairFrame.Preserves frame1 (generators i) (tops6 i))
  (h2 : ∀ i, BinaryPairFrame.Preserves frame2 (tops6 i) (tops3 i))

def firstFrame : BinaryPairFrame (Subgroup.closure (Set.range generators)) (Fin 6) :=
  BinaryPairFrame.ofGenerators frame1 generators tops6 h1

def middleEquiv : Subgroup.closure (Set.range tops6) ≃*
    (firstFrame frame1 generators tops6 h1).top.range :=
  MulEquiv.subgroupCongr
    (BinaryPairFrame.ofGenerators_top_range frame1 generators tops6 h1).symm

def secondFrame : BinaryPairFrame (firstFrame frame1 generators tops6 h1).top.range (Fin 3) :=
  BinaryPairFrame.ofEquiv (middleEquiv frame1 generators tops6 h1)
    (BinaryPairFrame.ofGenerators frame2 tops6 tops3 h2).top frame2 (by
      intro u v
      change (frame2.symm ((u : Equiv.Perm (Fin 6)) (frame2 v))).1 = _
      exact (BinaryPairFrame.ofGenerators frame2 tops6 tops3 h2).intertwine u v)

def ofGenerators : Tower (Subgroup.closure (Set.range generators)) where
  first := firstFrame frame1 generators tops6 h1
  second := secondFrame frame1 frame2 generators tops6 tops3 h1 h2

theorem ofGenerators_beta_generator (i : ι) :
    (ofGenerators frame1 frame2 generators tops6 tops3 h1 h2).beta
      ⟨generators i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = tops3 i := by
  let u : Subgroup.closure (Set.range generators) :=
    ⟨generators i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hm : (middleEquiv frame1 generators tops6 h1).symm
      ((firstFrame frame1 generators tops6 h1).top.rangeRestrict u) =
      (⟨tops6 i, Subgroup.subset_closure ⟨i, rfl⟩⟩ :
        Subgroup.closure (Set.range tops6)) := by
    apply Subtype.ext
    change (firstFrame frame1 generators tops6 h1).top u = tops6 i
    exact BinaryPairFrame.ofGenerators_top_generator frame1 generators tops6 h1 i
  change (BinaryPairFrame.ofGenerators frame2 tops6 tops3 h2).top
    ((middleEquiv frame1 generators tops6 h1).symm
      ((firstFrame frame1 generators tops6 h1).top.rangeRestrict u)) = tops3 i
  rw [hm]
  exact BinaryPairFrame.ofGenerators_top_generator frame2 tops6 tops3 h2 i

/-- Only the six permutations of three labels are covered. Their
witnesses lift to literal words in the original generator subgroup. -/
theorem ofGenerators_beta_onto (cycle swap : ι)
    (hcover : ∀ s : Equiv.Perm (Fin 3), ∃ a : Fin 3, ∃ b : Fin 2,
      tops3 cycle ^ a.val * tops3 swap ^ b.val = s) :
    Function.Surjective (ofGenerators frame1 frame2 generators tops6 tops3 h1 h2).beta := by
  intro s
  obtain ⟨a, b, hab⟩ := hcover s
  let c : Subgroup.closure (Set.range generators) :=
    ⟨generators cycle, Subgroup.subset_closure ⟨cycle, rfl⟩⟩
  let t : Subgroup.closure (Set.range generators) :=
    ⟨generators swap, Subgroup.subset_closure ⟨swap, rfl⟩⟩
  refine ⟨c ^ a.val * t ^ b.val, ?_⟩
  rw [map_mul, map_pow, map_pow]
  change (ofGenerators frame1 frame2 generators tops6 tops3 h1 h2).beta c ^ a.val *
    (ofGenerators frame1 frame2 generators tops6 tops3 h1 h2).beta t ^ b.val = s
  simpa only [c, t, ofGenerators_beta_generator] using hab

end Generators
end DegreeTwoTwelveBinaryTowerGeometry
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

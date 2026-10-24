import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity

/-!
# An independent ordinary-generation step for an actual elementary layer

The normal subgroup, its original conjugation action, and the actual
inducing subgroup are retained. The capacity used below is the least
actual capacity already constructed from Sylow/Mackey module generators;
it is not a published Tracey input. The elementary kernel is proved
abelian before its ambient normal generators are charged to ordinary
generation. No extension splitting or minimal-normal hypothesis is used.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementaryInducedOrdinaryGeneratorStep

variable {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)

include C in
theorem kernel_isMulCommutative : IsMulCommutative E where
  is_comm.comm x y := by
    apply C.equiv.injective
    simp only [map_mul]
    exact mul_comm _ _

/-- Only the genuinely abelian kernel permits this ordinary-generation
use of ambient normal generators. -/
theorem genRank_le_of_uniform (n : ℕ)
    (hu : UniformSubrepresentationGeneratorBound C.quotientRepresentation.ρ n) :
    MarkedC4.genRank G ≤ MarkedC4.genRank (G ⧸ E) + n := by
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  have hker : q.ker = E := QuotientGroup.ker_mk' E
  letI : IsMulCommutative E := kernel_isMulCommutative E C
  letI : IsMulCommutative q.ker := by rw [hker]; infer_instance
  have hn : MarkedC4.normalGen q.ker ≤ n := by
    rw [hker]
    exact ElementaryUniformNormalGenerators.kernel_normalGen_le E C n hu E le_rfl
  exact (AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    q (QuotientGroup.mk'_surjective E)).trans (Nat.add_le_add_left hn _)

variable {V : Type} [AddCommGroup V] [Module (ZMod C.p) V]
    [FiniteDimensional (ZMod C.p) V]
    (H : Subgroup G) (rho : Representation (ZMod C.p) H V)

/-- An actual injective intertwiner, retaining inflated ORIGINAL
conjugation, pays the layer by a proved induced-module capacity. -/
theorem genRank_le_induced_capacity
    (iota : Representation.IntertwiningMap
      (C.quotientRepresentation.ρ.comp (QuotientGroup.mk' E))
      (Representation.ind H.subtype rho)) (hiota : Function.Injective iota) :
    MarkedC4.genRank G ≤ MarkedC4.genRank (G ⧸ E) +
      InducedMinimumUniformCapacity.capacity H rho := by
  apply genRank_le_of_uniform E C
  apply UniformSubrepresentationGeneratorBound.of_comp
    C.quotientRepresentation.ρ (QuotientGroup.mk' E)
  exact (InducedMinimumUniformCapacity.uniform H rho).of_injective iota hiota

/-- A literal finite generating set in the SAME original group, without
assuming that the elementary extension splits. -/
theorem exists_generating_finset
    (iota : Representation.IntertwiningMap
      (C.quotientRepresentation.ρ.comp (QuotientGroup.mk' E))
      (Representation.ind H.subtype rho)) (hiota : Function.Injective iota) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ MarkedC4.genRank (G ⧸ E) + InducedMinimumUniformCapacity.capacity H rho := by
  obtain ⟨S, hcard, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S, hgen, hcard.le.trans (genRank_le_induced_capacity E C H rho iota hiota)⟩

end SymmetricSubgroupAsymptotics.ElementaryInducedOrdinaryGeneratorStep

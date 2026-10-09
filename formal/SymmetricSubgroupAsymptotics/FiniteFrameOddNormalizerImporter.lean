import SymmetricSubgroupAsymptotics.FiniteFrameRegistryTransport
import SymmetricSubgroupAsymptotics.OddNormalizerSubrepresentationHead

/-!
# Importing a finite odd-normalizer frame row

A checked sixteen-block row consists of a complete normal-axis registry for
its literal top and one odd subgroup together with a normalizing element.
The odd-normalizer theorem bounds every subrepresentation of the checked
ambient frame.  This file transports that bound through an exact top match
and an injective equivariant embedding of the actual translation module.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open FiniteFrameRepresentationTransport

namespace FiniteFrameOddNormalizerRow

variable {G H V W : Type} [Group G] [Finite G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {sigma : Representation (ZMod 2) G W}
  {rho : Representation (ZMod 2) H V}
  {slots : ℕ}

/-- The retained fixed-space equation identifies the abstract simultaneous
fixed space used by the reusable theorem with the subspace checked in the
finite row. -/
theorem oddNormalizerFixedSpace_eq
    (C : FiniteFrameOddNormalizerRow sigma slots) :
    oddNormalizerFixedSpace sigma C.fixedWitness.A C.fixedWitness.g =
      C.fixedWitness.fixed := by
  ext v
  rw [C.fixedWitness.mem_fixed_iff]
  constructor
  · intro hv
    exact ⟨(Representation.mem_invariants
        (ρ := sigma.comp C.fixedWitness.A.subtype) v).mp hv.1,
      (mem_representationElementFixedSpace sigma C.fixedWitness.g v).mp hv.2⟩
  · rintro ⟨hA, hg⟩
    exact ⟨(Representation.mem_invariants
        (ρ := sigma.comp C.fixedWitness.A.subtype) v).mpr hA,
      (mem_representationElementFixedSpace sigma C.fixedWitness.g v).mpr hg⟩

/-- Every actual invariant submodule has coinvariant head at most the
fixed-space entry in the matched finite row. -/
theorem module_bound_embedding
    [Finite V] [Finite W]
    (C : FiniteFrameOddNormalizerRow sigma slots)
    (groupEquiv : H ≃* G)
    (moduleEmbedding :
      rho.IntertwiningMap (sigma.comp groupEquiv.toMonoidHom))
    (moduleEmbedding_injective : Function.Injective moduleEmbedding)
    (B : Subrepresentation rho) :
    Module.finrank (ZMod 2) B.toRepresentation.Coinvariants ≤
      C.fixedWitness.dimension := by
  let inclusion : B.toRepresentation.IntertwiningMap rho := {
    toLinearMap := B.toSubmodule.subtype
    isIntertwining' := by intro g; rfl }
  let restricted := moduleEmbedding.comp inclusion
  have hrestricted : Function.Injective restricted :=
    moduleEmbedding_injective.comp Subtype.val_injective
  have hrange : Function.Injective
      (RepresentationHeadExact.rangeProjection restricted) := by
    intro x y hxy
    exact hrestricted (congrArg Subtype.val hxy)
  let rangeEquiv : B.toRepresentation.Equiv
      restricted.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection restricted).ofBijective
      ⟨hrange,
        RepresentationHeadExact.rangeProjection_surjective restricted⟩
  let source := descendGroupEquiv sigma groupEquiv restricted.range
  calc
    Module.finrank (ZMod 2) B.toRepresentation.Coinvariants =
        Module.finrank (ZMod 2)
          restricted.range.toRepresentation.Coinvariants :=
      coinvariants_finrank_eq_of_representationEquiv rangeEquiv
    _ = Module.finrank (ZMod 2) source.toRepresentation.Coinvariants :=
      coinvariants_finrank_descendGroupEquiv sigma groupEquiv restricted.range
    _ ≤ Module.finrank (ZMod 2)
          (oddNormalizerFixedSpace sigma C.fixedWitness.A
            C.fixedWitness.g) :=
      binary_subrepresentation_coinvariants_le_oddNormalizerFixedSpace
        sigma C.fixedWitness.A C.fixedWitness.odd_order
          C.fixedWitness.g C.fixedWitness.g_normalizes source
    _ = Module.finrank (ZMod 2) C.fixedWitness.fixed := by
      rw [oddNormalizerFixedSpace_eq C]
    _ = C.fixedWitness.dimension := C.fixedWitness.dimension_eq

end FiniteFrameOddNormalizerRow

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

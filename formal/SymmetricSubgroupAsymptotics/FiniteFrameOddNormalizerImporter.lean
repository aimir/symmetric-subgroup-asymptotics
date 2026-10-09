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

namespace FiniteFrameOddNormalizerWitness

variable {k G H V W : Type} [Field k] [Group G] [Finite G] [Group H]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  {sigma : Representation k G W}
  {rho : Representation k H V}
  {slots : ℕ}

/-- The retained fixed-space equation identifies the abstract simultaneous
fixed space used by the reusable theorem with the subspace checked in the
finite row. -/
theorem oddNormalizerFixedSpace_eq
    (C : FiniteFrameOddNormalizerWitness sigma) :
    oddNormalizerFixedSpace sigma C.A C.g = C.fixed := by
  ext v
  rw [C.mem_fixed_iff]
  constructor
  · intro hv
    exact ⟨(Representation.mem_invariants
        (ρ := sigma.comp C.A.subtype) v).mp hv.1,
      (mem_representationElementFixedSpace sigma C.g v).mp hv.2⟩
  · rintro ⟨hA, hg⟩
    exact ⟨(Representation.mem_invariants
        (ρ := sigma.comp C.A.subtype) v).mpr hA,
      (mem_representationElementFixedSpace sigma C.g v).mpr hg⟩

/-- Every actual invariant submodule has coinvariant head at most the
fixed-space entry in the matched finite row. -/
theorem module_bound_embedding
    [FiniteDimensional k V] [FiniteDimensional k W]
    (C : FiniteFrameOddNormalizerWitness sigma)
    (hunit : IsUnit (Nat.card C.A : k))
    (groupEquiv : H ≃* G)
    (moduleEmbedding :
      rho.IntertwiningMap (sigma.comp groupEquiv.toMonoidHom))
    (moduleEmbedding_injective : Function.Injective moduleEmbedding)
    (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants ≤
      C.dimension := by
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
    Module.finrank k B.toRepresentation.Coinvariants =
        Module.finrank k
          restricted.range.toRepresentation.Coinvariants :=
      coinvariants_finrank_eq_of_representationEquiv rangeEquiv
    _ = Module.finrank k source.toRepresentation.Coinvariants :=
      coinvariants_finrank_descendGroupEquiv sigma groupEquiv restricted.range
    _ ≤ Module.finrank k
          (oddNormalizerFixedSpace sigma C.A C.g) :=
      subrepresentation_coinvariants_le_oddNormalizerFixedSpace
        hunit C.g_normalizes source
    _ = Module.finrank k C.fixed := by
      rw [oddNormalizerFixedSpace_eq C]
    _ = C.dimension := C.dimension_eq

end FiniteFrameOddNormalizerWitness

namespace FiniteFrameOddNormalizerRow

variable {G H V W : Type} [Group G] [Finite G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {sigma : Representation (ZMod 2) G W}
  {rho : Representation (ZMod 2) H V}
  {slots : ℕ}

/-- Row-level compatibility wrapper around the witness-only importer. -/
theorem module_bound_embedding
    [Finite V] [Finite W]
    (C : FiniteFrameOddNormalizerRow sigma slots)
    (groupEquiv : H ≃* G)
    (moduleEmbedding :
      rho.IntertwiningMap (sigma.comp groupEquiv.toMonoidHom))
    (moduleEmbedding_injective : Function.Injective moduleEmbedding)
    (B : Subrepresentation rho) :
    Module.finrank (ZMod 2) B.toRepresentation.Coinvariants ≤
      C.fixedWitness.dimension :=
  C.fixedWitness.module_bound_embedding
    (isUnit_iff_ne_zero.mpr
      ((ZMod.natCast_eq_zero_iff (Nat.card C.fixedWitness.A) 2).not.mpr
        C.fixedWitness.odd_order))
    groupEquiv moduleEmbedding moduleEmbedding_injective B

end FiniteFrameOddNormalizerRow

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

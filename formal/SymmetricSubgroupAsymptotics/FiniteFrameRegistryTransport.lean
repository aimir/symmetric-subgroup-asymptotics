import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrbitImporter
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.RepresentationHeadExact
import Mathlib.RepresentationTheory.Coinvariants

/-!
# Transport finite-frame registries to the literal retained action

Finite frame rows are most compactly checked on a finite Cayley/permutation
model.  The structural theorem, however, consumes the actual quotient top
and its actual translation representation.  This file provides the two
transport steps and keeps the identifying equivalences explicit.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace FiniteTopRelativeBinaryRankRegistry

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
  {rank : ℕ}

omit [Finite H] in
/-- A complete top registry transports across an exact group equivalence. -/
theorem bound_equiv (C : FiniteTopRelativeBinaryRankRegistry G rank)
    (e : G ≃* H) (N : Subgroup H) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ rank := by
  let M : Subgroup G := N.comap e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.comap inferInstance e.toMonoidHom
  have hmap : M.map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  rw [(relativeCharacterAmbientCongr 2 e M N hmap).finrank_eq]
  exact C.bound M

end FiniteTopRelativeBinaryRankRegistry
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu

namespace FiniteFrameRepresentationTransport

variable {k G H V W : Type} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Coinvariants preserve an explicit equivalence of representations of the
same group. -/
noncomputable def coinvariantsEquivOfRepresentationEquiv
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : rho.Equiv sigma) :
    rho.Coinvariants ≃ₗ[k] sigma.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).mapIso (Rep.mkIso e)).toLinearEquiv

theorem coinvariants_finrank_eq_of_representationEquiv
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : rho.Equiv sigma) :
    Module.finrank k rho.Coinvariants =
      Module.finrank k sigma.Coinvariants :=
  (coinvariantsEquivOfRepresentationEquiv e).finrank_eq

/-- Push an invariant subspace through an equivariant linear equivalence. -/
def mapEquiv
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : rho.Equiv sigma) (B : Subrepresentation rho) :
    Subrepresentation sigma where
  toSubmodule := B.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨rho g v, B.apply_mem_toSubmodule g hv, ?_⟩
    exact congrArg (fun f : V →ₗ[k] W ↦ f v) (e.isIntertwining' g)

/-- The restriction of the ambient equivalence to an invariant subspace and
its image is again an equivalence of representations. -/
noncomputable def mapRepresentationEquiv
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : rho.Equiv sigma) (B : Subrepresentation rho) :
    B.toRepresentation.Equiv (mapEquiv e B).toRepresentation := by
  apply Representation.Equiv.mk (e.toLinearEquiv.submoduleMap B.toSubmodule)
  intro g
  ext v
  exact congrArg (fun f : V →ₗ[k] W ↦ f v.1) (e.isIntertwining' g)

/-- Reindexing the acting group through an equivalence does not change the
coinvariant subspace. -/
theorem coinvariants_ker_comp_equiv
    (sigma : Representation k G W) (e : H ≃* G) :
    Representation.Coinvariants.ker (sigma.comp e.toMonoidHom) =
      Representation.Coinvariants.ker sigma := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨h, v⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨e h, v⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨e.symm g, v⟩, by simp⟩

/-- Coinvariant dimensions are unchanged by an exact reindexing of the
acting group. -/
theorem coinvariants_finrank_comp_equiv
    (sigma : Representation k G W) (e : H ≃* G) :
    Module.finrank k (Representation.Coinvariants
      (sigma.comp e.toMonoidHom)) =
      Module.finrank k sigma.Coinvariants :=
  (Submodule.quotEquivOfEq _ _ (coinvariants_ker_comp_equiv sigma e)).finrank_eq

/-- Descend a subrepresentation of a pulled-back representation along the
surjective group equivalence.  The underlying subspace is unchanged. -/
def descendGroupEquiv
    (sigma : Representation k G W) (e : H ≃* G)
    (B : Subrepresentation (sigma.comp e.toMonoidHom)) :
    Subrepresentation sigma where
  toSubmodule := B.toSubmodule
  apply_mem_toSubmodule g v hv := by
    simpa using B.apply_mem_toSubmodule (e.symm g) hv

/-- The source and descended actions have equal coinvariant dimensions. -/
theorem coinvariants_finrank_descendGroupEquiv
    (sigma : Representation k G W) (e : H ≃* G)
    (B : Subrepresentation (sigma.comp e.toMonoidHom)) :
    Module.finrank k B.toRepresentation.Coinvariants =
    Module.finrank k (descendGroupEquiv sigma e B).toRepresentation.Coinvariants := by
  have hrep : B.toRepresentation =
      (descendGroupEquiv sigma e B).toRepresentation.comp e.toMonoidHom := by
    ext h v
    rfl
  rw [hrep]
  exact coinvariants_finrank_comp_equiv
    (descendGroupEquiv sigma e B).toRepresentation e

end FiniteFrameRepresentationTransport

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace FiniteFrameModuleOrbitHeadRegistry

open FiniteFrameRepresentationTransport

variable {k G H V W : Type} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {sigma : Representation k G W} {rho : Representation k H V}
  {rank : ℕ}

/-- Transport a checked module row through an exact group equivalence and
an equivariant linear equivalence of the literal representations. -/
theorem bound_equiv [Finite V] [Finite W]
    (C : FiniteFrameModuleOrbitHeadRegistry sigma rank)
    (groupEquiv : H ≃* G)
    (moduleEquiv : rho.Equiv (sigma.comp groupEquiv.toMonoidHom))
    (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants ≤ rank := by
  let pulled := mapEquiv moduleEquiv B
  let source := descendGroupEquiv sigma groupEquiv pulled
  calc
    Module.finrank k B.toRepresentation.Coinvariants =
        Module.finrank k pulled.toRepresentation.Coinvariants :=
      coinvariants_finrank_eq_of_representationEquiv
        (mapRepresentationEquiv moduleEquiv B)
    _ = Module.finrank k source.toRepresentation.Coinvariants :=
      coinvariants_finrank_descendGroupEquiv sigma groupEquiv pulled
    _ ≤ rank := C.bound source

/-- Transport a checked ambient-module row back along an injective
intertwiner.  This is the form needed by the eight-block computation: the
literal correlated translation module embeds in the checked full induced
frame, but need not equal that full frame. -/
theorem bound_embedding [Finite V] [Finite W]
    (C : FiniteFrameModuleOrbitHeadRegistry sigma rank)
    (groupEquiv : H ≃* G)
    (moduleEmbedding :
      rho.IntertwiningMap (sigma.comp groupEquiv.toMonoidHom))
    (moduleEmbedding_injective : Function.Injective moduleEmbedding)
    (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants ≤ rank := by
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
        Module.finrank k restricted.range.toRepresentation.Coinvariants :=
      coinvariants_finrank_eq_of_representationEquiv rangeEquiv
    _ = Module.finrank k source.toRepresentation.Coinvariants :=
      coinvariants_finrank_descendGroupEquiv sigma groupEquiv restricted.range
    _ ≤ rank := C.bound source

end FiniteFrameModuleOrbitHeadRegistry

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

namespace DegreeFourZeroCoreFiniteFrameBounds

/-- Import a row checked on an exactly matched finite model.  The group
equivalence identifies the actual complement quotient with the row's top;
the representation equivalence identifies the actual correlated
translation module with the row module pulled back along that group
equivalence. -/
noncomputable def ofMatchedOrbitRegistries
    {G W : Type} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod (elementaryChart block P).p) W]
    [Finite W]
    {slots topSlots moduleSlots : ℕ}
    [Finite (elementaryChart block P).V]
    (sigma : Representation (ZMod (elementaryChart block P).p) G W)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* G)
    (moduleEquiv :
      (elementaryChart block P).quotientRepresentation.ρ.Equiv
        (sigma.comp groupEquiv.toMonoidHom))
    (slot_sum_le : topSlots + moduleSlots ≤ slots)
    (top : FiniteTopRelativeBinaryRankRegistry G topSlots)
    (module : FiniteFrameModuleOrbitHeadRegistry sigma moduleSlots) :
    DegreeFourZeroCoreFiniteFrameBounds block P slots where
  topSlots := topSlots
  moduleSlots := moduleSlots
  slot_sum_le := slot_sum_le
  topRelativeBinaryRank := by
    intro L
    letI : L.1.Normal := L.2
    exact top.bound_equiv groupEquiv.symm L.1
  translationModuleHead := by
    intro B
    letI : Finite (elementaryChart block P).quotientRepresentation :=
      inferInstanceAs (Finite (elementaryChart block P).V)
    exact module.bound_equiv groupEquiv moduleEquiv B

end DegreeFourZeroCoreFiniteFrameBounds

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

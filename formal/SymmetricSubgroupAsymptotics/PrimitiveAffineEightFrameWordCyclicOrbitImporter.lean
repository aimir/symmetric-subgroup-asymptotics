import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameCyclicOrbitImporter
import SymmetricSubgroupAsymptotics.FiniteFrameRegistryTransport
import SymmetricSubgroupAsymptotics.FiniteTopRelativeBinaryRankWordRegistry

/-!
# Practical sparse importer for eight-block finite frames

The top is certified from conjugacy representatives and normal-closure word
transitions.  The module is certified from vector-orbit coverage and a join
table indexed only by distinct cyclic invariant submodules.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace FiniteFrameModuleCyclicOrbitHeadRegistry

variable {k G H V W : Type} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {sigma : Representation k G W} {rho : Representation k H V}
  {rank : ℕ}

/-- Transport a deduplicated cyclic-orbit row through exact group and module
equivalences. -/
theorem bound_equiv [Finite V] [Finite W]
    (C : FiniteFrameModuleCyclicOrbitHeadRegistry sigma rank)
    (groupEquiv : H ≃* G)
    (moduleEquiv : rho.Equiv (sigma.comp groupEquiv.toMonoidHom))
    (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants ≤ rank :=
  C.toOrbitRegistry.bound_equiv groupEquiv moduleEquiv B

/-- Restrict a checked full-frame row along the actual correlated
translation-module embedding. -/
theorem bound_embedding [Finite V] [Finite W]
    (C : FiniteFrameModuleCyclicOrbitHeadRegistry sigma rank)
    (groupEquiv : H ≃* G)
    (moduleEmbedding :
      rho.IntertwiningMap (sigma.comp groupEquiv.toMonoidHom))
    (moduleEmbedding_injective : Function.Injective moduleEmbedding)
    (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants ≤ rank :=
  C.toOrbitRegistry.bound_embedding groupEquiv moduleEmbedding
    moduleEmbedding_injective B

end FiniteFrameModuleCyclicOrbitHeadRegistry

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

namespace DegreeFourZeroCoreFiniteFrameBounds

/-- Import a finite row with both sparse top words and deduplicated cyclic
module joins.  The top is identified exactly, while the literal correlated
translation module is embedded in the checked full frame. -/
noncomputable def ofMatchedWordCyclicOrbitRegistries
    {G W I iota kappa : Type} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod (elementaryChart block P).p) W]
    [Finite W]
    [Finite (elementaryChart block P).V]
    {c slots topSlots moduleSlots : ℕ}
    {representative : Fin c → G}
    (cover : FiniteConjugacyCardinalCover representative)
    (ambient : iota → G) (stateGenerators : I → kappa → G)
    (sigma : Representation (ZMod (elementaryChart block P).p) G W)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* G)
    (moduleEmbedding :
      (elementaryChart block P).quotientRepresentation.ρ.IntertwiningMap
        (sigma.comp groupEquiv.toMonoidHom))
    (moduleEmbedding_injective : Function.Injective moduleEmbedding)
    (slot_sum_le : topSlots + moduleSlots ≤ slots)
    (top : FiniteTopRelativeBinaryRankWordRegistry
      (rank := topSlots) cover ambient stateGenerators)
    (module : FiniteFrameModuleCyclicOrbitHeadRegistry sigma moduleSlots) :
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
    exact module.bound_embedding groupEquiv moduleEmbedding
      moduleEmbedding_injective B

end DegreeFourZeroCoreFiniteFrameBounds

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

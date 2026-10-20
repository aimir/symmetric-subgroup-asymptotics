import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitRegistry
import SymmetricSubgroupAsymptotics.Non2PreE7OrdinaryNumericalInstances
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFiniteNormalImporter

/-! # Lightweight interface for literal degree-two pair tops -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

structure DegreeTwoPairTopFiniteInterface (s : ℕ) : Type 1 where
  top : Subgroup (Equiv.Perm (Fin s))
  normalRegistry : FiniteNormalStateRegistry top
  ModuleState : Type
  [moduleStateFinite : Finite ModuleState]
  moduleState : ModuleState → Subrepresentation
    (permutationFunctionRepresentation (ZMod 2) top (Fin s))
  moduleState_injective : Function.Injective moduleState
  moduleRegistry : BinaryInvariantCyclicOrbitRegistry
    (permutationFunctionRepresentation (ZMod 2) top (Fin s)) moduleState
  normalCount : ℕ
  moduleStateCount : ℕ
  cyclicCount : ℕ
  normalCount_eq : Nat.card normalRegistry.State = normalCount
  moduleStateCount_eq : Nat.card ModuleState = moduleStateCount
  cyclicCount_eq : Nat.card moduleRegistry.Cyclic = cyclicCount

attribute [instance] DegreeTwoPairTopFiniteInterface.moduleStateFinite

namespace DegreeTwoPairTopFiniteInterface

variable {s : ℕ} (D : DegreeTwoPairTopFiniteInterface s)

/-- Assemble an interface from independently checked normal and natural
permutation-module registries.  This is the target used by the generated
pair-top rows: their old shared-top certificates supply `normalRegistry`,
while the selected natural-module emitter supplies the remaining fields. -/
noncomputable def ofRegistries
    (top : Subgroup (Equiv.Perm (Fin s)))
    (normalRegistry : FiniteNormalStateRegistry top)
    (ModuleState : Type) [Finite ModuleState]
    (moduleState : ModuleState → Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) top (Fin s)))
    (moduleState_injective : Function.Injective moduleState)
    (moduleRegistry : BinaryInvariantCyclicOrbitRegistry
      (permutationFunctionRepresentation (ZMod 2) top (Fin s)) moduleState)
    (normalCount moduleStateCount cyclicCount : ℕ)
    (normalCount_eq : Nat.card normalRegistry.State = normalCount)
    (moduleStateCount_eq : Nat.card ModuleState = moduleStateCount)
    (cyclicCount_eq : Nat.card moduleRegistry.Cyclic = cyclicCount) :
    DegreeTwoPairTopFiniteInterface s where
  top := top
  normalRegistry := normalRegistry
  ModuleState := ModuleState
  moduleState := moduleState
  moduleState_injective := moduleState_injective
  moduleRegistry := moduleRegistry
  normalCount := normalCount
  moduleStateCount := moduleStateCount
  cyclicCount := cyclicCount
  normalCount_eq := normalCount_eq
  moduleStateCount_eq := moduleStateCount_eq
  cyclicCount_eq := cyclicCount_eq

/-- Every literal normal subgroup of the top is one emitted normal state. -/
theorem normal_complete (N : Subgroup D.top) [N.Normal] :
    ∃ i, D.normalRegistry.state i = N :=
  D.normalRegistry.complete N

/-- Every invariant binary submodule of the actual top action is one emitted
module state.  Completeness comes from vector-orbit coverage and cyclic-sum
closure, not from the stored list length. -/
theorem module_complete
    (W : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin s))) :
    ∃ i, D.moduleState i = W :=
  D.moduleRegistry.complete W

/-- The duplicate-free module states are exactly all invariant submodules. -/
noncomputable def moduleStateEquiv :
    D.ModuleState ≃ Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin s)) :=
  Equiv.ofBijective D.moduleState
    ⟨D.moduleState_injective, D.module_complete⟩

/-- Complete a checked top-normal registry with the canonical semantic
registry of all invariant subrepresentations of the natural binary
permutation module.  This is a census-free bridge for small pilot rows and
for legacy top certificates whose old module table used a different
representation.  A compressed generated module registry can later replace
it without changing any downstream state-profile theorem. -/
noncomputable def withCanonicalModuleRegistry
    (top : Subgroup (Equiv.Perm (Fin s)))
    (normalRegistry : FiniteNormalStateRegistry top) :
    DegreeTwoPairTopFiniteInterface s := by
  let rho := permutationFunctionRepresentation (ZMod 2) top (Fin s)
  exact
    { top := top
      normalRegistry := normalRegistry
      ModuleState := Subrepresentation rho
      moduleState := id
      moduleState_injective := Function.injective_id
      moduleRegistry :=
        BinaryInvariantCyclicOrbitRegistry.allSubrepresentations
      normalCount := Nat.card normalRegistry.State
      moduleStateCount := Nat.card (Subrepresentation rho)
      cyclicCount := Nat.card (Fin s → ZMod 2)
      normalCount_eq := rfl
      moduleStateCount_eq := rfl
      cyclicCount_eq := rfl }

/-- Canonical semantic interface on an explicitly specified finite top.
Both axes are the literal normal subgroups and invariant subrepresentations
themselves.  It is useful for uniform natural tops and as a fallback while a
compressed generated table is being connected. -/
noncomputable def withCanonicalRegistries
    (top : Subgroup (Equiv.Perm (Fin s))) :
    DegreeTwoPairTopFiniteInterface s :=
  withCanonicalModuleRegistry top
    (FiniteNormalStateRegistry.allNormals (U := top))

/-- Direct shared-top adapter: transport an executable complete normal-word
registry to its literal permutation top and install the canonical natural
module registry. -/
noncomputable def ofWordRegistryEquiv
    {G I ι κ : Type} [Group G] [Finite G] [Finite I]
    {c : ℕ} {representative : Fin c → G}
    (C : FiniteConjugacyCardinalCover representative)
    (ambient : ι → G) (stateGenerators : I → κ → G)
    (normalData : FiniteNormalJoinWordRegistryData
      C ambient stateGenerators)
    (top : Subgroup (Equiv.Perm (Fin s)))
    (e : G ≃* top) : DegreeTwoPairTopFiniteInterface s :=
  withCanonicalModuleRegistry top
    (FiniteNormalStateRegistry.ofWordRegistryEquiv
      C ambient stateGenerators normalData e)

end DegreeTwoPairTopFiniteInterface

structure DegreeTwoPairTopRealization {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (p : PreE7PairActionClass s) : Type 1 where
  frame : BinaryPairFrame (preE7PairAction s p) (Fin s)
  topEquiv : D.top ≃* frame.top.range
  module_action_eq : ∀ g v,
    permutationFunctionRepresentation (ZMod 2) D.top (Fin s) g v =
      frame.coordinateTopAction (topEquiv g) v

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

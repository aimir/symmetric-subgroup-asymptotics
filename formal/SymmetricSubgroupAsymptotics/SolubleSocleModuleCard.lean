import SymmetricSubgroupAsymptotics.SolubleSocleModuleGenerators
import SymmetricSubgroupAsymptotics.BoundedNormalChains

/-! Literal cardinality transport between an integral conjugation
submodule and its actual ambient subgroup. Bounded chief sections therefore
bound the actual simple row carriers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

def submoduleGroupEquiv
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (S : Submodule ℤ[G] (representation N).asModule) : S ≃ Additive (submoduleGroup N S) where
  toFun s := Additive.ofMul
    ⟨(s.val.toMul : G),(mem_submoduleGroup N S s.val.toMul).mpr s.property⟩
  invFun x :=
    let n : N := ⟨(x.toMul : G),submoduleGroup_le N S x.toMul.property⟩
    ⟨Additive.ofMul n,(mem_submoduleGroup N S n).mp x.toMul.property⟩
  left_inv s := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

theorem card_submoduleGroup
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (S : Submodule ℤ[G] (representation N).asModule) :
    Nat.card S=Nat.card (submoduleGroup N S) :=
  (Nat.card_congr (submoduleGroupEquiv N S)).trans (Nat.card_congr Additive.toMul)

theorem simple_card_le_of_boundedChiefSections
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (S : Submodule ℤ[G] (representation N).asModule)
    (hS : IsSimpleModule ℤ[G] ↥S) (B : ℕ)
    (hB : MarkedC4.OrdinaryNilpotentGeneration.BoundedChiefSections B G) :
    Nat.card S ≤ B := by
  rw [card_submoduleGroup N S]
  exact hB G G (MonoidHom.id G) Function.injective_id
    (MonoidHom.id G) Function.surjective_id (submoduleGroup N S)
    (simple_isMinimalNormal N S hS)

end SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

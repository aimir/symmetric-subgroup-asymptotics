import SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! The original row237 and row238 six-pair images contain both local
symmetric groups and the block exchange. The displayed short words give
literal full-image equalities, so the existing actual-image wreath theorem
provides quotient-socle capacity three. Historical capacity two is unchanged. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairImageSocles

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairCyclicSymmetricSocles SixPairLocalWreathSocles

/-- Original row237, zero-based index236, joint; historical (2,1). -/
def row237Codes : Fin 4 → Model :=
  ![1, firstTranslation, inl (1,reflection),
    inl (1,translation * reflection) * blockSwap]

/-- Original row238, zero-based index237, joint; historical (2,1). -/
def row238Codes : Fin 4 → Model :=
  ![1, firstTranslation, inl (1,reflection) * blockSwap, firstReflection]

def row237Tops (i : Fin 4) : Equiv.Perm (Fin 6) := literalAction (row237Codes i)
def row238Tops (i : Fin 4) : Equiv.Perm (Fin 6) := literalAction (row238Codes i)

theorem row237_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row237Generators i) (row237Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row238_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row238Generators i) (row238Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row237Frame : BinaryPairFrame Row237Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row237Generators row237Tops row237_preserves

def row238Frame : BinaryPairFrame Row238Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row238Generators row238Tops row238_preserves

theorem row237_reflection : literalAction firstReflection =
    row237Tops 3 * row237Tops 2 * (row237Tops 3)⁻¹ := by
  decide +kernel

theorem row237_exchange : literalAction blockSwap =
    row237Tops 3 * row237Tops 1 * row237Tops 3 * row237Tops 2 * (row237Tops 3)⁻¹ := by
  decide +kernel

theorem row238_exchange : literalAction blockSwap = row238Tops 2 * row238Tops 3 := by
  decide +kernel

theorem row237_range : row237Frame.top.range = literalAction.range := by
  apply (BinaryPairFrame.ofGenerators_top_range _ _ _ row237_preserves).trans
  apply generated_range row237Codes
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · have hm (i : Fin 4) : row237Tops i ∈ Subgroup.closure (Set.range row237Tops) :=
      Subgroup.subset_closure ⟨i,rfl⟩
    let K := Subgroup.closure (Set.range row237Tops)
    rw [row237_reflection]
    exact K.mul_mem (K.mul_mem (hm 3) (hm 2)) (K.inv_mem (hm 3))
  · have hm (i : Fin 4) : row237Tops i ∈ Subgroup.closure (Set.range row237Tops) :=
      Subgroup.subset_closure ⟨i,rfl⟩
    let K := Subgroup.closure (Set.range row237Tops)
    rw [row237_exchange]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (hm 3) (hm 1)) (hm 3)) (hm 2))
      (K.inv_mem (hm 3))

theorem row238_range : row238Frame.top.range = literalAction.range := by
  apply (BinaryPairFrame.ofGenerators_top_range _ _ _ row238_preserves).trans
  apply generated_range row238Codes
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · exact Subgroup.subset_closure ⟨3,rfl⟩
  · have hm (i : Fin 4) : row238Tops i ∈ Subgroup.closure (Set.range row238Tops) :=
      Subgroup.subset_closure ⟨i,rfl⟩
    rw [row238_exchange]
    exact (Subgroup.closure (Set.range row238Tops)).mul_mem (hm 2) (hm 3)

theorem row237AtThree_quotientSocle (N : Subgroup Row237Top) [N.Normal] :
    SocleNormalGeneratorBound (Row237Top ⧸ N) 3 :=
  SixPairLocalWreathSocles.quotientSocle row237Frame row237_range N

theorem row238AtThree_quotientSocle (N : Subgroup Row238Top) [N.Normal] :
    SocleNormalGeneratorBound (Row238Top ⧸ N) 3 :=
  SixPairLocalWreathSocles.quotientSocle row238Frame row238_range N

def row237AtThree_family : row237Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row237AtThree_quotientSocle N.1)

def row238AtThree_family : row238Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row238AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairImageSocles

end

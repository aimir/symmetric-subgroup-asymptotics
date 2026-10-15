import SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Two original twelve-point groups have full S3 wreath C2 image on their
six physical pairs. The short exchange identities establish the full image,
including both independent local factors. Capacity three is exact for
row235 and an alternate capacity for row201. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLocalWreathPairImageSocles

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairCyclicSymmetricSocles SixPairLocalWreathSocles

def row201Codes : Fin 5 → Model :=
  ![1, 1, inl (reflection,translation * reflection) * blockSwap,
    firstTranslation, firstReflection]

def row235Codes : Fin 5 → Model :=
  ![1, firstTranslation, inl (1,translation) * blockSwap,
    inl (translation * reflection,reflection), firstReflection]

def row201Tops (i : Fin 5) : Equiv.Perm (Fin 6) := literalAction (row201Codes i)
def row235Tops (i : Fin 5) : Equiv.Perm (Fin 6) := literalAction (row235Codes i)

theorem row201_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row201Generators i) (row201Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row235_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row235Generators i) (row235Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row201Frame : BinaryPairFrame Row201Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row201Generators row201Tops row201_preserves

def row235Frame : BinaryPairFrame Row235Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row235Generators row235Tops row235_preserves

theorem row201_exchange : literalAction blockSwap =
    row201Tops 2 * (row201Tops 3)⁻¹ * row201Tops 4 * row201Tops 3 *
      (row201Tops 2)⁻¹ * row201Tops 4 * row201Tops 2 := by
  decide +kernel

theorem row235_exchange : literalAction blockSwap = row235Tops 2 * (row235Tops 1)⁻¹ := by
  decide +kernel

theorem row201_range : row201Frame.top.range = literalAction.range := by
  apply (BinaryPairFrame.ofGenerators_top_range _ _ _ row201_preserves).trans
  apply generated_range row201Codes
  · exact Subgroup.subset_closure ⟨3,rfl⟩
  · exact Subgroup.subset_closure ⟨4,rfl⟩
  · have hm (i : Fin 5) : row201Tops i ∈ Subgroup.closure (Set.range row201Tops) :=
      Subgroup.subset_closure ⟨i,rfl⟩
    let K := Subgroup.closure (Set.range row201Tops)
    rw [row201_exchange]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
      (hm 2) (K.inv_mem (hm 3))) (hm 4)) (hm 3)) (K.inv_mem (hm 2))) (hm 4)) (hm 2)

theorem row235_range : row235Frame.top.range = literalAction.range := by
  apply (BinaryPairFrame.ofGenerators_top_range _ _ _ row235_preserves).trans
  apply generated_range row235Codes
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · exact Subgroup.subset_closure ⟨4,rfl⟩
  · have hm (i : Fin 5) : row235Tops i ∈ Subgroup.closure (Set.range row235Tops) :=
      Subgroup.subset_closure ⟨i,rfl⟩
    rw [row235_exchange]
    exact (Subgroup.closure (Set.range row235Tops)).mul_mem (hm 2)
      ((Subgroup.closure (Set.range row235Tops)).inv_mem (hm 1))

theorem row201AtThree_quotientSocle (N : Subgroup Row201Top) [N.Normal] :
    SocleNormalGeneratorBound (Row201Top ⧸ N) 3 :=
  SixPairLocalWreathSocles.quotientSocle row201Frame row201_range N

theorem row235_quotientSocle (N : Subgroup Row235Top) [N.Normal] :
    SocleNormalGeneratorBound (Row235Top ⧸ N) 3 :=
  SixPairLocalWreathSocles.quotientSocle row235Frame row235_range N

def row201AtThree_family : row201Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row201AtThree_quotientSocle N.1)

def row235_family : row235Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row235_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLocalWreathPairImageSocles

end

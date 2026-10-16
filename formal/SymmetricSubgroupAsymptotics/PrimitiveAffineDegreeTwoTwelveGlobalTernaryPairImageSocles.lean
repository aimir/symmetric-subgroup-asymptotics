import SymmetricSubgroupAsymptotics.SixPairDihedralSocles
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Original row54 has the full dihedral image on its six physical pairs.
The fixed chart follows the orbit of the original word g1*g2*g3.
Explicit image codes and words prove equality with the dihedral image. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveGlobalTernaryPairImageSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairCyclicSymmetricSocles SixPairDihedralSocles

def row54Chart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![0,5,7,1,3,9] p.1 else ![11,6,8,2,4,10] p.1
  invFun x := (![0,3,3,4,4,1,1,2,2,5,5,0] x,
    ![0,0,1,0,1,0,1,0,1,0,1,1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row54Codes : Fin 4 → DihedralGroup 6 :=
  ![.r 0, .r 4, .sr 5, .sr 2]

def row54Tops (i : Fin 4) : Equiv.Perm (Fin 6) := dihedralMap (row54Codes i)

theorem row54_preserves : ∀ i,
    BinaryPairFrame.Preserves row54Chart (row54Generators i) (row54Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row54Frame : BinaryPairFrame Row54Top (Fin 6) :=
  BinaryPairFrame.ofGenerators row54Chart row54Generators row54Tops row54_preserves

def row54CycleWord : Row54Top :=
  closureGenerators row54Generators 1 * closureGenerators row54Generators 2 *
    closureGenerators row54Generators 3

theorem row54_cycle : row54Frame.top row54CycleWord = cycle := by
  have hg (i : Fin 4) : row54Frame.top (closureGenerators row54Generators i) = row54Tops i :=
    BinaryPairFrame.ofGenerators_top_generator row54Chart row54Generators row54Tops row54_preserves i
  simp only [row54CycleWord, map_mul, hg]
  decide +kernel

theorem row54_cycle_literal : row54Tops 1 * row54Tops 2 * row54Tops 3 = cycle := by
  decide +kernel

theorem row54_reflection_literal : row54Tops 2 * cycle = reflection := by
  decide +kernel

theorem row54_range : row54Frame.top.range = dihedralMap.range := by
  change (BinaryPairFrame.ofGenerators row54Chart row54Generators row54Tops
    row54_preserves).top.range = dihedralMap.range
  rw [BinaryPairFrame.ofGenerators_top_range _ _ _ row54_preserves]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨row54Codes i, rfl⟩
  · have hm (i : Fin 4) : row54Tops i ∈ Subgroup.closure (Set.range row54Tops) :=
      Subgroup.subset_closure ⟨i, rfl⟩
    let K := Subgroup.closure (Set.range row54Tops)
    have hc : cycle ∈ K := by
      rw [← row54_cycle_literal]
      exact K.mul_mem (K.mul_mem (hm 1) (hm 2)) (hm 3)
    have hs : reflection ∈ K := by
      rw [← row54_reflection_literal]
      exact K.mul_mem (hm 2) hc
    rintro _ ⟨g, rfl⟩
    cases g with
    | r i => exact K.pow_mem hc i.val
    | sr i => exact K.mul_mem hs (K.pow_mem hc i.val)

theorem row54AtThree_quotientSocle (N : Subgroup Row54Top) [N.Normal] :
    SocleNormalGeneratorBound (Row54Top ⧸ N) 3 :=
  SixPairDihedralSocles.quotientSocle row54Frame row54CycleWord row54_cycle row54_range N

def row54AtThree_family : row54Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row54AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveGlobalTernaryPairImageSocles

end

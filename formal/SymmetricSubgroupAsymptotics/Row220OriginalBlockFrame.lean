import SymmetricSubgroupAsymptotics.Row182OriginalPrimitiveComponent
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveReferencePairWitness

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily
abbrev Original := Row220Top
abbrev pointFrame := Row182OriginalBlockKernel.pointFrame
abbrev swap := Row182OriginalBlockKernel.swap

def tops : Fin 4 → Equiv.Perm (Fin 2) := ![1,1,1,swap]
private theorem preserves : ∀ (j : Fin 4) (z : Fin 2 × Fin 6),
    (pointFrame.symm (row220Generators j (pointFrame z))).1 = tops j z.1 := by decide +kernel

def blockFrame : ProductBlockFrame Original (Fin 2) (Fin 6) :=
  ProductBlockFrame.ofGenerators pointFrame row220Generators tops preserves

def originalGenerator : Fin 4 → Original := originalGeneratedGenerators row220Generators

theorem top_generator (j : Fin 4) : blockFrame.top (originalGenerator j) = tops j :=
  ProductBlockFrame.ofGenerators_top_generator pointFrame row220Generators tops preserves j

theorem top_surjective : Function.Surjective blockFrame.top := by
  intro q
  have h : q = 1 ∨ q = swap :=
    (show ∀ q : Equiv.Perm (Fin 2), q = 1 ∨ q = swap from by decide +kernel) q
  rcases h with rfl | rfl
  · exact ⟨1,map_one _⟩
  · exact ⟨originalGenerator 3,top_generator 3⟩

abbrev inclusion : Row182OriginalBlockKernel.Original →* Original := row220Embedding.topMap

private theorem top_inclusion (g : Row182OriginalBlockKernel.Original) :
    blockFrame.top (inclusion g) = Row182OriginalBlockKernel.blockFrame.top g := by
  apply Equiv.ext
  intro i
  have h := blockFrame.intertwine (inclusion g) (i,0)
  have hsmall := Row182OriginalBlockKernel.blockFrame.intertwine g (i,0)
  exact h.symm.trans hsmall

def kernelInclusion : Row182OriginalBlockKernel.blockFrame.top.ker →* blockFrame.top.ker :=
  (inclusion.comp Row182OriginalBlockKernel.blockFrame.top.ker.subtype).codRestrict _
    (fun k => by
      change blockFrame.top (inclusion k.1) = 1
      rw [top_inclusion]
      exact k.2)

theorem coordinate_inclusion (s : Fin 2)
    (k : Row182OriginalBlockKernel.blockFrame.top.ker) :
    blockFrame.kernelCoordinate s (kernelInclusion k) =
      Row182OriginalBlockKernel.blockFrame.kernelCoordinate s k := by
  apply Equiv.ext
  intro x
  rfl

abbrev Component (s : Fin 2) := (blockFrame.kernelCoordinate s).range

theorem component_zero_two_pretransitive :
    MulAction.IsMultiplyPretransitive (Component 0) (Fin 6) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g,hg0,hg1⟩ := MulAction.is_two_pretransitive_iff.mp
    Row182OriginalBlockKernel.component_two_pretransitive hab hcd
  obtain ⟨k,hk⟩ := g.2
  refine ⟨(blockFrame.kernelCoordinate 0).rangeRestrict (kernelInclusion k),?_,?_⟩
  · change blockFrame.kernelCoordinate 0 (kernelInclusion k) a = c
    rw [coordinate_inclusion,hk]
    exact hg0
  · change blockFrame.kernelCoordinate 0 (kernelInclusion k) b = d
    rw [coordinate_inclusion,hk]
    exact hg1

end SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame

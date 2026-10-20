import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import SymmetricSubgroupAsymptotics.IndexTwoSchreier
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue
abbrev Original := Row278Top
def pointFrame : Fin 2 × Fin 6 ≃ Fin 12 :=
  (Equiv.prodComm (Fin 2) (Fin 6)).trans finProdFinEquiv
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def tops : Fin 3 → Equiv.Perm (Fin 2) := ![1, 1, swap]
private theorem frame_checked : ∀ (j : Fin 3) (p : Fin 2 × Fin 6),
    (pointFrame.symm (row278Generators j (pointFrame p))).1 = tops j p.1 := by decide +kernel
def blockFrame : ProductBlockFrame Original (Fin 2) (Fin 6) :=
  ProductBlockFrame.ofGenerators pointFrame row278Generators tops frame_checked
def originalGenerator : Fin 3 → Original := originalGeneratedGenerators row278Generators
theorem top_generator (j : Fin 3) : blockFrame.top (originalGenerator j) = tops j :=
  ProductBlockFrame.ofGenerators_top_generator pointFrame row278Generators tops frame_checked j
end SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame

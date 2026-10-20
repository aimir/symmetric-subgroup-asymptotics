import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import SymmetricSubgroupAsymptotics.IndexTwoSchreier
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Row298OriginalBlockFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue
abbrev Original := Row298Top
def pointFrame : Fin 2 × Fin 6 ≃ Fin 12 :=
  (Equiv.prodComm (Fin 2) (Fin 6)).trans finProdFinEquiv
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def tops : Fin 4 → Equiv.Perm (Fin 2) := ![1, 1, 1, swap]
private theorem frame_checked : ∀ (j : Fin 4) (p : Fin 2 × Fin 6),
    (pointFrame.symm (row298Generators j (pointFrame p))).1 = tops j p.1 := by decide +kernel
def blockFrame : ProductBlockFrame Original (Fin 2) (Fin 6) :=
  ProductBlockFrame.ofGenerators pointFrame row298Generators tops frame_checked
def originalGenerator : Fin 4 → Original := originalGeneratedGenerators row298Generators
theorem top_generator (j : Fin 4) : blockFrame.top (originalGenerator j) = tops j :=
  ProductBlockFrame.ofGenerators_top_generator pointFrame row298Generators tops frame_checked j
end SymmetricSubgroupAsymptotics.Row298OriginalBlockFrame

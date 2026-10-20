import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import SymmetricSubgroupAsymptotics.SubdirectPureCoordinateCore
import SymmetricSubgroupAsymptotics.IndexTwoSchreier
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Selected original row269 physical block frame and nontrivial pure
coordinate kernel. This is the full-product route, not the row182 graph
route. Primitive-component and simple-core/top receipts remain separate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Row269OriginalBlockFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

abbrev Original := Row269Top
def pointFrame : Fin 2 × Fin 6 ≃ Fin 12 :=
  (Equiv.prodComm (Fin 2) (Fin 6)).trans finProdFinEquiv
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def tops : Fin 3 → Equiv.Perm (Fin 2) := ![1, 1, swap]
private theorem frame_checked : ∀ (j : Fin 3) (p : Fin 2 × Fin 6),
    (pointFrame.symm (row269Generators j (pointFrame p))).1 = tops j p.1 := by
  decide +kernel
def blockFrame : ProductBlockFrame Original (Fin 2) (Fin 6) :=
  ProductBlockFrame.ofGenerators pointFrame row269Generators tops frame_checked
def originalGenerator : Fin 3 → Original := originalGeneratedGenerators row269Generators
theorem top_generator (j : Fin 3) : blockFrame.top (originalGenerator j) = tops j :=
  ProductBlockFrame.ofGenerators_top_generator pointFrame row269Generators tops frame_checked j

def pureKernel : blockFrame.top.ker :=
  ⟨originalGenerator 0, by
    change blockFrame.top (originalGenerator 0) = 1
    rw [top_generator]
    rfl⟩
theorem pure_left : blockFrame.kernelCoordinate 0 pureKernel = 1 := by
  apply Equiv.ext
  decide +kernel
theorem pure_right_ne : blockFrame.kernelCoordinate 1 pureKernel ≠ 1 := by
  decide +kernel

abbrev Left := (blockFrame.kernelCoordinate 0).range
abbrev Right := (blockFrame.kernelCoordinate 1).range
def leftRestriction : blockFrame.top.ker →* Left := (blockFrame.kernelCoordinate 0).rangeRestrict
def rightRestriction : blockFrame.top.ker →* Right := (blockFrame.kernelCoordinate 1).rangeRestrict
def pairMap : blockFrame.top.ker →* Left × Right := leftRestriction.prod rightRestriction
def pairImage : Subgroup (Left × Right) := pairMap.range

theorem pairMap_injective : Function.Injective pairMap := by
  intro x y h
  apply blockFrame.twoKernelMap_injective
  exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
    (congrArg Subtype.val (congrArg Prod.snd h))

theorem pairImage_right_surjective : ∀ r : Right, ∃ l : Left, (l,r) ∈ pairImage := by
  intro r
  obtain ⟨u,hu⟩ := (blockFrame.kernelCoordinate 1).rangeRestrict_surjective r
  refine ⟨leftRestriction u, u, ?_⟩
  refine Prod.ext ?_ ?_
  · rfl
  · exact hu

instance rightPure_normal : (SubdirectPureCoordinateCore.rightPure pairImage).Normal :=
  SubdirectPureCoordinateCore.rightPure_normal pairImage pairImage_right_surjective

theorem selected_pure_mem : ((1 : Left),rightRestriction pureKernel) ∈ pairImage := by
  refine ⟨pureKernel, ?_⟩
  refine Prod.ext ?_ rfl
  apply Subtype.ext
  exact pure_left

theorem rightPure_nontrivial : SubdirectPureCoordinateCore.rightPure pairImage ≠ ⊥ := by
  apply SubdirectPureCoordinateCore.rightPure_ne_bot pairImage
    (rightRestriction pureKernel) selected_pure_mem
  intro h
  exact pure_right_ne (congrArg Subtype.val h)

/-- A proved primitive-six socle containment receipt can now be applied
to the actual opposite pure kernel, without enumerating original normals. -/
theorem right_core_in_pairImage (S : Subgroup Right)
    (hcore : ∀ N : Subgroup Right, N.Normal → N ≠ ⊥ → S ≤ N) :
    ∀ s : Right, s ∈ S → ((1 : Left),s) ∈ pairImage :=
  hcore (SubdirectPureCoordinateCore.rightPure pairImage) rightPure_normal rightPure_nontrivial

end SymmetricSubgroupAsymptotics.Row269OriginalBlockFrame

import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathModelTop
import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathGeneratorCoordinates
import SymmetricSubgroupAsymptotics.FourBlockKleinSignBase
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246OriginalTripleFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open FourBlockKleinSignBase (Base blocks first second)

def points : Fin 4 × Fin 3 ≃ Fin 12 where
  toFun x := (#[0,4,8,1,5,9,2,6,10,3,7,11] : Array (Fin 12))[3*x.1.val+x.2.val]!
  invFun x := (⟨x.val%4,Nat.mod_lt _ (by decide)⟩,⟨x.val/4,by omega⟩)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def baseCodes : Fin 4 → Base := ![1,1,first,second]
def tops : Fin 4 → Equiv.Perm (Fin 4) := fun i => blocks (baseCodes i)
private theorem preserves : ∀ i,ProductBlockFrame.Preserves points (row246Generators i) (tops i) := by
  unfold ProductBlockFrame.Preserves
  decide +kernel

def frame : ProductBlockFrame row246Interface.top (Fin 4) (Fin 3) :=
  ProductBlockFrame.ofGenerators points row246Generators tops preserves

theorem blocks_injective : Function.Injective blocks := by
  have h : ∀ b c : Base,(∀ i : Fin 4,blocks b i=blocks c i) → b=c := by decide +kernel
  exact fun _ _ he => h _ _ (fun i => congrArg (fun p : Equiv.Perm (Fin 4) => p i) he)
private theorem top_range_le : frame.top.range≤blocks.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    ProductBlockFrame.ofGenerators_top_range points row246Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨baseCodes i,rfl⟩
private def baseEquiv : Base ≃* blocks.range := MonoidHom.ofInjective blocks_injective

def top : row246Interface.top →* Base := baseEquiv.symm.toMonoidHom.comp
  (frame.top.codRestrict blocks.range (fun u => top_range_le ⟨u,rfl⟩))

theorem top_bind (u : row246Interface.top) : blocks (top u)=frame.top u := by
  exact congrArg Subtype.val (baseEquiv.apply_symm_apply
    (frame.top.codRestrict blocks.range (fun u => top_range_le ⟨u,rfl⟩) u))

theorem top_generator (i : Fin 4) : top (closureGenerators row246Generators i)=baseCodes i := by
  apply blocks_injective
  exact (top_bind _).trans
    (ProductBlockFrame.ofGenerators_top_generator points row246Generators tops preserves i)

theorem top_intertwines (u : row246Interface.top) :
    frame.top u=MulAction.toPermHom Base (Fin 4) (top u) := by
  have h : ∀ b : Base, blocks b=MulAction.toPermHom Base (Fin 4) b := by
    decide +kernel
  exact (top_bind u).symm.trans (h (top u))

def wreathEmbedding := frame.wreathEmbeddingOfTop top top_intertwines

theorem wreathEmbedding_injective : Function.Injective wreathEmbedding :=
  frame.wreathEmbeddingOfTop_injective top top_intertwines
end SymmetricSubgroupAsymptotics.Row246OriginalTripleFrame

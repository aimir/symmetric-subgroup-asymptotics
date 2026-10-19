import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row74OriginalSixPairFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def points : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun x := (#[0,11,9,2,1,4,3,6,5,8,7,10] : Array (Fin 12))[2*x.1.val+x.2.val]!
  invFun x := (#[(0,0),(2,0),(1,1),(3,0),(2,1),(4,0),
    (3,1),(5,0),(4,1),(1,0),(5,1),(0,1)] : Array (Fin 6 × ZMod 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rotation : Equiv.Perm (Fin 6) where
  toFun := ![0,2,3,4,5,1]
  invFun := ![0,5,1,2,3,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def swap : Equiv.Perm (Fin 6) where
  toFun := ![1,0,3,2,5,4]
  invFun := ![1,0,3,2,5,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tops : Fin 2 → Equiv.Perm (Fin 6) := ![rotation,swap]
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row74Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def frame : BinaryPairFrame row74Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row74Generators tops preserves

theorem top_generator (i : Fin 2) : frame.top (closureGenerators row74Generators i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator points row74Generators tops preserves i

/- This finite identity supplies point-stabilizer transitivity, without
any assertion about the order or faithfulness of the six-pair projection. -/
theorem rotation_orbit : ∀ y : Fin 6,y≠0 → ∃ j : Fin 5,(rotation^j.val) 1=y := by
  decide +kernel
end SymmetricSubgroupAsymptotics.Row74OriginalSixPairFrame

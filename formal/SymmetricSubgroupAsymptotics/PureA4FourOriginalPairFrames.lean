import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! The opposite-edge pairs inside the two six-point blocks. The failed
primitive-six pilot is not used: these are literal original point identities. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def points : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun x := (#[2,8,1,7,6,0,5,11,10,4,9,3] : Array (Fin 12))[2*x.1.val+x.2.val]!
  invFun x := (#[(2,1),(1,0),(0,0),(5,1),(4,1),(3,0),
    (2,0),(1,1),(0,1),(5,0),(4,0),(3,1)] : Array (Fin 6 × ZMod 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rotation : Equiv.Perm (Fin 6) where
  toFun := ![0,3,2,5,4,1]
  invFun := ![0,5,2,1,4,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def swap : Equiv.Perm (Fin 6) where
  toFun := ![1,0,3,2,5,4]
  invFun := ![1,0,3,2,5,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def scalar : Equiv.Perm (Fin 6) where
  toFun := ![4,5,2,3,0,1]
  invFun := ![4,5,2,3,0,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quarterSwap : Equiv.Perm (Fin 6) where
  toFun := ![1,4,3,2,5,0]
  invFun := ![5,0,3,2,1,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflection : Equiv.Perm (Fin 6) where
  toFun := ![0,5,2,3,4,1]
  invFun := ![0,5,2,3,4,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

namespace Row126
def tops : Fin 3 → Equiv.Perm (Fin 6) := ![1,rotation,swap]
theorem preserves : ∀ i, BinaryPairFrame.Preserves points (row126Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row126Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row126Generators tops preserves
end Row126

namespace Row160
def tops : Fin 4 → Equiv.Perm (Fin 6) := ![1,rotation,scalar,quarterSwap]
theorem preserves : ∀ i, BinaryPairFrame.Preserves points (row160Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row160Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row160Generators tops preserves
end Row160

namespace Row161
def tops : Fin 4 → Equiv.Perm (Fin 6) := ![1,rotation,scalar,swap]
theorem preserves : ∀ i, BinaryPairFrame.Preserves points (row161Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row161Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row161Generators tops preserves
end Row161

namespace Row203
def tops : Fin 4 → Equiv.Perm (Fin 6) := ![1,rotation,reflection,swap]
theorem preserves : ∀ i, BinaryPairFrame.Preserves points (row203Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row203Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row203Generators tops preserves
end Row203
end SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames

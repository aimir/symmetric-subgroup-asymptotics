import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureData
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
def centralCoordinate (i : Fin 64) (j : Fin 3) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd ((((#[#[0, 0, 0], #[0, 0, 0], #[0, 0, 0], #[1, 1, 0], #[1, 0, 0], #[0, 0, 0], #[0, 1, 1], #[0, 0, 0], #[1, 1, 0], #[1, 0, 0], #[0, 0, 0], #[0, 1, 1], #[1, 1, 0], #[1, 0, 0], #[0, 0, 0], #[0, 1, 1], #[0, 1, 0], #[1, 1, 0], #[1, 0, 1], #[1, 0, 0], #[1, 1, 1], #[0, 1, 1], #[1, 0, 1], #[1, 1, 1], #[1, 1, 0], #[1, 0, 0], #[0, 0, 0], #[0, 1, 1], #[0, 1, 0], #[1, 1, 0], #[1, 0, 1], #[1, 0, 0], #[1, 1, 1], #[0, 1, 1], #[1, 0, 1], #[1, 1, 1], #[0, 1, 0], #[1, 1, 0], #[1, 0, 1], #[1, 0, 0], #[1, 1, 1], #[0, 1, 1], #[1, 0, 1], #[1, 1, 1], #[0, 1, 0], #[0, 0, 1], #[1, 0, 1], #[0, 1, 1], #[0, 0, 1], #[1, 1, 1], #[1, 0, 1], #[1, 1, 1], #[1, 1, 0], #[1, 0, 0], #[0, 1, 0], #[0, 1, 0], #[0, 0, 1], #[0, 0, 1], #[0, 1, 0], #[0, 0, 1], #[0, 0, 1], #[0, 0, 1], #[0, 0, 1], #[0, 1, 0]] : Array (Array (ZMod 2)))[i.val]!)[j.val]!))
def isOriginalNormal (i : Fin 64) : Bool :=
  (#[true, true, true, false, false, true, false, true, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] : Array Bool)[i.val]!
def centralBasisIndex (i : Fin 3) : Fin 64 := (#[4, 16, 45] : Array (Fin 64))[i.val]!
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

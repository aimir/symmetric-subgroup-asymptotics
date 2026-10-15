import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairTrivialKernelSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTopRelativeHeads
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-! The faithful-pair-action branch needs only an exact literal match to
one of the twenty-four eight-point tops. Its relative-head bound is derived
from the checked original quotient socles, and its frame bound is proved
by the actual Sylow-three orbit geometry. This does not assert the separate
published catalogue locator or the existence of a pair system. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

def degreeFourZeroCoreSixteenPairTrivialBounds_of_literal
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker = ⊥) (hcard : Nat.card I = 8) (x : block.Points)
    (j : Fin 24) (points : I ≃ Fin 8) (g : Equiv.Perm (Fin 8))
    (matched : MulAut.conj g • relabelSubgroup points F.top.range =
      (DegreeTwoPairedEightSharedTops.interface j).top) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let e := PermutationStabilizerTransport.groupEquiv F.top.range
    (DegreeTwoPairedEightSharedTops.interface j).top points g matched
  apply degreeFourZeroCoreSixteenPairKernelTrivialBounds block P hr hD F hker hcard x
  intro N _
  exact PrimitiveAffineEightTopRelativeHeads.relativeHead_le_two_of_equiv 2 j e N

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end

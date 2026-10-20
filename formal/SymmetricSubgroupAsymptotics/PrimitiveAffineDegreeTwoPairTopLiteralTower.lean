import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopOriginalNormalSignature
import SymmetricSubgroupAsymptotics.BinaryPairTernaryNormalizerPrefix

/-! A literal pair frame on a retained top extends every original
realization to a two-frame realization. The existing module-action
binding also binds the original point permutations, so the new frame
does not replace the physical source action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

structure DegreeTwoPairTopLiteralTower {s t : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s) (L : DegreeTwoPairTopFiniteInterface t) where
  frame : BinaryPairFrame D.top (Fin t)
  range_eq : frame.top.range = L.top

namespace DegreeTwoPairTopLiteralTower

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {L : DegreeTwoPairTopFiniteInterface t} (C : DegreeTwoPairTopLiteralTower D L)
  {p : PreE7PairActionClass s} (R : DegreeTwoPairTopRealization D p)

def secondFrame : BinaryPairFrame R.frame.top.range (Fin t) :=
  BinaryPairFrame.ofEquiv R.topEquiv C.frame.top C.frame.frame (by
    intro g x
    rw [BinaryPairTernaryNormalizerPrefix.realization_topEquiv_perm_eq R g]
    exact C.frame.intertwine g x)

theorem secondFrame_range : (C.secondFrame R).top.range = L.top := by
  rw [← C.range_eq]
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨R.topEquiv.symm u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨R.topEquiv u, ?_⟩
    change C.frame.top (R.topEquiv.symm (R.topEquiv u)) = C.frame.top u
    rw [R.topEquiv.symm_apply_apply]

def realization : DegreeTwoPairTopTowerRealization L p where
  frame := R.frame
  secondFrame := C.secondFrame R
  topEquiv := MulEquiv.subgroupCongr (C.secondFrame_range R).symm
  module_action_eq := by intro g v; rfl

end DegreeTwoPairTopLiteralTower
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

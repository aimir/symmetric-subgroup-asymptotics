import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopLiteralTower

/-! The second literal pair map carries the original first-top normal
image to the original second-top normal image. This equality binds the
two-frame quotient construction to the first top's existing registry. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopLiteralTower

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {L : DegreeTwoPairTopFiniteInterface t} (C : DegreeTwoPairTopLiteralTower D L)

/-- The actual second pair map, with its range identified with the
retained literal last top. -/
def literalMap : D.top →* L.top :=
  (MulEquiv.subgroupCongr C.range_eq).toMonoidHom.comp C.frame.top.rangeRestrict

theorem literalMap_surjective : Function.Surjective C.literalMap :=
  (MulEquiv.subgroupCongr C.range_eq).surjective.comp
    C.frame.top.rangeRestrict_surjective

def normalImage (M : Subgroup D.top) : Subgroup L.top := M.map C.literalMap

instance normalImage_normal (M : Subgroup D.top) [M.Normal] :
    (C.normalImage M).Normal :=
  Subgroup.Normal.map inferInstance _ C.literalMap_surjective

/-- Both maps refer to the same original normal subgroup, before any
registry state is selected. -/
theorem topNormal_eq_normalImage {p : PreE7PairActionClass s}
    (R : DegreeTwoPairTopRealization D p)
    (N : Subgroup (preE7PairAction s p)) :
    (C.realization R).topNormal N = C.normalImage (R.topNormal N) := by
  unfold DegreeTwoPairTopTowerRealization.topNormal
    DegreeTwoPairTopTowerRealization.outerTopNormal
    DegreeTwoPairTopRealization.topNormal normalImage
  rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.comap_equiv_eq_map_symm']
  simp only [Subgroup.map_map]
  rfl

/-- The old first-top normal-state lookup determines exactly the
denominator of the actual two-frame quotient. -/
theorem normalImage_topNormalState {p : PreE7PairActionClass s}
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    C.normalImage (D.normalRegistry.state (R.topNormalState N)) =
      (C.realization R).topNormal N.1 := by
  rw [R.topNormalState_spec, C.topNormal_eq_normalImage]

end DegreeTwoPairTopLiteralTower
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

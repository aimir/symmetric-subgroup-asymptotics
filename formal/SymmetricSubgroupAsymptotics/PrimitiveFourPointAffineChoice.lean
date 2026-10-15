import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationPublished

/-! At local degree four, the nonaffine side of the published primitive
socle dichotomy is numerically impossible. This extracts the actual affine
profile of an original minimal-block component without an extra profile
existence hypothesis. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

def primitiveFourPointAffineProfile
    (socle : PublishedPrimitiveSocleDichotomyInput)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (hr : Nat.card block.Fibre = 4) :
    PrimitiveAffineProfile block.Component block.Fibre := by
  rcases socle.imprimitive w U hw basePoint block with C | P
  · have hpos : 1 ≤ C.profile.factorCount := C.profile.factorCount_pos
    have hp := Nat.pow_le_pow_right
      (show 0 < C.profile.leastIndex from by
        have := C.profile.leastIndex_five_le
        omega) hpos
    rw [pow_one] at hp
    have hsmall := hp.trans C.profile.primitive_index_lower
    have hfive : 5 ≤ Nat.card block.Fibre := C.profile.leastIndex_five_le.trans hsmall
    omega
  · exact P

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

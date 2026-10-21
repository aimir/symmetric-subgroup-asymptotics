import SymmetricSubgroupAsymptotics.ActualBlockSemisimpleStrictMany

/-! Local semisimple compression with a strict degree reduction and at least two global blocks. Every
normal subgroup, quotient and original block action is retained, while the
local numerical condition is weakened to the exact sufficient margin. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact conclusion of primitive semisimple compression on one local
component of degree `r`. -/
structure LocalSemisimpleStrictCompressionData
    (L : Type) [Group L] (r : ℕ) where
  E : Subgroup L
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  quotientDegree : ℕ
  quotientDegree_pos : 0 < quotientDegree
  quotientAction : (L ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  degree_bound : r ≤ 512
  quotientDegree_gap : quotientDegree + 1 ≤ r

attribute [instance] LocalSemisimpleStrictCompressionData.E_normal

namespace LocalSemisimpleStrictCompressionData

variable {L : Type} [Group L] {r : ℕ}
  (C : LocalSemisimpleStrictCompressionData L r)

/-- The quotient action pulled back to the literal local group. -/
def compressedMap : L →* Equiv.Perm (Fin C.quotientDegree) :=
  C.quotientAction.comp (QuotientGroup.mk' C.E)

/-- Its actual permutation image, retained as the local quotient in the
wreath construction. -/
abbrev localQuotient : Subgroup (Equiv.Perm (Fin C.quotientDegree)) :=
  C.compressedMap.range

/-- The onto map from the literal component to its compressed image. -/
def localMap : L →* C.localQuotient :=
  C.compressedMap.rangeRestrict

/-- Faithfulness of the quotient action identifies the constructed kernel
with the originally supplied normal semisimple subgroup. -/
theorem localMap_ker : C.localMap.ker = C.E := by
  rw [localMap, MonoidHom.ker_rangeRestrict]
  apply le_antisymm
  · intro x hx
    have haction : C.quotientAction ((x : L) : L ⧸ C.E) = 1 :=
      MonoidHom.mem_ker.mp hx
    have hquot : ((x : L) : L ⧸ C.E) = 1 :=
      C.quotientAction_injective (haction.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff (x : L)).mp hquot
  · intro x hx
    apply MonoidHom.mem_ker.mpr
    change C.quotientAction ((x : L) : L ⧸ C.E) = 1
    rw [(QuotientGroup.eq_one_iff (x : L)).mpr hx, map_one]

/-- The supplied chart transports across the proved literal kernel equality. -/
noncomputable def localChart : SemisimpleNormalChart C.localMap.ker := by
  rw [C.localMap_ker]
  exact C.chart

end LocalSemisimpleStrictCompressionData

namespace Non2UnipotentPrefixFiniteMenu

/-- Original-minimal-block data stated in the output form of the primitive
compression theorem. -/
structure PreE7OriginalMinimalBlockLocalStrictManyData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  basePoint : Fin w
  block : OriginalMinimalBlock
    (A := preE7NonPairAction w i) basePoint
  compression : LocalSemisimpleStrictCompressionData block.Component
    (Nat.card block.Fibre)
  blockCount_two_le : 2 ≤ Fintype.card block.Points

namespace PreE7OriginalMinimalBlockLocalStrictManyData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7OriginalMinimalBlockLocalStrictManyData w i)

/-- Convert the natural primitive theorem output to the local-map certificate
consumed by the actual wreath construction. -/
noncomputable def toOriginalMinimalBlockMarginData :
    PreE7OriginalMinimalBlockStrictManyData w i where
  width_lower := C.width_lower
  basePoint := C.basePoint
  block := C.block
  localDegree := C.compression.quotientDegree
  localDegree_pos := C.compression.quotientDegree_pos
  localQuotient := C.compression.localQuotient
  localMap := C.compression.localMap
  localChart := C.compression.localChart
  blockSize_bound := C.compression.degree_bound
  blockCount_two_le := C.blockCount_two_le
  localDegree_gap := C.compression.quotientDegree_gap

/-- Local primitive compression on an actual block gives the complete global
semisimple compression datum. -/
noncomputable def toSemisimpleMarginData :
    PreE7SemisimpleMarginData w i :=
  C.toOriginalMinimalBlockMarginData.toSemisimpleMarginData

end PreE7OriginalMinimalBlockLocalStrictManyData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

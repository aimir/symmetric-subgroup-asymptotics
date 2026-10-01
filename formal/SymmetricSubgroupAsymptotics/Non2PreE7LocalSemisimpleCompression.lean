import SymmetricSubgroupAsymptotics.Non2PreE7ActualBlockCompression

/-!
# Local primitive semisimple compression

The primitive-component theorem naturally produces a normal semisimple
subgroup `E` and a faithful permutation action of the literal quotient
`L/E`.  The block-compression API instead consumes a map from `L` onto its
actual permutation image.  This file constructs that map and proves that its
kernel is exactly the supplied `E`; no kernel identification is left in a
finite certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact conclusion of primitive semisimple compression on one local
component of degree `r`. -/
structure LocalSemisimpleCompressionData
    (L : Type) [Group L] (r : ℕ) where
  E : Subgroup L
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  quotientDegree : ℕ
  quotientDegree_pos : 0 < quotientDegree
  quotientAction : (L ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  quotientDegree_small : 2 * quotientDegree ≤ evenWidth r

attribute [instance] LocalSemisimpleCompressionData.E_normal

namespace LocalSemisimpleCompressionData

variable {L : Type} [Group L] {r : ℕ}
  (C : LocalSemisimpleCompressionData L r)

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

end LocalSemisimpleCompressionData

namespace Non2UnipotentPrefixFiniteMenu

/-- Original-minimal-block data stated in the output form of the primitive
compression theorem. -/
structure PreE7OriginalMinimalBlockLocalCompressionData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  basePoint : Fin w
  block : OriginalMinimalBlock
    (A := preE7NonPairAction w i) basePoint
  compression : LocalSemisimpleCompressionData block.Component
    (Nat.card block.Fibre)

namespace PreE7OriginalMinimalBlockLocalCompressionData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7OriginalMinimalBlockLocalCompressionData w i)

/-- Convert the natural primitive theorem output to the local-map certificate
consumed by the actual wreath construction. -/
noncomputable def toOriginalMinimalBlockCompressionData :
    PreE7OriginalMinimalBlockCompressionData w i where
  width_lower := C.width_lower
  basePoint := C.basePoint
  block := C.block
  localDegree := C.compression.quotientDegree
  localDegree_pos := C.compression.quotientDegree_pos
  localQuotient := C.compression.localQuotient
  localMap := C.compression.localMap
  localChart := C.compression.localChart
  localDegree_small := C.compression.quotientDegree_small

/-- Local primitive compression on an actual block gives the complete global
semisimple compression datum. -/
noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i :=
  C.toOriginalMinimalBlockCompressionData.toSemisimpleCompressionData

end PreE7OriginalMinimalBlockLocalCompressionData

/-- The same primitive compression datum for an action which is already
primitive, corresponding to the one-block case of the manuscript theorem. -/
structure PreE7PrimitiveLocalCompressionData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  compression : LocalSemisimpleCompressionData (preE7NonPairAction w i) w

namespace PreE7PrimitiveLocalCompressionData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7PrimitiveLocalCompressionData w i)

noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i where
  width_lower := C.width_lower
  E := C.compression.E
  E_normal := C.compression.E_normal
  chart := C.compression.chart
  quotientDegree := C.compression.quotientDegree
  quotientAction := C.compression.quotientAction
  quotientAction_injective := C.compression.quotientAction_injective
  quotientDegree_small := C.compression.quotientDegree_small

end PreE7PrimitiveLocalCompressionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

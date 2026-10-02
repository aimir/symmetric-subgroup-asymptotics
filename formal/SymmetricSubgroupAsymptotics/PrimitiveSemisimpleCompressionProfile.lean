import SymmetricSubgroupAsymptotics.Non2PreE7LocalSemisimpleCompression
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleCompressionProfileData

/-!
# Numerical primitive-socle compression profile

For a nonaffine primitive group with socle `S^a`, the manuscript lets
`ell` be the least proper index of `S` and `q = |Out(S)|`.  The structural
group theory supplies a faithful quotient action of degree `a*q` and the
core-free index bound `ell^a ≤ r`.  This file proves the remaining
power propagation: the single inequality `4*q ≤ ell^2` handles every
`a ≥ 2`.  The `a = 1`, `ell ≥ 30` branch uses `2*q ≤ ell`; only the
bounded almost-simple range is left to a finite primitive certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveSemisimpleCompressionProfile

variable {L : Type} [Group L] {r : ℕ}
  (C : PrimitiveSemisimpleCompressionProfile L r)

theorem quotientDegree_pos : 0 < C.factorCount * C.outerOrder :=
  Nat.mul_pos C.factorCount_pos C.outerOrder_pos

theorem quotientDegree_small_of_multiple (ha : 2 ≤ C.factorCount) :
    2 * (C.factorCount * C.outerOrder) ≤ evenWidth r := by
  apply even_le_evenWidth
  · exact ⟨C.factorCount * C.outerOrder, by omega⟩
  · exact (primitiveSocle_degree_le_power ha C.leastIndex_two_le
      C.multiple_factor_base).trans C.primitive_index_lower

theorem quotientDegree_small_of_large_simple
    (ha : C.factorCount = 1) (hell : 30 ≤ C.leastIndex) :
    2 * (C.factorCount * C.outerOrder) ≤ evenWidth r := by
  apply even_le_evenWidth
  · exact ⟨C.factorCount * C.outerOrder, by omega⟩
  · rw [ha, one_mul]
    have hindex : C.leastIndex ≤ r := by
      simpa [ha] using C.primitive_index_lower
    exact (C.large_simple_base hell).trans hindex

noncomputable def toLocalCompressionOfMultiple
    (ha : 2 ≤ C.factorCount) :
    LocalSemisimpleCompressionData L r where
  E := C.E
  E_normal := C.E_normal
  chart := C.chart
  quotientDegree := C.factorCount * C.outerOrder
  quotientDegree_pos := C.quotientDegree_pos
  quotientAction := C.quotientAction
  quotientAction_injective := C.quotientAction_injective
  quotientDegree_small := C.quotientDegree_small_of_multiple ha

noncomputable def toLocalCompressionOfLargeSimple
    (ha : C.factorCount = 1) (hell : 30 ≤ C.leastIndex) :
    LocalSemisimpleCompressionData L r where
  E := C.E
  E_normal := C.E_normal
  chart := C.chart
  quotientDegree := C.factorCount * C.outerOrder
  quotientDegree_pos := C.quotientDegree_pos
  quotientAction := C.quotientAction
  quotientAction_injective := C.quotientAction_injective
  quotientDegree_small := C.quotientDegree_small_of_large_simple ha hell

end PrimitiveSemisimpleCompressionProfile

/-- Exhaustive output shape for primitive compression.  The first two
constructors are the uniform socle argument; `bounded` is reserved for the
classified almost-simple degrees below thirty. -/
inductive PrimitiveSemisimpleCompressionCertificate
    (L : Type) [Group L] (r : ℕ) : Type 1 where
  | multiple (profile : PrimitiveSemisimpleCompressionProfile L r)
      (factorCount_two_le : 2 ≤ profile.factorCount)
  | largeSimple (profile : PrimitiveSemisimpleCompressionProfile L r)
      (factorCount_eq_one : profile.factorCount = 1)
      (leastIndex_thirty_le : 30 ≤ profile.leastIndex)
  | bounded (data : LocalSemisimpleCompressionData L r)

namespace PrimitiveSemisimpleCompressionCertificate

variable {L : Type} [Group L] {r : ℕ}

/-- Every uniform or bounded primitive certificate yields the exact local
compression datum used by T1. -/
noncomputable def toLocalCompression
    (C : PrimitiveSemisimpleCompressionCertificate L r) :
    LocalSemisimpleCompressionData L r :=
  match C with
  | .multiple profile ha => profile.toLocalCompressionOfMultiple ha
  | .largeSimple profile ha hell =>
      profile.toLocalCompressionOfLargeSimple ha hell
  | .bounded data => data

end PrimitiveSemisimpleCompressionCertificate

namespace Non2UnipotentPrefixFiniteMenu

/-- A primitive retained action equipped with the uniform-or-bounded
primitive compression certificate. -/
structure PreE7PrimitiveCompressionCertificateData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  certificate : PrimitiveSemisimpleCompressionCertificate
    (preE7NonPairAction w i) w

namespace PreE7PrimitiveCompressionCertificateData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7PrimitiveCompressionCertificateData w i)

noncomputable def toPrimitiveLocalCompressionData :
    PreE7PrimitiveLocalCompressionData w i where
  width_lower := C.width_lower
  compression := C.certificate.toLocalCompression

noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i :=
  C.toPrimitiveLocalCompressionData.toSemisimpleCompressionData

end PreE7PrimitiveCompressionCertificateData

/-- An actual minimal block whose literal primitive component has the
uniform-or-bounded primitive compression certificate. -/
structure PreE7OriginalMinimalBlockCompressionCertificateData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  basePoint : Fin w
  block : OriginalMinimalBlock
    (A := preE7NonPairAction w i) basePoint
  certificate : PrimitiveSemisimpleCompressionCertificate block.Component
    (Nat.card block.Fibre)

namespace PreE7OriginalMinimalBlockCompressionCertificateData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7OriginalMinimalBlockCompressionCertificateData w i)

noncomputable def toLocalCompressionData :
    PreE7OriginalMinimalBlockLocalCompressionData w i where
  width_lower := C.width_lower
  basePoint := C.basePoint
  block := C.block
  compression := C.certificate.toLocalCompression

noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i :=
  C.toLocalCompressionData.toSemisimpleCompressionData

end PreE7OriginalMinimalBlockCompressionCertificateData

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

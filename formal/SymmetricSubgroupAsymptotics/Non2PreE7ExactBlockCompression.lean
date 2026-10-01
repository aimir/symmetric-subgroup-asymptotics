import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleCompression
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-!
# Exact block compression into the COMP source

This is the faithful-action end of the manuscript's exact block-component
lifting theorem.  The local compressed quotient acts on `u` points and the
literal block top acts on `s` points.  An embedding of the actual quotient
into their permutational wreath product therefore gives a faithful action on
exactly `u * s` points.  The parity inequality is proved for every `r,s`.

The remaining group-theoretic construction has a precise boundary: build the
literal semisimple intersection and the displayed quotient embedding from an
actual exact block component.  No regular replacement of the block top is
used here.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- `evenWidth n` is the largest even natural number at most `n`. -/
theorem even_le_evenWidth {a n : ℕ} (ha : Even a) (han : a ≤ n) :
    a ≤ evenWidth n := by
  obtain ⟨k, rfl⟩ := ha
  unfold evenWidth halfDegree
  omega

/-- Local parity propagates through every number of blocks. -/
theorem evenWidth_mul_block_bound {r s u : ℕ}
    (hlocal : 2 * u ≤ evenWidth r) :
    2 * (u * s) ≤ evenWidth (r * s) := by
  apply even_le_evenWidth
  · exact ⟨u * s, by omega⟩
  · calc
      2 * (u * s) = (2 * u) * s := by simp [Nat.mul_assoc]
      _ ≤ evenWidth r * s := Nat.mul_le_mul_right s hlocal
      _ ≤ r * s := Nat.mul_le_mul_right s (evenWidth_le r)

namespace Non2UnipotentPrefixFiniteMenu

/-- The exact data produced by block lifting after the semisimple intersection
and quotient embedding have been constructed.  The base and top are retained
as literal permutation groups in their supplied actions. -/
structure PreE7ExactBlockCompressionData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  blockSize : ℕ
  blockCount : ℕ
  blockCount_pos : 0 < blockCount
  localDegree : ℕ
  localDegree_pos : 0 < localDegree
  width_eq : w = blockSize * blockCount
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  localQuotient : Subgroup (Equiv.Perm (Fin localDegree))
  blockTop : Subgroup (Equiv.Perm (Fin blockCount))
  quotientEmbedding :
    (preE7NonPairAction w i ⧸ E) →*
      PermutationalWreathProduct localQuotient blockTop (Fin blockCount)
  quotientEmbedding_injective : Function.Injective quotientEmbedding
  localDegree_small : 2 * localDegree ≤ evenWidth blockSize

attribute [instance] PreE7ExactBlockCompressionData.E_normal

namespace PreE7ExactBlockCompressionData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7ExactBlockCompressionData w i)

def quotientDegree : ℕ := D.localDegree * D.blockCount

/-- The faithful quotient action retains both the local action and the
actual block-top action. -/
def quotientAction :
    (preE7NonPairAction w i ⧸ D.E) →*
      Equiv.Perm (Fin D.quotientDegree) := by
  letI : Nonempty (Fin D.localDegree) := Fin.pos_iff_nonempty.mp D.localDegree_pos
  letI : Nonempty (Fin D.blockCount) := Fin.pos_iff_nonempty.mp D.blockCount_pos
  exact
    (PermutationalWreathProduct.toFinPerm
      (u := D.localDegree) (s := D.blockCount)
      D.localQuotient D.blockTop).comp D.quotientEmbedding

theorem quotientAction_injective : Function.Injective D.quotientAction := by
  letI : Nonempty (Fin D.localDegree) := Fin.pos_iff_nonempty.mp D.localDegree_pos
  letI : Nonempty (Fin D.blockCount) := Fin.pos_iff_nonempty.mp D.blockCount_pos
  exact
    (PermutationalWreathProduct.toFinPerm_injective
      (u := D.localDegree) (s := D.blockCount)
      D.localQuotient D.blockTop).comp D.quotientEmbedding_injective

theorem quotientDegree_small :
    2 * D.quotientDegree ≤ evenWidth w := by
  unfold quotientDegree
  calc
    2 * (D.localDegree * D.blockCount) ≤
        evenWidth (D.blockSize * D.blockCount) :=
      evenWidth_mul_block_bound D.localDegree_small
    _ = evenWidth w := congrArg evenWidth D.width_eq.symm

/-- Exact block compression supplies the numerical COMP structure without
changing the physical action or its normalizer. -/
noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i where
  width_lower := D.width_lower
  E := D.E
  E_normal := D.E_normal
  chart := D.chart
  quotientDegree := D.quotientDegree
  quotientAction := D.quotientAction
  quotientAction_injective := D.quotientAction_injective
  quotientDegree_small := D.quotientDegree_small

end PreE7ExactBlockCompressionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

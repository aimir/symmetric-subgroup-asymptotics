import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource

/-!
# Raw complete-quotient envelopes from the small additive template

The fixed-degree owners are usually consumed after an orbit predicate has
been imposed.  A later affine layer instead needs the complete quotient
moment of the literal target itself.  The same per-axis certificates prove
that stronger pre-padding statement: sum their comparator and tail
coefficients before summing over the complementary source.

This is a theorem about an already constructed `PreE7SmallAdditiveData`;
it introduces no catalogue or structural input.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

attribute [-instance] originalNormalFintype

namespace PreE7SmallAdditiveData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SmallAdditiveData w i)

/-- Total comparator multiplicity on the literal normal menu. -/
def rawMainCoefficient : ℝ :=
  ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    (D.axis N).mainCoefficient

/-- Total additive-tail multiplicity on the literal normal menu. -/
def rawTailCoefficient : ℝ :=
  ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    (D.axis N).tailCoefficient

theorem rawMainCoefficient_nonneg : 0 ≤ D.rawMainCoefficient := by
  unfold rawMainCoefficient
  exact Finset.sum_nonneg (fun N _ => (D.axis N).mainCoefficient_nonneg)

theorem rawTailCoefficient_nonneg : 0 ≤ D.rawTailCoefficient := by
  unfold rawTailCoefficient
  exact Finset.sum_nonneg (fun N _ => (D.axis N).tailCoefficient_nonneg)

/-- The complete quotient weight of the literal action, before any physical
pointing, is bounded by the same compressed comparator and additive tail. -/
theorem completeQuotientWeight_le_rawEnvelope {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := preE7NonPairAction w i) J ≤
      D.rawMainCoefficient * completeQuotientWeight (R := D.R) J +
        D.rawTailCoefficient * (2 : ℝ) ^ (D.tailSlope * b) := by
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
        (Nat.card
          (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) : ℝ)) ≤
        ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
          ((D.axis N).mainCoefficient *
              completeQuotientWeight (R := D.R) J +
            (D.axis N).tailCoefficient *
              (2 : ℝ) ^ (D.tailSlope * b)) := by
      apply Finset.sum_le_sum
      intro N _
      simpa only [zero_mul, Real.rpow_zero, mul_one] using
        ((D.axis N).envelope J)
    _ = D.rawMainCoefficient * completeQuotientWeight (R := D.R) J +
        D.rawTailCoefficient * (2 : ℝ) ^ (D.tailSlope * b) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      rfl

/-- Sum the literal complete-quotient estimate over all complementary
sources.  No hot exceptional term is created by this conversion. -/
noncomputable def quotientSummedEnvelope :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction w i) where
  R := D.R
  mainCoefficient := D.rawMainCoefficient
  coldCoefficient := fun _ => D.rawTailCoefficient
  eta := 0
  theta := D.tailSlope
  mainCoefficient_nonneg := D.rawMainCoefficient_nonneg
  coldCoefficient_nonneg := fun _ => D.rawTailCoefficient_nonneg
  exceptionalRaw := fun _ => 0
  exceptionalRaw_nonneg := fun _ => le_rfl
  summed := fun b => by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun (J : Subgroup (Equiv.Perm (Fin b))) _ =>
        D.completeQuotientWeight_le_rawEnvelope J)
    simpa only [zero_mul, Real.rpow_zero, mul_one, add_zero] using h

end PreE7SmallAdditiveData
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

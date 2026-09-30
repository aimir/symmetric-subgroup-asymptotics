import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2RankTailNumerics

/-!
# SNS2 in the mixed physical catalogue

The cold weighted term is a genuine continuation row; the hot weighted term
is already source-summed and is retained as an exceptional scalar.  This file
installs that exact local decomposition without yet applying the all-width
entropy aggregation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

def preE7Sns2ExceptionalDelta : ℝ := preE7CharacterRho * 5 / 2

def preE7Sns2ExceptionalCutoff : ℝ :=
  (1 : ℝ) / 8 + preE7Sns2ExceptionalDelta / 2

/-- The hot, already source-summed half of one SNS2 action row. -/
def preE7Sns2ExceptionalScalar {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Sns2RankTailCertificate w i) (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
    (C.normalCount * C.outerFactor b *
      ((2 : ℝ) ^
          (-(((sns2RankTailTilt b C.quotientRank : ℝ) -
              C.quotientRank) * (51 / 200) * b)) *
        (subgroupCount
          (b + 2 * sns2RankTailTilt b C.quotientRank) : ℝ)))

/-- The exact local SNS2 row.  The dummy main-row parameters multiply zero;
the cold term retains slope `51ℓ/200`, and the hot term remains correlated in
`preE7Sns2ExceptionalScalar`. -/
noncomputable def PreE7EarlierLocalCertificate.ofSns2
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Sns2RankTailCertificate w i) :
    PreE7EarlierLocalCertificate .sns2 w i where
  D := fun _ => 0
  T := fun b => C.normalCount * C.outerFactor b
  X := preE7Sns2ExceptionalScalar C
  v := 1
  eta := 0
  delta := preE7Sns2ExceptionalDelta
  cutoff := preE7Sns2ExceptionalCutoff
  alpha := preE7Sns2ExceptionalCutoff
  theta := (C.quotientRank : ℝ) * (51 / 200)
  alpha_eq := by simp
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun b =>
    mul_nonneg C.normalCount_nonneg (C.outerFactor_nonneg b)
  local_bound := by
    intro b P hP _hPbroad
    have h := C.physical_normalized_bound b P hP
    have hcold := growingQuotient_cold_identity (subgroupCount b : ℝ)
      b w (C.normalCount * C.outerFactor b)
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
      ((C.quotientRank : ℝ) * (51 / 200)) 0
    rw [show (C.quotientRank : ℝ) * (51 / 200) + 0 =
        (C.quotientRank : ℝ) * (51 / 200) by ring] at hcold
    simp only [growingQuotientThreshold, zero_mul, Real.rpow_zero,
      mul_one] at hcold
    have hhotzero : growingQuotientHotKernel
        (fun n => (subgroupCount n : ℝ)) b w 1 0
        (Nat.card (Subgroup.normalizer
          (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
        0 preE7Sns2ExceptionalDelta preE7Sns2ExceptionalCutoff = 0 := by
      simp [growingQuotientHotKernel]
    have hcoldzero : fusionWidthColdKernel b w 0
        (Nat.card (Subgroup.normalizer
          (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
        preE7Sns2ExceptionalCutoff = 0 := by
      simp [fusionWidthColdKernel]
    simp only [preE7Sns2ExceptionalScalar, hhotzero, hcoldzero, zero_add]
    rw [ordinarySubgroupRatio, ← hcold]
    calc
      _ ≤ growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
          (C.normalCount * C.outerFactor b *
                (2 : ℝ) ^
                  ((C.quotientRank : ℝ) * ((51 / 200) * b)) *
                (subgroupCount b : ℝ) +
            C.normalCount * C.outerFactor b *
              ((2 : ℝ) ^
                  (-(((sns2RankTailTilt b C.quotientRank : ℝ) -
                      C.quotientRank) * (51 / 200) * b)) *
                (subgroupCount
                  (b + 2 * sns2RankTailTilt b C.quotientRank) : ℝ))) := h
      _ = _ := by ring_nf

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

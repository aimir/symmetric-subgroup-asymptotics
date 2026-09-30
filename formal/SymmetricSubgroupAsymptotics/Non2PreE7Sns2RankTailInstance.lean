import SymmetricSubgroupAsymptotics.Non2PreE7Sns2RankTailSource

/-!
# SNS2: the summed-source weighted rank-tail certificate

The SNS2 fibre keeps its weight `2^(l d₂(J))`.  With the tilt
`q = max(l, ⌈b/100⌉)`, so that `l ≤ q` holds by construction, the weighted
rank tail at `a = 51/200` bounds the hot sources:

`∑_{J ≤ S_b} Z_J(U) ≤ ν(R) Ψ_E(b) (2^(51 l b/200) s_b
    + 2^(-(q-l) 51 b/200) s_{b+2q})`.

In the first regime `l ≤ ⌈b/100⌉` the tilt is `⌈b/100⌉` and the completed
square keeps the deficit `b²/40000`.  In the second regime the tilt is `l`
and `b < 100 l`, so the removed width `w ≥ 3l` is a fixed fraction of the
ambient degree.  The cold slope `51 l/200` meets the cold gap at every width
`w ≥ 5` with `3l ≤ w`, at `ρ = 1/8192`.

The certificate keeps the source weight and the hot/cold split until after
the sum over sources; it is meant for the summed-source physical transfer.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The SNS2 tilt `q = max(l, ⌈b/100⌉)`. -/
def sns2RankTailTilt (b l : ℕ) : ℕ := max l (rankTail51Tilt b)

theorem sns2_weight_le_tilt (b l : ℕ) : l ≤ sns2RankTailTilt b l :=
  le_max_left _ _

/-- First regime: the weighted square completion at `a = 51/200`. -/
theorem sns2RankTail_squareCompletion (b l : ℕ) (hl : l ≤ rankTail51Tilt b) :
    ((b : ℝ) + 2 * sns2RankTailTilt b l) ^ 2 / 16 -
        ((sns2RankTailTilt b l : ℝ) - l) * (51 / 200) * b ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + (l : ℝ) * (51 / 200) * b +
        1 / 4 := by
  have hq : sns2RankTailTilt b l = rankTail51Tilt b := max_eq_right hl
  rw [hq]
  exact rankTail51_squareCompletion b l

/-- Second regime: the tilt is the weight itself and `b < 100 l`. -/
theorem sns2RankTail_secondRegime (b l : ℕ) (hl : rankTail51Tilt b < l) :
    sns2RankTailTilt b l = l ∧ (b : ℝ) < 100 * l := by
  refine ⟨max_eq_left hl.le, ?_⟩
  have h1 := (rankTail51Tilt_bounds b).1
  have h2 : (rankTail51Tilt b : ℝ) < l := by exact_mod_cast hl
  linarith

/-- The cold slope `51 l / 200` meets the cold gap at `ρ = 1/8192`. -/
theorem sns2RankTail_coldGap {w l : ℕ} (hw : 5 ≤ w) (hl : 3 * l ≤ w) :
    (l : ℝ) * (51 / 200) ≤
      (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  have hhalf : (w : ℝ) ≤ 2 * halfDegree w + 1 := by
    have : w ≤ 2 * halfDegree w + 1 := by
      unfold halfDegree
      omega
    exact_mod_cast this
  have hl' : 3 * (l : ℝ) ≤ w := by exact_mod_cast hl
  have hw' : (5 : ℝ) ≤ w := by exact_mod_cast hw
  unfold preE7CharacterRho
  linarith

namespace PreE7Sns2ActionCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (C : PreE7Sns2ActionCertificate U)

/-- The summed complete source: the cold bound on cold sources and the
weighted fibre on hot sources, summed by the weighted rank tail with the
proved `l ≤ q`. -/
theorem summedSource_le (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum U P J) ≤
      C.quotientNormalCount * C.outerFactor b *
          (2 : ℝ) ^ ((C.quotientRank : ℝ) * ((51 / 200) * b)) *
          (subgroupCount b : ℝ) +
        C.quotientNormalCount * C.outerFactor b *
          ((2 : ℝ) ^ (-(((sns2RankTailTilt b C.quotientRank : ℝ) -
              C.quotientRank) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * sns2RankTailTilt b C.quotientRank) : ℝ)) := by
  set q := sns2RankTailTilt b C.quotientRank
  set l := C.quotientRank
  set K : ℝ := C.quotientNormalCount * C.outerFactor b
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (C.outerFactor_nonneg b)
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := BinaryRankHot (51 / 200)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  refine (add_comm _ _).le.trans (add_le_add ?_ ?_)
  · set K₁ : ℝ := K * (2 : ℝ) ^ ((l : ℝ) * ((51 / 200) * b))
    have hK₁ : 0 ≤ K₁ := mul_nonneg hK (by positivity)
    calc (∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
          fusionCompleteSourceSum U P J)
        ≤ ∑ J ∈ Finset.univ.filter (fun J => ¬ hot J), K₁ := by
          apply Finset.sum_le_sum
          intro J hJ
          exact C.completeSource_cold P J (Finset.mem_filter.mp hJ).2
      _ = K₁ * ((Finset.univ.filter (fun J => ¬ hot J)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ K₁ * (subgroupCount b : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hK₁
          have hle := Finset.card_filter_le
            (Finset.univ : Finset (Subgroup (Equiv.Perm (Fin b)))) (fun J => ¬ hot J)
          rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
          exact_mod_cast hle
  · have hweight := binaryRankWeightedHotSum_le (51 / 200) b q l
      (sns2_weight_le_tilt b l)
    set T : ℝ := ∑ J ∈ Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot (51 / 200) J),
      (2 : ℝ) ^ ((l : ℝ) * binaryCharacterRank J)
    have hT : T ≤ (2 : ℝ) ^ (-(((q : ℝ) - l) * (51 / 200) * b)) *
        (subgroupCount (b + 2 * q) : ℝ) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (((q : ℝ) - l) * (51 / 200) * b) := by
        positivity
      rw [Real.rpow_neg (by norm_num), ← div_eq_inv_mul, le_div_iff₀ hpos,
        mul_comm]
      exact hweight
    calc (∑ J ∈ Finset.univ.filter hot, fusionCompleteSourceSum U P J)
        ≤ ∑ J ∈ Finset.univ.filter hot,
            K * (2 : ℝ) ^ ((l : ℝ) * binaryCharacterRank J) :=
          Finset.sum_le_sum (fun J _ => C.completeSource_weighted P J)
      _ = K * T := by rw [Finset.mul_sum]
      _ ≤ K * ((2 : ℝ) ^ (-(((q : ℝ) - l) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * q) : ℝ)) :=
          mul_le_mul_of_nonneg_left hT hK

end PreE7Sns2ActionCertificate

/-! ## The family-specific certificate and its dispatcher -/

/-- The SNS2 weighted rank-tail certificate on one retained action class.  It
keeps the per-source weighted fibre `2^(l d₂(J))`, the cold envelope, their
sum over all complementary sources with the proved tilt `l ≤ q`, and the
numerical facts at `ρ = 1/8192`. -/
structure PreE7Sns2RankTailCertificate (w : ℕ) (i : PreE7NonPairActionClass w) :
    Type where
  quotientRank : ℕ
  normalCount : ℝ
  outerFactor : ℕ → ℝ
  normalCount_nonneg : 0 ≤ normalCount
  outerFactor_nonneg : ∀ b, 0 ≤ outerFactor b
  width_lower : 5 ≤ w
  quotientRank_le : 3 * quotientRank ≤ w
  weighted : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
      (J : Subgroup (Equiv.Perm (Fin b))),
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      normalCount * outerFactor b *
        (2 : ℝ) ^ ((quotientRank : ℝ) * binaryCharacterRank J)
  cold : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
      (J : Subgroup (Equiv.Perm (Fin b))), ¬ BinaryRankHot (51 / 200) J →
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      normalCount * outerFactor b *
        (2 : ℝ) ^ ((quotientRank : ℝ) * ((51 / 200) * b))
  summed : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w i) P J) ≤
      normalCount * outerFactor b *
          (2 : ℝ) ^ ((quotientRank : ℝ) * ((51 / 200) * b)) *
          (subgroupCount b : ℝ) +
        normalCount * outerFactor b *
          ((2 : ℝ) ^ (-(((sns2RankTailTilt b quotientRank : ℝ) -
              quotientRank) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * sns2RankTailTilt b quotientRank) : ℝ))
  cold_gap : (quotientRank : ℝ) * (51 / 200) ≤
    (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4
  square_completion : ∀ b : ℕ, quotientRank ≤ rankTail51Tilt b →
    ((b : ℝ) + 2 * sns2RankTailTilt b quotientRank) ^ 2 / 16 -
        ((sns2RankTailTilt b quotientRank : ℝ) - quotientRank) * (51 / 200) * b ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 +
        (quotientRank : ℝ) * (51 / 200) * b + 1 / 4
  second_regime : ∀ b : ℕ, rankTail51Tilt b < quotientRank →
    sns2RankTailTilt b quotientRank = quotientRank ∧
      (b : ℝ) < 100 * quotientRank

/-- The SNS2 source on one retained action class.  The family predicate is
existence of this datum. -/
abbrev PreE7Sns2SourceData (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  PreE7Sns2ActionCertificate (preE7NonPairAction w i)

/-- The SNS2 rank-tail certificate of one certified action. -/
def preE7_sns2RankTailCertificate {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7Sns2SourceData w i) : PreE7Sns2RankTailCertificate w i where
  quotientRank := S.quotientRank
  normalCount := S.quotientNormalCount
  outerFactor := S.outerFactor
  normalCount_nonneg := Nat.cast_nonneg _
  outerFactor_nonneg := S.outerFactor_nonneg
  width_lower := S.width_lower
  quotientRank_le := S.quotient_small
  weighted _ P J := S.completeSource_weighted P J
  cold _ P J hJ := S.completeSource_cold P J hJ
  summed b P := S.summedSource_le b P
  cold_gap := sns2RankTail_coldGap S.width_lower S.quotient_small
  square_completion b hb := sns2RankTail_squareCompletion b _ hb
  second_regime b hb := sns2RankTail_secondRegime b _ hb

/-- The family dispatcher for the SNS2 branch of the binary rank-tail
moment. -/
def preE7_rankTailCertificate_sns2
    (family : PreE7NoPairNoC3EarlierOwnerFamily) (_hfamily : family = .sns2)
    (w : ℕ) (i : PreE7NonPairActionClass w) (hsource : PreE7Sns2SourceData w i) :
    PreE7Sns2RankTailCertificate w i :=
  preE7_sns2RankTailCertificate hsource

theorem preE7_sns2_specialMoment :
    PreE7NoPairNoC3EarlierOwnerFamily.sns2.specialMoment = .binaryRankTail :=
  rfl

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

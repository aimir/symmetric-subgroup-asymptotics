import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailSource

/-!
# Y1: the summed-source rank-tail certificate

The Y1 source is hot when some index-three kernel `F` of the complete source
has `d₂(F) > 51b/200`.  Hot sources are counted through a hot kernel and one
further permutation, and hot kernels by the untilted rank tail at
`a = 51/200` and tilt `r = ⌈b/100⌉`:

`∑_{J ≤ S_b} Z_J(U) ≤ C_U (1+b) 2^(153b/200) s_b
    + ν(U) (b!)^16 · b! · 2^(-51 r b / 200) s_{b+2r}`.

The square completion `(b+2r)²/16 - 51rb/200 ≤ b²/16 - b²/40000 + 1/4`
leaves a quadratic deficit for the factors `(b!)^17`.  The cold slope
`153/200` meets the width-eight gap at `ρ = 1/8192`.

The certificate keeps the hot/cold split until after the sum over sources;
it is meant for the summed-source physical transfer.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The square completion for the Y1 kernel tail (`ℓ = 0`). -/
theorem y1RankTail_squareCompletion (b : ℕ) :
    ((b : ℝ) + 2 * rankTail51Tilt b) ^ 2 / 16 -
        (rankTail51Tilt b : ℝ) * (51 / 200) * b ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + 1 / 4 := by
  simpa using rankTail51_squareCompletion b 0

/-- The cold slope `153/200` meets the width-eight cold gap at the global
`ρ = 1/8192`. -/
theorem y1RankTail_coldGap :
    (153 / 200 : ℝ) ≤
      (halfDegree 8 : ℝ) / 4 - preE7CharacterRho * (8 : ℕ) / 4 := by
  unfold preE7CharacterRho halfDegree
  norm_num

namespace PreE7Y1ActionCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (C : PreE7Y1ActionCertificate U)

/-- The summed complete source, with the cold envelope on cold sources and
the full fibre only on hot sources, counted through their hot index-three
kernels. -/
theorem summedSource_le (lit : PreE7CharacterLiterature) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum U P J) ≤
      C.constant * (1 + b) * (2 : ℝ) ^ ((153 / 200 : ℝ) * b) *
          (subgroupCount b : ℝ) +
        (PreE7B6ActionCertificate.normalCount U : ℝ) *
            ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Nat.factorial b : ℝ) *
            ((2 : ℝ) ^ (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
  set K₁ : ℝ := C.constant * (1 + b) * (2 : ℝ) ^ ((153 / 200 : ℝ) * b)
  set K₂ : ℝ := (PreE7B6ActionCertificate.normalCount U : ℝ) *
    ((Nat.factorial b : ℕ) : ℝ) ^ 16
  have hK₁ : 0 ≤ K₁ := by
    have := C.constant_nonneg
    positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := IndexThreeRankHot (51 / 200)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  refine (add_comm _ _).le.trans (add_le_add ?_ ?_)
  · calc (∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
          fusionCompleteSourceSum U P J)
        ≤ ∑ J ∈ Finset.univ.filter (fun J => ¬ hot J), K₁ := by
          apply Finset.sum_le_sum
          intro J hJ
          exact C.completeSource_cold lit P J (Finset.mem_filter.mp hJ).2
      _ = K₁ * ((Finset.univ.filter (fun J => ¬ hot J)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ K₁ * (subgroupCount b : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hK₁
          have hle := Finset.card_filter_le
            (Finset.univ : Finset (Subgroup (Equiv.Perm (Fin b)))) (fun J => ¬ hot J)
          rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
          exact_mod_cast hle
  · calc (∑ J ∈ Finset.univ.filter hot, fusionCompleteSourceSum U P J)
        ≤ ∑ J ∈ Finset.univ.filter hot, K₂ :=
          Finset.sum_le_sum (fun J _ => C.completeSource_full P J)
      _ = K₂ * ((Finset.univ.filter hot).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ K₂ * ((Nat.factorial b : ℝ) *
            ((2 : ℝ) ^ (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hK₂
          exact (indexThreeRankHot_card_le (51 / 200) b).trans
            (mul_le_mul_of_nonneg_left (binaryRankHot51_card_le b)
              (Nat.cast_nonneg _))

end PreE7Y1ActionCertificate

/-! ## The family-specific certificate and its dispatcher -/

/-- The width-eight repeated-`A₄` rank-tail certificate on one retained
action class.  It keeps the per-source cold and full envelopes and their sum
over all complementary sources with the hot sources counted through their
hot index-three kernels, together with the two numerical facts at
`ρ = 1/8192`. -/
structure PreE7Y1RankTailCertificate (w : ℕ) (i : PreE7NonPairActionClass w) :
    Type where
  coldConstant : ℝ
  normalCount : ℝ
  coldConstant_nonneg : 0 ≤ coldConstant
  normalCount_nonneg : 0 ≤ normalCount
  width_eq : w = 8
  cold : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
      (J : Subgroup (Equiv.Perm (Fin b))), ¬ IndexThreeRankHot (51 / 200) J →
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      coldConstant * (1 + b) * (2 : ℝ) ^ ((153 / 200 : ℝ) * b)
  full : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
      (J : Subgroup (Equiv.Perm (Fin b))),
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16
  summed : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w i) P J) ≤
      coldConstant * (1 + b) * (2 : ℝ) ^ ((153 / 200 : ℝ) * b) *
          (subgroupCount b : ℝ) +
        normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Nat.factorial b : ℝ) *
            ((2 : ℝ) ^ (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ)))
  cold_gap : (153 / 200 : ℝ) ≤
    (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4
  square_completion : ∀ b : ℕ,
    ((b : ℝ) + 2 * rankTail51Tilt b) ^ 2 / 16 -
        (rankTail51Tilt b : ℝ) * (51 / 200) * b ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + 1 / 4

/-- The Y1 source on one retained action class.  The family predicate is
existence of this datum. -/
abbrev PreE7Y1SourceData (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  PreE7Y1ActionCertificate (preE7NonPairAction w i)

/-- The Y1 rank-tail certificate of one certified action. -/
def preE7_y1RankTailCertificate (lit : PreE7CharacterLiterature) {w : ℕ}
    {i : PreE7NonPairActionClass w} (S : PreE7Y1SourceData w i) :
    PreE7Y1RankTailCertificate w i where
  coldConstant := S.constant
  normalCount := PreE7B6ActionCertificate.normalCount (preE7NonPairAction w i)
  coldConstant_nonneg := S.constant_nonneg
  normalCount_nonneg := Nat.cast_nonneg _
  width_eq := S.width_eq
  cold b P J hJ := S.completeSource_cold lit P J hJ
  full b P J := S.completeSource_full P J
  summed b P := S.summedSource_le lit b P
  cold_gap := by
    have hw := S.width_eq
    subst hw
    exact y1RankTail_coldGap
  square_completion := y1RankTail_squareCompletion

/-- The family dispatcher for the Y1 branch of the binary rank-tail
moment. -/
def preE7_rankTailCertificate_y1
    (family : PreE7NoPairNoC3EarlierOwnerFamily) (_hfamily : family = .y1)
    (w : ℕ) (i : PreE7NonPairActionClass w) (hsource : PreE7Y1SourceData w i)
    (lit : PreE7CharacterLiterature) : PreE7Y1RankTailCertificate w i :=
  preE7_y1RankTailCertificate lit hsource

theorem preE7_y1_specialMoment :
    PreE7NoPairNoC3EarlierOwnerFamily.y1.specialMoment = .binaryRankTail :=
  rfl

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

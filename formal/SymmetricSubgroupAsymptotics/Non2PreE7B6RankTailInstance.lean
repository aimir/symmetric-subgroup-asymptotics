import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource
import SymmetricSubgroupAsymptotics.BinaryRankWeightedTail

/-!
# B6: the summed-source rank-tail certificate

The B6 envelope depends on the temperature of the complete source `J`:

* cold (`d₂(J) ≤ 13b/50`): `Z_J(U) ≤ C_U (1+b) 2^(4b/3)`;
* every source: `Z_J(U) ≤ ν(U) (b!)^16`.

The generic additive-tail interface forgets the temperature, so it cannot
carry the second bound only on the hot set.  This file therefore sums the
complete sources with the hot/cold split still visible.  The untilted
rank tail at `a = 13/50` counts the hot sources:

`∑_{J ≤ S_b} Z_J(U) ≤ C_U (1+b) 2^(4b/3) s_b
    + ν(U) (b!)^16 2^(-13 q b / 50) s_{b+2q}`,

for every `q`.  At `q = ⌈b/50⌉ = (b+49)/50` the exponent obeys the square
completion `(b+2q)²/16 - 13qb/50 ≤ b²/16 - b²/10000 + 1/4`.  That quadratic
deficit is what absorbs the factor `(b!)^16`.

The resulting `PreE7B6RankTailCertificate` is family-specific.  It is
meant to be consumed by the special-moment integration layer before the
source rank is forgotten.  No census, literature input beyond the character
bundle, or tail hypothesis is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-! ## The B6 threshold and its square completion -/

/-- The rank-tail tilt `q = ⌈b/50⌉`. -/
def b6RankTailExponent (b : ℕ) : ℕ := (b + 49) / 50

/-- The B6 cold test is the complement of the rank-tail hot set at
`a = 13/50`. -/
theorem preE7B6Cold_iff_not_hot {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    PreE7B6Cold J ↔ ¬ BinaryRankHot (13 / 50) J := by
  unfold PreE7B6Cold BinaryRankHot
  rw [not_lt]
  constructor <;> intro h <;> linarith

/-- The exact square completion at `q = ⌈b/50⌉`. -/
theorem b6RankTail_squareCompletion (b : ℕ) :
    ((b : ℝ) + 2 * b6RankTailExponent b) ^ 2 / 16 -
        13 * (b6RankTailExponent b : ℝ) * b / 50 ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 10000 + 1 / 4 := by
  have h1 : b ≤ 50 * b6RankTailExponent b := by
    unfold b6RankTailExponent
    omega
  have h2 : 50 * b6RankTailExponent b ≤ b + 49 := by
    unfold b6RankTailExponent
    omega
  have h1' : (b : ℝ) ≤ 50 * (b6RankTailExponent b : ℝ) := by exact_mod_cast h1
  have h2' : 50 * (b6RankTailExponent b : ℝ) ≤ b + 49 := by exact_mod_cast h2
  set q : ℝ := (b6RankTailExponent b : ℝ)
  have hd : 0 ≤ 50 * q - b := by linarith
  have hd' : 50 * q - b ≤ 49 := by linarith
  have hsq : (50 * q - b) * (50 * q - b) ≤ 49 * 49 :=
    mul_le_mul hd' hd' hd (by norm_num)
  nlinarith [hsq]

/-- The cold slope `4/3` meets the width-twelve cold gap at the global
`ρ = 1/8192`. -/
theorem b6RankTail_coldGap :
    (4 / 3 : ℝ) ≤ (halfDegree 12 : ℝ) / 4 - preE7CharacterRho * (12 : ℕ) / 4 := by
  unfold preE7CharacterRho halfDegree
  norm_num

/-! ## Summing the complete sources with the split visible -/

namespace PreE7B6ActionCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (C : PreE7B6ActionCertificate U)

/-- The summed complete source, with the cold envelope paid on the cold
sources and the full fibre paid only on the hot sources, counted by the
untilted rank tail. -/
theorem summedSource_le (lit : PreE7CharacterLiterature) (b q : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum U P J) ≤
      C.constant * (1 + b) * (2 : ℝ) ^ ((4 / 3 : ℝ) * b) *
          (subgroupCount b : ℝ) +
        (normalCount U : ℝ) * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
            (subgroupCount (b + 2 * q) : ℝ)) := by
  set K₁ : ℝ := C.constant * (1 + b) * (2 : ℝ) ^ ((4 / 3 : ℝ) * b)
  set K₂ : ℝ := (normalCount U : ℝ) * ((Nat.factorial b : ℕ) : ℝ) ^ 16
  have hK₁ : 0 ≤ K₁ := by
    have := C.constant_nonneg
    positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := BinaryRankHot (13 / 50)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  refine (add_comm _ _).le.trans (add_le_add ?_ ?_)
  · calc (∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
          fusionCompleteSourceSum U P J)
        ≤ ∑ J ∈ Finset.univ.filter (fun J => ¬ hot J), K₁ := by
          apply Finset.sum_le_sum
          intro J hJ
          exact C.completeSource_cold lit P J
            ((preE7B6Cold_iff_not_hot J).mpr (Finset.mem_filter.mp hJ).2)
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
      _ ≤ K₂ * ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
            (subgroupCount (b + 2 * q) : ℝ)) :=
          mul_le_mul_of_nonneg_left (binaryRankHot_card_le (13 / 50) b q) hK₂

end PreE7B6ActionCertificate

/-! ## The family-specific certificate and its dispatcher -/

/-- The B6 summed-source rank-tail certificate on one retained action
class.  It keeps the per-source cold and full envelopes and their sum over
all complementary sources with the hot set counted by the rank tail at the
tilt `q = ⌈b/50⌉`, together with the two numerical facts at `ρ = 1/8192`. -/
structure PreE7B6RankTailCertificate (w : ℕ) (i : PreE7NonPairActionClass w) :
    Type where
  coldConstant : ℝ
  normalCount : ℝ
  coldConstant_nonneg : 0 ≤ coldConstant
  normalCount_nonneg : 0 ≤ normalCount
  width_eq : w = 12
  cold : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
      (J : Subgroup (Equiv.Perm (Fin b))), ¬ BinaryRankHot (13 / 50) J →
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      coldConstant * (1 + b) * (2 : ℝ) ^ ((4 / 3 : ℝ) * b)
  full : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
      (J : Subgroup (Equiv.Perm (Fin b))),
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16
  summed : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w i) P J) ≤
      coldConstant * (1 + b) * (2 : ℝ) ^ ((4 / 3 : ℝ) * b) *
          (subgroupCount b : ℝ) +
        normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((2 : ℝ) ^ (-((b6RankTailExponent b : ℝ) * (13 / 50) * b)) *
            (subgroupCount (b + 2 * b6RankTailExponent b) : ℝ))
  cold_gap : (4 / 3 : ℝ) ≤
    (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4
  square_completion : ∀ b : ℕ,
    ((b : ℝ) + 2 * b6RankTailExponent b) ^ 2 / 16 -
        13 * (b6RankTailExponent b : ℝ) * b / 50 ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 10000 + 1 / 4

/-- The B6 source on one retained action class: a literal six-pair-block
certificate for its original action.  The family predicate is existence of
this datum. -/
abbrev PreE7B6SourceData (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  PreE7B6ActionCertificate (preE7NonPairAction w i)

/-- The B6 rank-tail certificate of one certified six-pair-block action. -/
def preE7_b6RankTailCertificate (lit : PreE7CharacterLiterature) {w : ℕ}
    {i : PreE7NonPairActionClass w} (S : PreE7B6SourceData w i) :
    PreE7B6RankTailCertificate w i where
  coldConstant := S.constant
  normalCount := PreE7B6ActionCertificate.normalCount (preE7NonPairAction w i)
  coldConstant_nonneg := S.constant_nonneg
  normalCount_nonneg := Nat.cast_nonneg _
  width_eq := S.width_eq
  cold b P J hJ :=
    S.completeSource_cold lit P J ((preE7B6Cold_iff_not_hot J).mpr hJ)
  full b P J := S.completeSource_full P J
  summed b P := S.summedSource_le lit b (b6RankTailExponent b) P
  cold_gap := by
    have hw := S.width_eq
    subst hw
    exact b6RankTail_coldGap
  square_completion := b6RankTail_squareCompletion

/-- The family dispatcher for the B6 branch of the binary rank-tail
moment. -/
def preE7_rankTailCertificate_b6
    (family : PreE7NoPairNoC3EarlierOwnerFamily) (_hfamily : family = .b6)
    (w : ℕ) (i : PreE7NonPairActionClass w) (hsource : PreE7B6SourceData w i)
    (lit : PreE7CharacterLiterature) : PreE7B6RankTailCertificate w i :=
  preE7_b6RankTailCertificate lit hsource

theorem preE7_b6_specialMoment :
    PreE7NoPairNoC3EarlierOwnerFamily.b6.specialMoment = .binaryRankTail :=
  rfl

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

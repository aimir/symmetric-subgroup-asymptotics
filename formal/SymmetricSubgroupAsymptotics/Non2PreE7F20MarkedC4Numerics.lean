import SymmetricSubgroupAsymptotics.Non2PreE7F20MarkedC4Source
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailDecay
import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailOwnerOrJointTopClosure
import SymmetricSubgroupAsymptotics.FusionPhysicalSummedSource

/-!
# F20: the marked-`C4` numerical owner

The historical F20 row (D0386) splits each complete source `J ≤ S_b` by the
strict hot test `|Hom(J, C4)| > 2^(3b/8)` of the SAME source:

* cold sources pay the complete fibre `Z_J(U) ≤ |Epi(J,U)| + |Hom(J,C4)|`
  pointwise at slope `η = log₂(5)/5`, an ordinary cold row;
* hot sources are summed with the whole fibre retained.  On the hot set
  `Z_J(U) ≤ (|Aut U| + 1) 2^(b/8) |Hom(J,C4)|`, and the first-moment tail of
  the global marked `C4` moment at `r = ⌊b/8⌋ + 1` gives a quadratic decay of
  the exact benchmark-normalized scalar.

The marked moment is the held global theorem
`non2_global_marked_c4_moment_working.md`, eq. (0.2):

`log₂ ∑_{J ≤ S_b} |Hom(J,C4)|^r ≤ b²/16 + br/4 + r²/2 + o((b+r)²)`,

uniformly for `r/b` bounded.  It is recorded below as the explicitly named
proposition `GlobalMarkedC4MomentBound`.  It is a project theorem, not a
published result, and it is not proved in Lean here: every export in this
file that uses it takes it as a visible hypothesis.

The resulting package is the ordinary numerical package of the `.f20`
family, with a nonzero source-summed exceptional scalar.  It enters the
first-owner recurrence through the existing ordinary disjunct; no shared
interface is changed.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-! ## The marked moment -/

/-- The global marked `C4` moment `M4(b,r) = ∑_{J ≤ S_b} |Hom(J,C4)|^r`.
Literal maps are counted; there is no quotient by `Aut(C4^r)`. -/
def markedC4Moment (b r : ℕ) : ℝ :=
  ∑ J : Subgroup (Equiv.Perm (Fin b)),
    (Nat.card (J →* Multiplicative (ZMod 4)) : ℝ) ^ r

/-- **The global marked `C4` moment bound** (held project theorem,
`directions/non2_global_marked_c4_moment_working.md`, eq. (0.2), with its
independent audit `audit_non2_global_marked_c4_moment_working.md`): for every
`ε > 0` and every bound `K` on `r/b`, eventually in `b`,

`M4(b,r) ≤ 2^(b²/16 + br/4 + r²/2 + ε (b+r)²)`.

This is not a published literature result.  It is an explicit hypothesis of
every export below and is not discharged in this file. -/
def GlobalMarkedC4MomentBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ K * b →
    markedC4Moment b r ≤
      (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + (b : ℝ) * r / 4 + (r : ℝ) ^ 2 / 2 +
        ε * ((b : ℝ) + r) ^ 2)

/-! ## Constants and numerical facts -/

/-- The strict hot test of the historical F20 row. -/
def F20Hot {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  (2 : ℝ) ^ ((3 / 8 : ℝ) * b) < Nat.card (J →* Multiplicative (ZMod 4))

/-- The onto slope `η = log₂(5)/5`. -/
def preE7F20Eta : ℝ := Real.logb 2 5 / 5

/-- The cold coefficient `|Aut(C5 ⋊ C4)| + 1`. -/
def preE7F20ColdConstant : ℝ := (Nat.card (F20.G ≃* F20.G) : ℝ) + 1

/-- Harmless hot-row parameters; the F20 comparator coefficient is zero. -/
def preE7F20Delta : ℝ := preE7CharacterRho * 5 / 2

def preE7F20Cutoff : ℝ := 1 / 8 + preE7F20Delta / 2

theorem preE7F20ColdConstant_pos : 0 < preE7F20ColdConstant := by
  unfold preE7F20ColdConstant
  positivity

theorem two_logFive_le_five : 2 * Real.logb 2 5 ≤ 5 := by
  have hp : ((5 : ℝ) ^ 2) ≤ (2 : ℝ) ^ (5 : ℕ) := by norm_num
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 2) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hl
  exact_mod_cast hl

theorem fifteen_le_eight_logFive : 15 ≤ 8 * Real.logb 2 5 := by
  have hp : ((2 : ℝ) ^ (15 : ℕ)) ≤ (5 : ℝ) ^ (8 : ℕ) := by norm_num
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 15) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hl
  exact_mod_cast hl

theorem three_logFive_lt_seven : 3 * Real.logb 2 5 < 7 := by
  have hp : ((5 : ℝ) ^ 3) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hl
  exact_mod_cast hl

theorem preE7F20Eta_le_window : preE7F20Eta ≤ preE7CharacterWindow 5 := by
  have hlog := three_logFive_lt_seven
  unfold preE7F20Eta preE7CharacterWindow preE7CharacterRho halfDegree
  norm_num at hlog ⊢
  linarith

theorem threeEighths_le_eta : (3 / 8 : ℝ) ≤ preE7F20Eta := by
  have := fifteen_le_eight_logFive
  unfold preE7F20Eta
  linarith

theorem eta_sub_le_eighth : preE7F20Eta - 3 / 8 ≤ 1 / 8 := by
  have := two_logFive_le_five
  unfold preE7F20Eta
  linarith

/-- The F20 parameters satisfy every entrywise transfer condition at width
five and `ρ = 1/8192`. -/
theorem preE7F20_entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho 5 1 0 preE7F20Delta
      preE7F20Cutoff preE7F20Cutoff preE7F20Eta where
  delta_nonneg := by unfold preE7F20Delta preE7CharacterRho; norm_num
  degree_pos := by norm_num
  ratio := by unfold preE7F20Delta preE7CharacterRho; norm_num
  degree_upper := by unfold preE7CharacterRho; norm_num
  delta_lower := by unfold preE7F20Delta; norm_num
  hot_margin := by unfold preE7F20Cutoff preE7F20Delta preE7CharacterRho; norm_num
  threshold_eq := by unfold preE7F20Cutoff; norm_num
  delta_upper := by unfold preE7F20Delta preE7CharacterRho; norm_num
  degree_lower := by unfold preE7CharacterRho; norm_num
  degree_width := by norm_num
  cold_slope := by ring
  cold_gap := by
    unfold preE7F20Cutoff preE7F20Delta preE7CharacterRho halfDegree
    norm_num
  tail_gap := preE7F20Eta_le_window

/-! ## The complete fibre, the hot scalar and the summed source -/

/-- The complete fibre bound of one source: onto maps plus `C4` characters of
the same `J`. -/
def preE7F20Fibre {w : ℕ} (i : PreE7NonPairActionClass w) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  (Nat.card (GroupEpimorphism J (preE7NonPairAction w i)) : ℝ) +
    Nat.card (J →* Multiplicative (ZMod 4))

/-- The original action weight. -/
def preE7F20Weight {w : ℕ} (i : PreE7NonPairActionClass w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairAction w i : Set (Equiv.Perm (Fin w))))

/-- The exact benchmark-normalized hot scalar: the whole fibre of every hot
source, with the original action weight. -/
def preE7F20ExceptionalScalar {w : ℕ} (i : PreE7NonPairActionClass w) (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w (preE7F20Weight i) *
    ∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
      preE7F20Fibre i J

namespace PreE7F20Source

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7F20Source w i)

include S

/-- Cold sources pay the whole fibre at slope `η`. -/
theorem fibre_cold {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) (hJ : ¬ F20Hot J) :
    preE7F20Fibre i J ≤ preE7F20ColdConstant * (2 : ℝ) ^ (preE7F20Eta * b) := by
  have hepi := S.epi_card_le J
  have hcold : (Nat.card (J →* Multiplicative (ZMod 4)) : ℝ) ≤
      (2 : ℝ) ^ ((3 / 8 : ℝ) * b) := not_lt.mp hJ
  have hmono : (2 : ℝ) ^ ((3 / 8 : ℝ) * b) ≤ (2 : ℝ) ^ (preE7F20Eta * b) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right threeEighths_le_eta (Nat.cast_nonneg b))
  unfold preE7F20Fibre preE7F20ColdConstant
  change _ ≤ _ * (2 : ℝ) ^ (Real.logb 2 5 / 5 * b) at hepi
  unfold preE7F20Eta at hmono ⊢
  nlinarith

/-- The summed complete source, cold sources paid pointwise and hot sources
kept with their whole correlated fibre. -/
theorem summedSource_le (b : ℕ)
    (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w i) P J) ≤
      (subgroupCount b : ℝ) * preE7F20ColdConstant * (2 : ℝ) ^ (preE7F20Eta * b) +
        ∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
          preE7F20Fibre i J := by
  set K : ℝ := preE7F20ColdConstant * (2 : ℝ) ^ (preE7F20Eta * b)
  have hK : 0 ≤ K := mul_nonneg preE7F20ColdConstant_pos.le (by positivity)
  calc (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w i) P J)
      ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)), preE7F20Fibre i J :=
        Finset.sum_le_sum (fun J _ => S.completeSource_le P J)
    _ = (∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => ¬ F20Hot J),
          preE7F20Fibre i J) +
        ∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
          preE7F20Fibre i J := by
        rw [add_comm, Finset.sum_filter_add_sum_filter_not]
    _ ≤ (subgroupCount b : ℝ) * K +
        ∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
          preE7F20Fibre i J := by
        refine add_le_add ?_ le_rfl
        calc (∑ J ∈ Finset.univ.filter
                (fun J : Subgroup (Equiv.Perm (Fin b)) => ¬ F20Hot J), preE7F20Fibre i J)
            ≤ ∑ J ∈ Finset.univ.filter
                (fun J : Subgroup (Equiv.Perm (Fin b)) => ¬ F20Hot J), K :=
              Finset.sum_le_sum (fun J hJ => S.fibre_cold J (Finset.mem_filter.mp hJ).2)
          _ = K * ((Finset.univ.filter
                (fun J : Subgroup (Equiv.Perm (Fin b)) => ¬ F20Hot J)).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          _ ≤ K * (subgroupCount b : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ hK
              have hle := Finset.card_filter_le
                (Finset.univ : Finset (Subgroup (Equiv.Perm (Fin b))))
                (fun J => ¬ F20Hot J)
              rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
              exact_mod_cast hle
          _ = (subgroupCount b : ℝ) * K := mul_comm _ _
    _ = _ := by rw [mul_assoc]

/-! ## The local certificate -/

/-- The F20 local certificate: zero comparator row, the cold row at slope
`η`, and the hot full-fibre scalar. -/
noncomputable def localCertificate : PreE7EarlierLocalCertificate .f20 w i where
  D := fun _ => 0
  T := fun _ => preE7F20ColdConstant
  X := preE7F20ExceptionalScalar i
  v := 1
  eta := 0
  delta := preE7F20Delta
  cutoff := preE7F20Cutoff
  alpha := preE7F20Cutoff
  theta := preE7F20Eta
  alpha_eq := by ring
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun _ => preE7F20ColdConstant_pos.le
  local_bound := by
    intro b P hP _hPbroad
    have h := fusionPhysical_summedSource_normalized_bound (preE7NonPairAction w i) P hP _
      (S.summedSource_le b P)
    have hcold := growingQuotient_cold_identity (subgroupCount b : ℝ) b w
      preE7F20ColdConstant (preE7F20Weight i) preE7F20Eta 0
    rw [show preE7F20Eta + 0 = preE7F20Eta by ring] at hcold
    simp only [growingQuotientThreshold, zero_mul, Real.rpow_zero, mul_one] at hcold
    have hhotzero : growingQuotientHotKernel
        (fun n => (subgroupCount n : ℝ)) b w 1 0 (preE7F20Weight i)
        0 preE7F20Delta preE7F20Cutoff = 0 := by
      simp [growingQuotientHotKernel]
    have hcoldzero : fusionWidthColdKernel b w 0 (preE7F20Weight i) preE7F20Cutoff = 0 := by
      simp [fusionWidthColdKernel]
    change _ ≤ (growingQuotientHotKernel (fun n => (subgroupCount n : ℝ)) b w 1 0
        (preE7F20Weight i) 0 preE7F20Delta preE7F20Cutoff +
      fusionWidthColdKernel b w 0 (preE7F20Weight i) preE7F20Cutoff *
        ordinarySubgroupRatio b +
      fusionWidthColdKernel b w preE7F20ColdConstant (preE7F20Weight i) preE7F20Eta *
        ordinarySubgroupRatio b) + preE7F20ExceptionalScalar i b
    rw [hhotzero, hcoldzero, zero_mul, zero_add, zero_add, ordinarySubgroupRatio, ← hcold]
    unfold preE7F20ExceptionalScalar
    calc _ ≤ growingQuotientNormalizedPointing b w (preE7F20Weight i) *
          ((subgroupCount b : ℝ) * preE7F20ColdConstant * (2 : ℝ) ^ (preE7F20Eta * b) +
            ∑ J ∈ Finset.univ.filter
              (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J), preE7F20Fibre i J) := h
      _ = _ := by ring

/-! ## Quadratic decay of the hot scalar from the marked moment -/

/-- On a hot source the whole fibre is a fixed multiple of `2^(b/8)` times
the `C4` character count, which is in turn controlled by its `r`-th power. -/
theorem fibre_hot_le {b : ℕ} (s : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) (hJ : F20Hot J) :
    preE7F20Fibre i J ≤
      preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
        ((2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) *
          (Nat.card (J →* Multiplicative (ZMod 4)) : ℝ) ^ (s + 1)) := by
  set H : ℝ := (Nat.card (J →* Multiplicative (ZMod 4)) : ℝ)
  set t : ℝ := (2 : ℝ) ^ ((3 / 8 : ℝ) * b)
  have ht : 0 < t := by positivity
  have hH : t < H := hJ
  have hH0 : 0 < H := ht.trans hH
  have hepi := S.epi_card_le J
  -- `2^(ηb) ≤ 2^(b/8) · H`
  have hexp : (2 : ℝ) ^ (preE7F20Eta * b) ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * b) * H := by
    calc (2 : ℝ) ^ (preE7F20Eta * b)
        = (2 : ℝ) ^ ((preE7F20Eta - 3 / 8) * b) * t := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
      _ ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * b) * H := by
          apply mul_le_mul _ hH.le ht.le (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_right eta_sub_le_eighth (Nat.cast_nonneg b))
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * b) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hfib : preE7F20Fibre i J ≤
      preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) * H := by
    unfold preE7F20Fibre preE7F20ColdConstant
    change _ ≤ _ * (2 : ℝ) ^ (Real.logb 2 5 / 5 * b) at hepi
    unfold preE7F20Eta at hexp
    have hA : (0 : ℝ) ≤ Nat.card (F20.G ≃* F20.G) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * b) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hA, mul_le_mul_of_nonneg_left hone hH0.le]
  -- `H ≤ 2^(-(3/8) b s) H^(s+1)`
  have hpow : t ^ s * H ≤ H ^ (s + 1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le hH.le s) hH0.le
  have htpow : t ^ s = (2 : ℝ) ^ ((3 / 8 : ℝ) * b * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hHle : H ≤ (2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) * H ^ (s + 1) := by
    have hinv : (2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) * t ^ s = 1 := by
      rw [htpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
        Real.rpow_zero]
    calc H = (2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) * (t ^ s * H) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  calc preE7F20Fibre i J
      ≤ preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) * H := hfib
    _ ≤ _ := mul_le_mul_of_nonneg_left hHle
        (mul_nonneg preE7F20ColdConstant_pos.le (by positivity))

/-- The hot sum is controlled by the marked moment at any order `s + 1`. -/
theorem hotSum_le (b s : ℕ) :
    (∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
        preE7F20Fibre i J) ≤
      preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
        ((2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) * markedC4Moment b (s + 1)) := by
  have hc : 0 ≤ preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
      (2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) :=
    mul_nonneg (mul_nonneg preE7F20ColdConstant_pos.le (by positivity)) (by positivity)
  calc (∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
        preE7F20Fibre i J)
      ≤ ∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
          preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
            ((2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) *
              (Nat.card (J →* Multiplicative (ZMod 4)) : ℝ) ^ (s + 1)) :=
        Finset.sum_le_sum (fun J hJ => S.fibre_hot_le s J (Finset.mem_filter.mp hJ).2)
    _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
          preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
            ((2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) *
              (Nat.card (J →* Multiplicative (ZMod 4)) : ℝ) ^ (s + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun J _ _ => mul_nonneg (mul_nonneg preE7F20ColdConstant_pos.le (by positivity))
            (mul_nonneg (by positivity) (by positivity)))
    _ = _ := by
        unfold markedC4Moment
        rw [Finset.mul_sum, Finset.mul_sum]

end PreE7F20Source

theorem two_rpow_mul_mul (a b c : ℝ) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ b * (2 : ℝ) ^ c) = (2 : ℝ) ^ (a + b + c) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_assoc]

theorem two_rpow_regroup (e C x y : ℝ) :
    (e * (2 : ℝ) ^ x) * (C * (2 : ℝ) ^ y) = (e * C) * (2 : ℝ) ^ (x + y) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The quadratic exponent bookkeeping of the hot scalar. -/
theorem preE7F20_exponent_le (B R : ℝ) (hB : 2048 ≤ B) (hR1 : B + 1 ≤ 8 * R)
    (hR2 : 8 * R ≤ B + 8) :
    ((1 / 2048 : ℝ) * (B + 5) ^ 2 - (B + 5) ^ 2 / 16 + 5 * (B + 5) / 8 + 1 / 4) +
        (1 / 8 : ℝ) * B + (-((3 / 8 : ℝ) * B * (R - 1))) +
        (B ^ 2 / 16 + B * R / 4 + R ^ 2 / 2 + (1 / 2048 : ℝ) * (B + R) ^ 2) ≤
      -(B ^ 2) / 512 := by
  have hB0 : 0 ≤ B := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hBR : B * (B + 1) ≤ 8 * (B * R) := by nlinarith
  have hRR : R ^ 2 * 64 ≤ (B + 8) ^ 2 := by nlinarith
  have hsum : (B + R) ^ 2 * 64 ≤ (9 * B + 8) ^ 2 := by nlinarith
  have hBB : 2048 * B ≤ B ^ 2 := by nlinarith
  nlinarith

namespace PreE7F20Source

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7F20Source w i)

include S

/-- **Scalar decay.**  The marked moment gives the hot F20 scalar a fixed
quadratic deficit, with the original action weight retained. -/
theorem exceptionalScalar_eventually (hM4 : GlobalMarkedC4MomentBound) :
    ∀ᶠ b : ℕ in atTop,
      preE7F20ExceptionalScalar i b ≤
        (eulerProduct⁻¹ * preE7F20ColdConstant) * (2 : ℝ) ^ (-((b : ℝ) ^ 2) / 512) := by
  have hw := S.width_eq
  subst hw
  have hmoment := hM4 (1 / 2048) (by norm_num) 1
  have hsucc := (tendsto_add_atTop_nat 5).eventually
    (eventually_succ_le_two_rpow (show (0 : ℝ) < 1 / 2048 by norm_num))
  filter_upwards [hmoment, hsucc, eventually_ge_atTop 2048] with b hM hs hb
  set s : ℕ := b / 8
  have hbR : (2048 : ℝ) ≤ b := by exact_mod_cast hb
  have hs1 : (b : ℝ) + 1 ≤ 8 * ((s + 1 : ℕ) : ℝ) := by
    have : b + 1 ≤ 8 * (s + 1) := by omega
    exact_mod_cast this
  have hs2 : 8 * ((s + 1 : ℕ) : ℝ) ≤ (b : ℝ) + 8 := by
    have : 8 * (s + 1) ≤ b + 8 := by omega
    exact_mod_cast this
  have hrK : ((s + 1 : ℕ) : ℝ) ≤ 1 * b := by
    have : s + 1 ≤ b := by omega
    rw [one_mul]
    exact_mod_cast this
  have hmom := hM (s + 1) hrK
  -- the pointing
  have hA : (1 : ℝ) ≤ preE7F20Weight i := by
    unfold preE7F20Weight
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (preE7NonPairAction 5 i : Set (Equiv.Perm (Fin 5)))))
  have hpoint0 := fusionWidthHot_pointing_denominator_le b 5
  have hfac : (((b + 5 + 1 : ℕ) : ℝ) ^ (b + 5)) ≤
      (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2) := by
    have hs' : (((b + 5) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b + 5 : ℕ) : ℝ)) := hs
    calc (((b + 5 + 1 : ℕ) : ℝ) ^ (b + 5))
        ≤ ((2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b + 5 : ℕ) : ℝ))) ^ (b + 5) :=
          pow_le_pow_left₀ (by positivity) hs' _
      _ = (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          push_cast
          ring
  have hpoint : growingQuotientNormalizedPointing b 5 (preE7F20Weight i) ≤
      eulerProduct⁻¹ *
        (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2 - ((b : ℝ) + 5) ^ 2 / 16 +
          5 * ((b : ℝ) + 5) / 8 + 1 / 4) := by
    unfold growingQuotientNormalizedPointing
    have hnum : 0 ≤ (((b + 5).factorial : ℝ) / (b.factorial : ℝ)) := by positivity
    have hbench : 0 < exactBenchmark (b + 5) := exactBenchmark_pos (b + 5)
    calc ((((b + 5).factorial : ℝ) / (b.factorial : ℝ)) / preE7F20Weight i) /
          exactBenchmark (b + 5)
        ≤ (((b + 5).factorial : ℝ) / (b.factorial : ℝ)) / exactBenchmark (b + 5) := by
          apply div_le_div_of_nonneg_right _ hbench.le
          exact div_le_self hnum hA
      _ ≤ eulerProduct⁻¹ * (((b + 5 + 1 : ℕ) : ℝ) ^ (b + 5)) *
          (2 : ℝ) ^ (-((b + 5 : ℕ) : ℝ) ^ 2 / 16 + 5 * ((b + 5 : ℕ) : ℝ) / 8 + 1 / 4) :=
          hpoint0
      _ ≤ eulerProduct⁻¹ * (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2) *
          (2 : ℝ) ^ (-((b + 5 : ℕ) : ℝ) ^ 2 / 16 + 5 * ((b + 5 : ℕ) : ℝ) / 8 + 1 / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hfac (inv_nonneg.mpr euler_positive.le)
      _ = _ := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          push_cast
          ring
  -- the hot sum
  have hhot := S.hotSum_le b s
  have hhot' : (∑ J ∈ Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J), preE7F20Fibre i J) ≤
      preE7F20ColdConstant *
        (2 : ℝ) ^ ((1 / 8 : ℝ) * b + (-((3 / 8 : ℝ) * b * s)) +
          ((b : ℝ) ^ 2 / 16 + (b : ℝ) * ((s + 1 : ℕ) : ℝ) / 4 +
            ((s + 1 : ℕ) : ℝ) ^ 2 / 2 + 1 / 2048 * ((b : ℝ) + ((s + 1 : ℕ) : ℝ)) ^ 2)) := by
    calc _ ≤ preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
          ((2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) * markedC4Moment b (s + 1)) := hhot
      _ ≤ preE7F20ColdConstant * (2 : ℝ) ^ ((1 / 8 : ℝ) * b) *
          ((2 : ℝ) ^ (-((3 / 8 : ℝ) * b * s)) *
            (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + (b : ℝ) * ((s + 1 : ℕ) : ℝ) / 4 +
              ((s + 1 : ℕ) : ℝ) ^ 2 / 2 + 1 / 2048 * ((b : ℝ) + ((s + 1 : ℕ) : ℝ)) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg preE7F20ColdConstant_pos.le (by positivity))
          exact mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = _ := by
          rw [mul_assoc, two_rpow_mul_mul]
  have hexp := preE7F20_exponent_le (b : ℝ) ((s + 1 : ℕ) : ℝ) hbR hs1 hs2
  have hsR : ((s : ℕ) : ℝ) = ((s + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  unfold preE7F20ExceptionalScalar
  have hsum0 : 0 ≤ ∑ J ∈ Finset.univ.filter
      (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J), preE7F20Fibre i J :=
    Finset.sum_nonneg (fun J _ => by unfold preE7F20Fibre; positivity)
  have hpointU : 0 ≤ eulerProduct⁻¹ *
      (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2 - ((b : ℝ) + 5) ^ 2 / 16 +
        5 * ((b : ℝ) + 5) / 8 + 1 / 4) :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity)
  calc growingQuotientNormalizedPointing b 5 (preE7F20Weight i) *
        ∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) => F20Hot J),
          preE7F20Fibre i J
      ≤ (eulerProduct⁻¹ *
          (2 : ℝ) ^ ((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2 - ((b : ℝ) + 5) ^ 2 / 16 +
            5 * ((b : ℝ) + 5) / 8 + 1 / 4)) *
        (preE7F20ColdConstant *
          (2 : ℝ) ^ ((1 / 8 : ℝ) * b + (-((3 / 8 : ℝ) * b * s)) +
            ((b : ℝ) ^ 2 / 16 + (b : ℝ) * ((s + 1 : ℕ) : ℝ) / 4 +
              ((s + 1 : ℕ) : ℝ) ^ 2 / 2 + 1 / 2048 * ((b : ℝ) + ((s + 1 : ℕ) : ℝ)) ^ 2))) :=
        mul_le_mul hpoint hhot' hsum0 hpointU
    _ = (eulerProduct⁻¹ * preE7F20ColdConstant) *
        (2 : ℝ) ^ (((1 / 2048 : ℝ) * ((b : ℝ) + 5) ^ 2 - ((b : ℝ) + 5) ^ 2 / 16 +
            5 * ((b : ℝ) + 5) / 8 + 1 / 4) +
          ((1 / 8 : ℝ) * b + (-((3 / 8 : ℝ) * b * s)) +
            ((b : ℝ) ^ 2 / 16 + (b : ℝ) * ((s + 1 : ℕ) : ℝ) / 4 +
              ((s + 1 : ℕ) : ℝ) ^ 2 / 2 + 1 / 2048 * ((b : ℝ) + ((s + 1 : ℕ) : ℝ)) ^ 2))) :=
        two_rpow_regroup _ _ _ _
    _ ≤ (eulerProduct⁻¹ * preE7F20ColdConstant) * (2 : ℝ) ^ (-((b : ℝ) ^ 2) / 512) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (inv_nonneg.mpr euler_positive.le) preE7F20ColdConstant_pos.le)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hsR]
        linarith [hexp]

/-! ## The local and numerical packages -/

/-- The F20 local package: the certificate and the decay of its hot scalar. -/
noncomputable def localPackage (hM4 : GlobalMarkedC4MomentBound) :
    PreE7EarlierLocalPackage .f20 w i where
  certificate := S.localCertificate
  exceptional := fun _ => by
    let h := eventually_atTop.mp (S.exceptionalScalar_eventually hM4)
    let N : ℕ := Classical.choose h
    have hN := Classical.choose_spec h
    let K : ℝ := eulerProduct⁻¹ * preE7F20ColdConstant
    have hK : 0 ≤ K :=
      mul_nonneg (inv_nonneg.mpr euler_positive.le) preE7F20ColdConstant_pos.le
    refine
      { threshold := max N 1
        rate := 1 / 512
        constant := K + 1
        rate_pos := by norm_num
        constant_pos := by linarith
        bound := ?_ }
    intro b hb
    have hbN : N ≤ b := (le_max_left _ _).trans hb
    have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
    have hquad := hN b hbN
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hexp : -((b : ℝ) ^ 2) / 512 ≤ -(1 / 512 : ℝ) * b := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ b by positivity) (sub_nonneg.mpr hbR)]
    exact hquad.trans (mul_le_mul (by linarith)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (by positivity) (by linarith))
  exceptional_support := Or.inr (by rw [S.width_eq]; norm_num)

/-- **The F20 numerical owner package**: the certificate, its entry
parameters at `ρ = 1/8192`, and the menu-mass bounds of both coefficient
rows. -/
noncomputable def numericalPackage (hM4 : GlobalMarkedC4MomentBound) :
    PreE7EarlierNumericalPackage .f20 w i where
  package := S.localPackage hM4
  parameters := by
    have hw := S.width_eq
    subst hw
    exact preE7F20_entryParameters
  main_total_growth := .inl (fun b => by
    change (0 : ℝ) ≤ _
    positivity)
  tail_total_bound := fun b => by
    change preE7F20ColdConstant ≤ _
    have hw := S.width_eq
    subst hw
    have haut := F20.aut_card_le
    calc preE7F20ColdConstant ≤ (160001 : ℝ) := by
          unfold preE7F20ColdConstant
          have : (Nat.card (F20.G ≃* F20.G) : ℝ) ≤ 160000 := by exact_mod_cast haut
          linarith
      _ ≤ (2 : ℝ) ^ (16 * ((5 : ℕ) : ℝ)) := by norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (by norm_num) b

/-- The numerically certified family predicate of the `.f20` owner. -/
theorem numericalFamilyAction (hM4 : GlobalMarkedC4MomentBound) :
    preE7NoPairNoC3EarlierNumericalFamilyAction .f20 w i :=
  ⟨S.numericalPackage hM4⟩

/-- **The F20 bridge.**  An actual F20 action produces the literal numerical
owner consumed by the first-owner recurrence, through the ordinary
numerical disjunct of the rank-tail catalogue. -/
noncomputable def rankTailActionOwner (hM4 : GlobalMarkedC4MomentBound) :
    PreE7NumericalRankTailActionOwner w i :=
  ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .f20, by
    simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
      preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
      (Or.inl (S.numericalFamilyAction hM4) :
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .f20 w i)⟩

end PreE7F20Source

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

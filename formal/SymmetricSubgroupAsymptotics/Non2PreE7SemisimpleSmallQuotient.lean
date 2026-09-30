import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators
import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate
import SymmetricSubgroupAsymptotics.Non2PreE7SmallOrderSemisimple

/-!
# SNS: a semisimple normal layer with small literal quotient

This file proves the complete quotient estimate used by the SNS family.
If `|R| ≤ 2^l`, the literal normal axes of `R` number at most `2^(l^2)`.
The ordinary permutation-source generator bound gives at most
`2^l * 2^((l/2)b)` onto maps on each axis.  Multiplying this exact quotient
sum by the semisimple outer factor gives the direct earlier-owner envelope.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {R : Type*} [Group R] [Finite R]

/-- One literal quotient axis of a group of order at most `2^l`. -/
theorem quotientEpimorphism_card_le_of_order
    (hgen : PermutationSubgroupGeneratorBound)
    (l b : ℕ) (horder : Nat.card R ≤ 2 ^ l)
    (N : {N : Subgroup R // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (R ⧸ N.1)) : ℝ) ≤
      (2 : ℝ) ^ l * (2 : ℝ) ^ (((l : ℝ) / 2) * b) := by
  obtain ⟨S, hS, hScard⟩ := hgen b J
  have hQ : Nat.card (R ⧸ N.1) ≤ 2 ^ l :=
    (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk_surjective (s := N.1))).trans horder
  have hepi : Nat.card (GroupEpimorphism J (R ⧸ N.1)) ≤
      Nat.card (J →* (R ⧸ N.1)) := by
    letI : Finite (J →* (R ⧸ N.1)) := Finite.of_injective
      (fun f : J →* (R ⧸ N.1) => (f : J → R ⧸ N.1))
      DFunLike.coe_injective
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hnat : Nat.card (GroupEpimorphism J (R ⧸ N.1)) ≤
      2 ^ (l * S.card) := by
    calc
      Nat.card (GroupEpimorphism J (R ⧸ N.1)) ≤
          Nat.card (J →* (R ⧸ N.1)) := hepi
      _ ≤ Nat.card (R ⧸ N.1) ^ S.card :=
        monoidHom_card_le_pow_of_closure S hS
      _ ≤ (2 ^ l) ^ S.card := Nat.pow_le_pow_left hQ _
      _ = 2 ^ (l * S.card) := by rw [pow_mul]
  have hexponent : ((l * S.card : ℕ) : ℝ) ≤
      l + ((l : ℝ) / 2) * b := by
    have hScardR : (2 : ℝ) * S.card ≤ b + 2 := by exact_mod_cast hScard
    have hl0 : (0 : ℝ) ≤ l := by positivity
    push_cast
    nlinarith
  have hreal :
      (Nat.card (GroupEpimorphism J (R ⧸ N.1)) : ℝ) ≤
        (2 : ℝ) ^ ((l * S.card : ℕ) : ℝ) := by
    calc
      (Nat.card (GroupEpimorphism J (R ⧸ N.1)) : ℝ) ≤
          ((2 ^ (l * S.card) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 : ℝ) ^ ((l * S.card : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
  calc
    (Nat.card (GroupEpimorphism J (R ⧸ N.1)) : ℝ) ≤
        (2 : ℝ) ^ ((l * S.card : ℕ) : ℝ) := hreal
    _ ≤ (2 : ℝ) ^ (l + ((l : ℝ) / 2) * b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = (2 : ℝ) ^ l * (2 : ℝ) ^ (((l : ℝ) / 2) * b) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [Real.rpow_natCast]

/-- The complete literal quotient sum, including every normal axis. -/
theorem completeQuotientWeight_le_of_order
    (hgen : PermutationSubgroupGeneratorBound)
    (l b : ℕ) (horder : Nat.card R ≤ 2 ^ l)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      (2 : ℝ) ^ (l * l + l) *
        (2 : ℝ) ^ (((l : ℝ) / 2) * b) := by
  let B : ℝ := (2 : ℝ) ^ l * (2 : ℝ) ^ (((l : ℝ) / 2) * b)
  have haxis : ∀ N : {N : Subgroup R // N.Normal},
      (Nat.card (GroupEpimorphism J (R ⧸ N.1)) : ℝ) ≤ B :=
    fun N => quotientEpimorphism_card_le_of_order hgen l b horder N J
  have hnormal := normalSubgroup_card_le_two_pow_sq (R := R) l horder
  unfold completeQuotientWeight completeQuotientCount
  calc
    (↑(∑ N : {N : Subgroup R // N.Normal},
        Nat.card (GroupEpimorphism J (R ⧸ N.1))) : ℝ) =
        ∑ N : {N : Subgroup R // N.Normal},
          (Nat.card (GroupEpimorphism J (R ⧸ N.1)) : ℝ) := by
            rw [Nat.cast_sum]
    _ ≤ ∑ _N : {N : Subgroup R // N.Normal}, B := by
      apply Finset.sum_le_sum
      intro N _
      exact haxis N
    _ = (Nat.card {N : Subgroup R // N.Normal} : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_eq_nat_card]
    _ ≤ ((2 ^ (l * l) : ℕ) : ℝ) * B := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnormal) (by positivity)
    _ = (2 : ℝ) ^ (l * l + l) *
        (2 : ℝ) ^ (((l : ℝ) / 2) * b) := by
      dsimp [B]
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_add]
      ring

namespace Non2UnipotentPrefixFiniteMenu

/-- One literal SNS action: a nontrivial semisimple normal layer and a
small actual quotient. -/
structure PreE7SnsActionCertificate
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 64 ≤ w
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  layer_ne_bot : E ≠ ⊥
  chart : SemisimpleNormalChart E
  l : ℕ
  quotient_order_le : Nat.card (preE7NonPairAction w i ⧸ E) ≤ 2 ^ l
  quotient_small : 8 * l ≤ w

attribute [instance] PreE7SnsActionCertificate.E_normal

namespace PreE7SnsActionCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7SnsActionCertificate w i)

def eta : ℝ := (C.l : ℝ) / 2

def degree (_C : PreE7SnsActionCertificate w i) : ℕ :=
  paddedComparatorDegree preE7CharacterRho 2 w

def delta : ℝ := paddedComparatorDelta preE7CharacterRho C.eta 2 w

def cutoff : ℝ := (C.degree : ℝ) / 8 + C.delta / 2

def coefficient (b : ℕ) : ℝ :=
  (2 : ℝ) ^ (C.l * C.l + C.l) *
    C.chart.outerFactor (Real.logb 2 (Nat.factorial b))

theorem coefficient_nonneg (b : ℕ) : 0 ≤ C.coefficient b :=
  mul_nonneg (by positivity)
    (C.chart.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast Nat.factorial_pos b)))

theorem degree_margin :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 - C.eta := by
  have hlR : (8 : ℝ) * C.l ≤ w := by exact_mod_cast C.quotient_small
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hw : (64 : ℝ) ≤ w := by exact_mod_cast C.width_lower
  unfold preE7CharacterRho eta
  norm_num
  linarith

private theorem log_source_le_factorial
    (_C : PreE7SnsActionCertificate w i) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    Real.logb 2 (Nat.card J) ≤ Real.logb 2 (Nat.factorial b) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.card_pos)
  have hcard := Nat.card_le_card_of_injective
    (Subtype.val : J → Equiv.Perm (Fin b)) Subtype.val_injective
  rw [Nat.card_perm, Nat.card_fin] at hcard
  exact_mod_cast hcard

/-- The complete direct SNS envelope. -/
noncomputable def direct (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SemisimpleDirectSourceData .sns w i where
  template_eq := rfl
  E := C.E
  E_normal := C.E_normal
  chart := C.chart
  v := C.degree
  coefficient := C.coefficient
  eta := C.eta
  delta := C.delta
  cutoff := C.cutoff
  alpha := C.eta + C.cutoff
  theta := 0
  alpha_eq := rfl
  coefficient_nonneg := C.coefficient_nonneg
  combined_bound := by
    intro b J
    have hquot := completeQuotientWeight_le_of_order hgen C.l b
      C.quotient_order_le J
    have hfactor : C.chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
        C.chart.outerFactor (Real.logb 2 (Nat.factorial b)) := by
      unfold SemisimpleNormalChart.outerFactor
      apply Finset.prod_le_prod
      · intro k _
        exact add_nonneg zero_le_one
          (C.chart.factorWeight_nonneg
            (Real.logb_nonneg (by norm_num)
              (by exact_mod_cast Nat.card_pos)) k)
      · intro k _
        simpa only [add_comm] using add_le_add_left
          (C.chart.factorWeight_mono
            (C.log_source_le_factorial b J) k) 1
    calc
      completeQuotientWeight
          (R := preE7NonPairAction w i ⧸ C.E) J *
          C.chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
        ((2 : ℝ) ^ (C.l * C.l + C.l) *
          (2 : ℝ) ^ (C.eta * b)) *
          C.chart.outerFactor (Real.logb 2 (Nat.factorial b)) :=
            mul_le_mul hquot hfactor
              (C.chart.outerFactor_nonneg
                (Real.logb_nonneg (by norm_num)
                  (by exact_mod_cast Nat.card_pos)))
              (by positivity)
      _ = C.coefficient b * (2 : ℝ) ^ (C.eta * b) := by
        unfold coefficient
        ring

end PreE7SnsActionCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

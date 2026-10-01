import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailDecay
import SymmetricSubgroupAsymptotics.GrowingMenuMassCertificate
import SymmetricSubgroupAsymptotics.GrowingQuotientExceptionalAggregation

/-!
# Fixed-width B6 and Y1 rank-tail menus

The B6 and Y1 certificates contain action-dependent constants.  They should
not be forced through the uniform all-width coefficient envelope used by the
ordinary catalogue.  Their widths are literally twelve and eight, so the
complete menus have finite width support.  This file aggregates the retained
constants directly and proves the exact growing-menu bounds needed by the
cold continuation rows.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

abbrev PreE7B6MenuIndex (w : ℕ) :=
  {i : PreE7NonPairActionClass w // Nonempty (PreE7B6SourceData w i)}

abbrev PreE7Y1MenuIndex (w : ℕ) :=
  {i : PreE7NonPairActionClass w // Nonempty (PreE7Y1SourceData w i)}

noncomputable instance preE7B6MenuIndexFintype (w : ℕ) :
    Fintype (PreE7B6MenuIndex w) := Fintype.ofFinite _

noncomputable instance preE7Y1MenuIndexFintype (w : ℕ) :
    Fintype (PreE7Y1MenuIndex w) := Fintype.ofFinite _

noncomputable def preE7B6MenuSource {w : ℕ} (i : PreE7B6MenuIndex w) :
    PreE7B6SourceData w i.1 := Classical.choice i.2

noncomputable def preE7Y1MenuSource {w : ℕ} (i : PreE7Y1MenuIndex w) :
    PreE7Y1SourceData w i.1 := Classical.choice i.2

noncomputable def preE7B6MenuCertificate (lit : PreE7CharacterLiterature)
    {w : ℕ} (i : PreE7B6MenuIndex w) : PreE7B6RankTailCertificate w i.1 :=
  preE7_b6RankTailCertificate lit (preE7B6MenuSource i)

noncomputable def preE7Y1MenuCertificate (lit : PreE7CharacterLiterature)
    {w : ℕ} (i : PreE7Y1MenuIndex w) : PreE7Y1RankTailCertificate w i.1 :=
  preE7_y1RankTailCertificate lit (preE7Y1MenuSource i)

def preE7B6MenuNormalizer {w : ℕ} (i : PreE7B6MenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairAction w i.1 : Set (Equiv.Perm (Fin w))))

def preE7Y1MenuNormalizer {w : ℕ} (i : PreE7Y1MenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairAction w i.1 : Set (Equiv.Perm (Fin w))))

theorem preE7B6MenuNormalizer_pos {w : ℕ} (i : PreE7B6MenuIndex w) :
    0 < preE7B6MenuNormalizer i := by
  unfold preE7B6MenuNormalizer
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7NonPairAction w i.1 : Set (Equiv.Perm (Fin w)))))

theorem preE7Y1MenuNormalizer_pos {w : ℕ} (i : PreE7Y1MenuIndex w) :
    0 < preE7Y1MenuNormalizer i := by
  unfold preE7Y1MenuNormalizer
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7NonPairAction w i.1 : Set (Equiv.Perm (Fin w)))))

def preE7B6MenuCoefficient (lit : PreE7CharacterLiterature) {w : ℕ}
    (i : PreE7B6MenuIndex w) (b : ℕ) : ℝ :=
  (preE7B6MenuCertificate lit i).coldConstant * (1 + b)

def preE7Y1MenuCoefficient (lit : PreE7CharacterLiterature) {w : ℕ}
    (i : PreE7Y1MenuIndex w) (b : ℕ) : ℝ :=
  (preE7Y1MenuCertificate lit i).coldConstant * (1 + b)

theorem preE7B6MenuCoefficient_nonneg (lit : PreE7CharacterLiterature)
    {w : ℕ} (i : PreE7B6MenuIndex w) (b : ℕ) :
    0 ≤ preE7B6MenuCoefficient lit i b :=
  mul_nonneg (preE7B6MenuCertificate lit i).coldConstant_nonneg (by positivity)

theorem preE7Y1MenuCoefficient_nonneg (lit : PreE7CharacterLiterature)
    {w : ℕ} (i : PreE7Y1MenuIndex w) (b : ℕ) :
    0 ≤ preE7Y1MenuCoefficient lit i b :=
  mul_nonneg (preE7Y1MenuCertificate lit i).coldConstant_nonneg (by positivity)

def preE7B6MenuExceptional (lit : PreE7CharacterLiterature) {w : ℕ}
    (i : PreE7B6MenuIndex w) (b : ℕ) : ℝ :=
  preE7B6ExceptionalScalar (preE7B6MenuCertificate lit i) b

def preE7Y1MenuExceptional (lit : PreE7CharacterLiterature) {w : ℕ}
    (i : PreE7Y1MenuIndex w) (b : ℕ) : ℝ :=
  preE7Y1ExceptionalScalar (preE7Y1MenuCertificate lit i) b

private theorem preE7B6Menu_width {w : ℕ} (i : PreE7B6MenuIndex w) :
    w = 12 := (preE7B6MenuSource i).width_eq

private theorem preE7Y1Menu_width {w : ℕ} (i : PreE7Y1MenuIndex w) :
    w = 8 := (preE7Y1MenuSource i).width_eq

/-- The arbitrary retained B6 constants are harmless because their literal
menu is supported only at width twelve. -/
theorem preE7B6Menu_polynomialMass (lit : PreE7CharacterLiterature) :
    PolynomialSubquadraticMenuMassBound 3
      (fun w i => preE7B6MenuCoefficient lit (w := w) i)
      (fun w i => preE7B6MenuNormalizer (w := w) i) := by
  intro epsilon hepsilon
  let B : ℝ := ∑ i : PreE7B6MenuIndex 12,
    (preE7B6MenuCertificate lit i).coldConstant /
      preE7B6MenuNormalizer i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ =>
    div_nonneg (preE7B6MenuCertificate lit i).coldConstant_nonneg
      (preE7B6MenuNormalizer_pos i).le)
  refine ⟨B, 1, hB, ?_⟩
  intro n w hw
  by_cases hne : w = 12
  · subst w
    have hn : 12 ≤ n := by
      have := (Finset.mem_Ico.mp hw).2
      omega
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (epsilon * (12 : ℝ) ^ 2) := by
      rw [← Real.rpow_zero (2 : ℝ)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      positivity
    calc
      (∑ i : PreE7B6MenuIndex 12,
          preE7B6MenuCoefficient lit i (n - 12) /
            preE7B6MenuNormalizer i) = B * (1 + (n - 12) : ℕ) := by
          dsimp only [B, preE7B6MenuCoefficient]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          push_cast
          ring
      _ ≤ B * ((n + 1 : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hB
          exact_mod_cast (show 1 + (n - 12) ≤ n + 1 by omega)
      _ ≤ B * (((n + 1 : ℕ) : ℝ) ^ 1) *
          (2 : ℝ) ^ (epsilon * (12 : ℝ) ^ 2) := by
          simp only [pow_one]
          exact le_mul_of_one_le_right (mul_nonneg hB (by positivity)) hpow
  · haveI : IsEmpty (PreE7B6MenuIndex w) :=
      ⟨fun i => hne (preE7B6Menu_width i)⟩
    simp only [Finset.sum_of_isEmpty]
    positivity

/-- The arbitrary retained Y1 constants are harmless because their literal
menu is supported only at width eight. -/
theorem preE7Y1Menu_polynomialMass (lit : PreE7CharacterLiterature) :
    PolynomialSubquadraticMenuMassBound 3
      (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
      (fun w i => preE7Y1MenuNormalizer (w := w) i) := by
  intro epsilon hepsilon
  let B : ℝ := ∑ i : PreE7Y1MenuIndex 8,
    (preE7Y1MenuCertificate lit i).coldConstant /
      preE7Y1MenuNormalizer i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ =>
    div_nonneg (preE7Y1MenuCertificate lit i).coldConstant_nonneg
      (preE7Y1MenuNormalizer_pos i).le)
  refine ⟨B, 1, hB, ?_⟩
  intro n w hw
  by_cases hne : w = 8
  · subst w
    have hn : 8 ≤ n := by
      have := (Finset.mem_Ico.mp hw).2
      omega
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (epsilon * (8 : ℝ) ^ 2) := by
      rw [← Real.rpow_zero (2 : ℝ)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      positivity
    calc
      (∑ i : PreE7Y1MenuIndex 8,
          preE7Y1MenuCoefficient lit i (n - 8) /
            preE7Y1MenuNormalizer i) = B * (1 + (n - 8) : ℕ) := by
          dsimp only [B, preE7Y1MenuCoefficient]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          push_cast
          ring
      _ ≤ B * ((n + 1 : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hB
          exact_mod_cast (show 1 + (n - 8) ≤ n + 1 by omega)
      _ ≤ B * (((n + 1 : ℕ) : ℝ) ^ 1) *
          (2 : ℝ) ^ (epsilon * (8 : ℝ) ^ 2) := by
          simp only [pow_one]
          exact le_mul_of_one_le_right (mul_nonneg hB (by positivity)) hpow
  · haveI : IsEmpty (PreE7Y1MenuIndex w) :=
      ⟨fun i => hne (preE7Y1Menu_width i)⟩
    simp only [Finset.sum_of_isEmpty]
    positivity

theorem preE7B6MenuMass (lit : PreE7CharacterLiterature) :
    GrowingMenuMassBound 3
      (fun w i => preE7B6MenuCoefficient lit (w := w) i)
      (fun w i => preE7B6MenuNormalizer (w := w) i) :=
  growingMenuMassBound_of_polynomialSubquadratic (by omega) _ _
    (preE7B6Menu_polynomialMass lit)

theorem preE7Y1MenuMass (lit : PreE7CharacterLiterature) :
    GrowingMenuMassBound 3
      (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
      (fun w i => preE7Y1MenuNormalizer (w := w) i) :=
  growingMenuMassBound_of_polynomialSubquadratic (by omega) _ _
    (preE7Y1Menu_polynomialMass lit)

noncomputable def preE7B6MenuExceptionalBound
    (lit : PreE7CharacterLiterature)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ExponentialScalarBound (growingQuotientExceptionalTotal 3
      (fun w i => preE7B6MenuExceptional lit (w := w) i)) := by
  apply exponentialScalarBound_growingQuotientExceptionalTotal 3 12
  · intro w i
    exact (PreE7EarlierLocalPackage.ofB6
      (preE7B6MenuCertificate lit i)).exceptional hcoarse
  · intro w i hw
    have := preE7B6Menu_width i
    exact False.elim (by omega : False)

noncomputable def preE7Y1MenuExceptionalBound
    (lit : PreE7CharacterLiterature)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ExponentialScalarBound (growingQuotientExceptionalTotal 3
      (fun w i => preE7Y1MenuExceptional lit (w := w) i)) := by
  apply exponentialScalarBound_growingQuotientExceptionalTotal 3 8
  · intro w i
    exact (PreE7EarlierLocalPackage.ofY1
      (preE7Y1MenuCertificate lit i)).exceptional hcoarse
  · intro w i hw
    have := preE7Y1Menu_width i
    exact False.elim (by omega : False)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

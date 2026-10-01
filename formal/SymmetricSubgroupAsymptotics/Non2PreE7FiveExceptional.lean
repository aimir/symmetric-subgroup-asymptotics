import SymmetricSubgroupAsymptotics.FusionFiniteComparatorListTransfer
import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage

/-!
# The three exceptional local-five owners

The retained statistic is the arithmetic mean of the literal comparator
list consisting of the top and every invariant line quotient.  Distinct
literal entries remain distinct even when their abstract groups are
isomorphic.  Jensen's inequality, proved in `FiniteComparatorListMoment`,
gives the exact degree-`4s` moments.  This module installs the audited
all-normal finite-group inequality for `s = 2,3,4` as one numerical owner.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

inductive PreE7FiveExceptionalKind
  | two | three | four
  deriving DecidableEq, Fintype

def PreE7FiveExceptionalKind.blocks : PreE7FiveExceptionalKind → ℕ
  | .two => 2
  | .three => 3
  | .four => 4

def PreE7FiveExceptionalKind.width (k : PreE7FiveExceptionalKind) : ℕ :=
  5 * k.blocks

def PreE7FiveExceptionalKind.degree (k : PreE7FiveExceptionalKind) : ℕ :=
  4 * k.blocks

def PreE7FiveExceptionalKind.delta : PreE7FiveExceptionalKind → ℝ
  | .two | .three => 1 / 4
  | .four => 1 / 2

def PreE7FiveExceptionalKind.cutoff : PreE7FiveExceptionalKind → ℝ
  | .two => 9 / 8
  | .three => 13 / 8
  | .four => 9 / 4

def PreE7FiveExceptionalKind.tailSlope : PreE7FiveExceptionalKind → ℝ
  | .two | .three => Real.logb 2 5 / 5
  | .four => 1 + Real.logb 2 5 / 5

private theorem three_logFive_lt_seven :
    3 * Real.logb 2 5 < 7 := by
  have hp : ((5 : ℝ) ^ 3) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 3) hp
  simpa [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

theorem PreE7FiveExceptionalKind.tail_window
    (k : PreE7FiveExceptionalKind) :
    k.tailSlope ≤ preE7CharacterWindow k.width := by
  have hlog := three_logFive_lt_seven
  cases k <;>
    norm_num [PreE7FiveExceptionalKind.tailSlope,
      PreE7FiveExceptionalKind.width, PreE7FiveExceptionalKind.blocks,
      preE7CharacterWindow, preE7CharacterRho, halfDegree] <;>
    linarith

theorem PreE7FiveExceptionalKind.entryParameters
    (k : PreE7FiveExceptionalKind) :
    PreE7CharacterEntryParameters preE7CharacterRho k.width k.degree 0
      k.delta k.cutoff k.cutoff k.tailSlope := by
  cases k <;>
    refine
      { delta_nonneg := by norm_num [PreE7FiveExceptionalKind.delta]
        degree_pos := by norm_num [PreE7FiveExceptionalKind.degree,
          PreE7FiveExceptionalKind.blocks]
        ratio := by norm_num [preE7CharacterRho,
          PreE7FiveExceptionalKind.delta,
          PreE7FiveExceptionalKind.degree,
          PreE7FiveExceptionalKind.blocks]
        degree_upper := by norm_num [preE7CharacterRho,
          PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.degree,
          PreE7FiveExceptionalKind.blocks]
        delta_lower := by norm_num [preE7CharacterRho,
          PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.delta,
          PreE7FiveExceptionalKind.blocks]
        hot_margin := by norm_num [PreE7FiveExceptionalKind.cutoff,
          PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.delta,
          PreE7FiveExceptionalKind.blocks]
        threshold_eq := by norm_num [PreE7FiveExceptionalKind.cutoff,
          PreE7FiveExceptionalKind.degree,
          PreE7FiveExceptionalKind.delta,
          PreE7FiveExceptionalKind.blocks]
        delta_upper := by norm_num [PreE7FiveExceptionalKind.delta,
          PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.blocks]
        degree_lower := by norm_num [preE7CharacterRho,
          PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.degree,
          PreE7FiveExceptionalKind.blocks]
        degree_width := by norm_num [PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.degree,
          PreE7FiveExceptionalKind.blocks]
        cold_slope := by norm_num
        cold_gap := by norm_num [preE7CharacterRho,
          PreE7FiveExceptionalKind.width,
          PreE7FiveExceptionalKind.cutoff,
          PreE7FiveExceptionalKind.blocks, halfDegree]
        tail_gap := PreE7FiveExceptionalKind.tail_window _ }

/-- One actual exceptional local-five action.  The exact list is stored as a
finite type rather than collapsed to abstract isomorphism classes. -/
structure PreE7FiveExceptionalSource
    (kind : PreE7FiveExceptionalKind)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_eq : w = kind.width
  Comparator : Type
  [comparator_fintype : Fintype Comparator]
  [comparator_nonempty : Nonempty Comparator]
  Q : Comparator → Subgroup (Equiv.Perm (Fin kind.degree))
  tailConstant : ℝ
  tailConstant_nonneg : 0 ≤ tailConstant
  complete_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := preE7NonPairAction w i) J ≤
      (∑ k : Comparator, completeQuotientWeight (R := Q k) J) +
        tailConstant * (2 : ℝ) ^ (kind.tailSlope * b)
  main_menu : ∀ b,
    (Nat.card Comparator : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_menu : ∀ b,
    tailConstant ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

attribute [instance]
  PreE7FiveExceptionalSource.comparator_fintype
  PreE7FiveExceptionalSource.comparator_nonempty

namespace PreE7FiveExceptionalSource

variable {kind : PreE7FiveExceptionalKind}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7FiveExceptionalSource kind w i)

private theorem list_count_pos : (0 : ℝ) < Nat.card S.Comparator := by
  exact_mod_cast Nat.card_pos (α := S.Comparator)

private theorem count_mul_statistic {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card S.Comparator : ℝ) *
        finiteComparatorListStatistic S.Q J =
      ∑ k : S.Comparator, completeQuotientWeight (R := S.Q k) J := by
  unfold finiteComparatorListStatistic
  field_simp

private theorem source_envelope {b : ℕ}
    (P : Subgroup
      (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
    (hPbroad : ∀ H, P H → preE7NoPairNoC3BroadActionPredicate w i b H)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      (Nat.card S.Comparator : ℝ) *
          finiteComparatorListStatistic S.Q J +
        S.tailConstant * (2 : ℝ) ^ (kind.tailSlope * b) := by
  have hmono :
      fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
        fusionCompleteSourceSum (preE7NonPairAction w i)
          (preE7NoPairNoC3BroadActionPredicate w i b) J := by
    unfold fusionCompleteSourceSum
    exact Finset.sum_le_sum (fun N _ =>
      fusionSurvivingEpiCount_mono hPbroad N J)
  have hforget :
      fusionCompleteSourceSum (preE7NonPairAction w i)
          (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
        completeQuotientWeight (R := preE7NonPairAction w i) J := by
    unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun N _ =>
      fusionSurvivingEpiCount_le_groupEpimorphism_card
        (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) N J)
  calc
    _ ≤ completeQuotientWeight (R := preE7NonPairAction w i) J :=
      hmono.trans hforget
    _ ≤ (∑ k : S.Comparator,
          completeQuotientWeight (R := S.Q k) J) +
        S.tailConstant * (2 : ℝ) ^ (kind.tailSlope * b) :=
      S.complete_bound J
    _ = _ := by rw [S.count_mul_statistic J]

/-- The exact local physical certificate obtained from the finite-list
moment. -/
noncomputable def localCertificate :
    PreE7EarlierLocalCertificate .fiveExc w i where
  D := fun _ => Nat.card S.Comparator
  T := fun _ => S.tailConstant
  X := fun _ => 0
  v := kind.degree
  eta := 0
  delta := kind.delta
  cutoff := kind.cutoff
  alpha := kind.cutoff
  theta := kind.tailSlope
  alpha_eq := by simp
  D_nonneg := fun _ => Nat.cast_nonneg _
  T_nonneg := fun _ => S.tailConstant_nonneg
  local_bound := by
    intro b P hP hPbroad
    have h := fusionPhysical_finiteComparatorList_additiveTail_kernel_bound
      (preE7NonPairAction w i) P hP S.Q
      (Nat.card S.Comparator : ℝ) S.tailConstant kind.tailSlope
      kind.delta kind.cutoff (Nat.cast_nonneg _) (S.source_envelope P hPbroad)
    simpa only [zero_add, add_zero] using h

noncomputable def localPackage :
    PreE7EarlierLocalPackage .fiveExc w i where
  certificate := S.localCertificate
  exceptional := fun _ =>
    { threshold := 0
      rate := 1
      constant := 1
      rate_pos := by norm_num
      constant_pos := by norm_num
      bound := by simp [localCertificate] }
  exceptional_support := Or.inl rfl

/-- Complete numerical fiveExc package for all three block counts. -/
noncomputable def numericalPackage :
    PreE7EarlierNumericalPackage .fiveExc w i where
  package := S.localPackage
  parameters := by
    simpa only [localPackage, localCertificate] using
      (S.width_eq.symm ▸ kind.entryParameters)
  main_total_bound := S.main_menu
  tail_total_bound := S.tail_menu

include S

theorem numericalFamilyAction :
    preE7NoPairNoC3EarlierNumericalFamilyAction .fiveExc w i :=
  ⟨S.numericalPackage⟩

end PreE7FiveExceptionalSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceComparator
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics

/-!
# The complete-envelope S3EXC owner

Every historical S3EXC branch has the same correlated all-normal shape

`Z_J(U) ≤ (B 2^(eta b)) Z_J(Q) + C 2^(theta b)`.

The P branches have `B = 0`, the A branches have `eta = 0`, and the M
branches have `C = 0`.  This file keeps that complete quotient sum intact,
pads the actual comparator action, and proves the common numerical owner
package once.  The source record is the exact finite-group theorem to be
supplied by the audited S3-local calculation; it contains no owner-order or
action-census assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- One S3EXC action with its audited complete all-normal envelope. -/
structure PreE7S3ExceptionalSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  sourceDegree : ℕ
  sourceDegree_two : 2 ≤ sourceDegree
  Q : Subgroup (Equiv.Perm (Fin sourceDegree))
  B : ℝ
  C : ℝ
  eta : ℝ
  theta : ℝ
  B_nonneg : 0 ≤ B
  C_nonneg : 0 ≤ C
  eta_nonneg : 0 ≤ eta
  exponent_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - sourceDegree) / 8 - eta
  tail_window : theta ≤ preE7CharacterWindow w
  complete_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := preE7NonPairAction w i) J ≤
      (B * (2 : ℝ) ^ (eta * b)) *
          completeQuotientWeight (R := Q) J +
        C * (2 : ℝ) ^ (theta * b)
  main_menu : ∀ b,
    B ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_menu : ∀ b,
    C ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7S3ExceptionalSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7S3ExceptionalSource w i)

def degree : ℕ :=
  paddedComparatorDegree preE7CharacterRho S.sourceDegree w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho S.eta S.sourceDegree w

def cutoff : ℝ := (S.degree : ℝ) / 8 + S.delta / 2

def alpha : ℝ := S.eta + S.cutoff

def paddedAction : S.Q →* Equiv.Perm (Fin S.degree) :=
  (characterComparatorPadHom (le_max_left _ _)).comp S.Q.subtype

theorem paddedAction_injective : Function.Injective S.paddedAction :=
  (characterComparatorPadHom_injective _).comp Subtype.val_injective

theorem entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho w S.degree S.eta S.delta
      S.cutoff S.alpha S.theta := by
  simpa [degree, delta, cutoff, alpha] using
    (preE7Padded_entryParameters_withTail
      (w := w) (v0 := S.sourceDegree) (eta := S.eta) (theta := S.theta)
      S.eta_nonneg S.sourceDegree_two S.exponent_margin S.tail_window)

/-- The complete S3EXC envelope as a direct source comparator.  The first
inequality only forgets the broad-source predicate; no normal-axis factor is
introduced. -/
noncomputable def certificate :
    PreE7CompleteSourceComparatorCertificate .s3exc w i where
  R := S.Q
  groupR := inferInstance
  finiteR := inferInstance
  v := S.degree
  action := S.paddedAction
  action_injective := S.paddedAction_injective
  D := fun _ => S.B
  T := fun _ => S.C
  eta := S.eta
  delta := S.delta
  cutoff := S.cutoff
  alpha := S.alpha
  theta := S.theta
  alpha_eq := rfl
  D_nonneg := fun _ => S.B_nonneg
  T_nonneg := fun _ => S.C_nonneg
  broad_source_envelope := by
    intro b J
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
    exact hforget.trans (S.complete_bound J)

/-- The complete numerical S3EXC package, covering all P/A/M branches of
the historical owner through their common all-normal inequality. -/
noncomputable def numericalData :
    PreE7CompleteSourceNumericalData .s3exc w i where
  certificate := S.certificate
  parameters := S.entryParameters
  main_total_bound := S.main_menu
  tail_total_bound := S.tail_menu

include S

/-- S3EXC enters the exact numerical earlier-family predicate without an
owner-precedence hypothesis. -/
theorem numericalFamilyAction :
    preE7NoPairNoC3EarlierNumericalFamilyAction .s3exc w i :=
  ⟨(PreE7S3ExceptionalSource.numericalData S).toPackage⟩

end PreE7S3ExceptionalSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

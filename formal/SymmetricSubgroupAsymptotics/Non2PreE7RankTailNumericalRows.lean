import SymmetricSubgroupAsymptotics.Non2PreE7RankTailNumericalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalRows

/-!
# Local rows for the complete numerical rank-tail catalogue
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

noncomputable def preE7B6OwnedMenuIndex {w : ℕ}
    (j : PreE7B6OwnedIndex w) : PreE7B6MenuIndex w :=
  ⟨j.2.1, j.2.2.2⟩

noncomputable def preE7Y1OwnedMenuIndex {w : ℕ}
    (j : PreE7Y1OwnedIndex w) : PreE7Y1MenuIndex w :=
  ⟨j.2.1, j.2.2.2⟩

/-- A terminal row against the ordinary/B6/Y1/SNS2 first-owner predicate. -/
structure PreE7NumericalRankTailResidualChoice
    (w : ℕ) (U : PreE7NonPairActionClass w) where
  D : ℕ → ℝ
  v : ℕ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  X : ℕ → ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  main_total_growth :
    (∀ b, D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) ∨
    (∀ b, D b ≤ (2 : ℝ) ^
      (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)))
  exceptional : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
    ExponentialScalarBound X
  exceptional_support : X = 0 ∨ w ≤ 12288
  local_bound : ∀ b,
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w U)
      (FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b))) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta cutoff +
        fusionWidthColdKernel b w (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          alpha * ordinarySubgroupRatio b + X b

/-- Terminal numerical data only for the width-at-least-four actions that
remain after the complete degree-three packet has been removed. -/
abbrev PreE7NumericalRankTailResidualData :=
  ∀ w (t : PreE7NumericalTerminalIndex w),
    PreE7NumericalRankTailResidualChoice w t.action

variable
  (lit : PreE7CharacterLiterature)
  (Residual : PreE7NumericalRankTailResidualData)

def preE7NumericalRankTailD (w : ℕ)
    (j : PreE7NumericalRankTailIndex w) (b : ℕ) : ℝ :=
  match j with
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.D b
  | .b6 _ | .y1 _ | .sns2 _ => 0
  | .terminal t => (Residual w t).D b

def preE7NumericalRankTailT (w : ℕ)
    (j : PreE7NumericalRankTailIndex w) (b : ℕ) : ℝ :=
  match j with
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.T b
  | .b6 a => preE7B6MenuCoefficient lit (preE7B6OwnedMenuIndex a) b
  | .y1 a => preE7Y1MenuCoefficient lit (preE7Y1OwnedMenuIndex a) b
  | .sns2 a => preE7Sns2MenuCoefficient (preE7Sns2OwnedMenuIndex a) b
  | .terminal _ => 0

def preE7NumericalRankTailX (w : ℕ)
    (j : PreE7NumericalRankTailIndex w) (b : ℕ) : ℝ :=
  match j with
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.X b
  | .b6 a => preE7B6MenuExceptional lit (preE7B6OwnedMenuIndex a) b
  | .y1 a => preE7Y1MenuExceptional lit (preE7Y1OwnedMenuIndex a) b
  | .sns2 a => preE7Sns2MenuExceptional (preE7Sns2OwnedMenuIndex a) b
  | .terminal t => (Residual w t).X b

def preE7NumericalRankTailA (w : ℕ)
    (j : PreE7NumericalRankTailIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NumericalRankTailAction w j : Set (Equiv.Perm (Fin w))))

def preE7NumericalRankTailV (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℕ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.v
  | .b6 _ | .y1 _ | .sns2 _ => preE7EmptyCellDegree w
  | .terminal t => (Residual w t).v

def preE7NumericalRankTailEta (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.eta
  | .b6 _ | .y1 _ | .sns2 _ => 0
  | .terminal t => (Residual w t).eta

def preE7NumericalRankTailDelta (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.delta
  | .b6 _ | .y1 _ | .sns2 _ => preE7EmptyCellDelta w
  | .terminal t => (Residual w t).delta

def preE7NumericalRankTailCutoff (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.cutoff
  | .b6 _ | .y1 _ | .sns2 _ => preE7EmptyCellCutoff w
  | .terminal t => (Residual w t).cutoff

def preE7NumericalRankTailAlpha (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.alpha
  | .b6 _ | .y1 _ | .sns2 _ => preE7EmptyCellAlpha w
  | .terminal t => (Residual w t).alpha

def preE7NumericalRankTailTheta (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.theta
  | .b6 _ => 4 / 3
  | .y1 _ => 153 / 200
  | .sns2 a => preE7Sns2MenuSlope (preE7Sns2OwnedMenuIndex a)
  | .terminal _ => 0

theorem preE7NumericalRankTailD_nonneg :
    ∀ w j b, 0 ≤ preE7NumericalRankTailD Residual w j b := by
  intro w j b
  cases j with
  | ordinary a =>
      exact (preE7NumericalOwnedPackage a).package.certificate.D_nonneg b
  | b6 | y1 | sns2 => exact le_rfl
  | terminal t => exact (Residual w t).D_nonneg b

theorem preE7NumericalRankTailT_nonneg :
    ∀ w j b, 0 ≤ preE7NumericalRankTailT lit w j b := by
  intro w j b
  cases j with
  | ordinary a =>
      exact (preE7NumericalOwnedPackage a).package.certificate.T_nonneg b
  | b6 a => exact preE7B6MenuCoefficient_nonneg lit _ _
  | y1 a => exact preE7Y1MenuCoefficient_nonneg lit _ _
  | sns2 a => exact preE7Sns2MenuCoefficient_nonneg _ _
  | terminal => exact le_rfl

theorem preE7NumericalRankTailA_pos (w : ℕ)
    (j : PreE7NumericalRankTailIndex w) :
    0 < preE7NumericalRankTailA w j := by
  unfold preE7NumericalRankTailA
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7NumericalRankTailAction w j : Set (Equiv.Perm (Fin w)))))

/-- Every cell of the enlarged disjoint menu has its exact local row. -/
theorem preE7NumericalRankTail_local_bound :
    GrowingQuotientAdditiveExceptionalLocalPhysicalBound 3
      preE7NumericalRankTailAction preE7NumericalRankTailPredicate
      (preE7NumericalRankTailD Residual)
      (preE7NumericalRankTailT lit) (preE7NumericalRankTailX lit Residual)
      preE7NumericalRankTailA (preE7NumericalRankTailV Residual)
      (preE7NumericalRankTailEta Residual)
      (preE7NumericalRankTailDelta Residual)
      (preE7NumericalRankTailCutoff Residual)
      (preE7NumericalRankTailAlpha Residual)
      preE7NumericalRankTailTheta := by
  intro n j
  have hwn : j.1.1 ≤ n := growingQuotientPhysicalWidth_le j
  rw [GrowingQuotientCanonicalFamily, fusionWidthCanonicalFamily_card]
  cases j.2 with
  | ordinary a =>
      let C := preE7NumericalOwnedPackage a
      have h := C.package.certificate.local_bound (n - j.1.1)
        (preE7NumericalRankTailPredicate j.1.1 (.ordinary a) (n - j.1.1))
        (preE7NumericalRankTailPredicate_natural j.1.1 (.ordinary a)
          (n - j.1.1))
        (preE7NumericalRankTailPredicate_implies_broad j.1.1 (.ordinary a)
          (n - j.1.1))
      simpa [Nat.sub_add_cancel hwn, C, preE7NumericalRankTailAction,
        preE7NumericalRankTailActionClass, preE7NumericalRankTailD,
        preE7NumericalRankTailT, preE7NumericalRankTailX,
        preE7NumericalRankTailA, preE7NumericalRankTailV,
        preE7NumericalRankTailEta, preE7NumericalRankTailDelta,
        preE7NumericalRankTailCutoff, preE7NumericalRankTailAlpha,
        preE7NumericalRankTailTheta] using h
  | b6 a =>
      let C := PreE7EarlierLocalCertificate.ofB6
        (preE7B6MenuCertificate lit (preE7B6OwnedMenuIndex a))
      have h := C.local_bound (n - j.1.1)
        (preE7NumericalRankTailPredicate j.1.1 (.b6 a) (n - j.1.1))
        (preE7NumericalRankTailPredicate_natural j.1.1 (.b6 a)
          (n - j.1.1))
        (preE7NumericalRankTailPredicate_implies_broad j.1.1 (.b6 a)
          (n - j.1.1))
      simp only [C, PreE7EarlierLocalCertificate.ofB6] at h
      simpa [Nat.sub_add_cancel hwn, C, preE7NumericalRankTailAction,
        preE7NumericalRankTailActionClass, preE7NumericalRankTailD,
        preE7NumericalRankTailT, preE7NumericalRankTailX,
        preE7NumericalRankTailA, preE7NumericalRankTailV,
        preE7NumericalRankTailEta, preE7NumericalRankTailDelta,
        preE7NumericalRankTailCutoff, preE7NumericalRankTailAlpha,
        preE7NumericalRankTailTheta, preE7B6MenuCoefficient,
        preE7B6MenuExceptional, preE7B6OwnedMenuIndex,
        growingQuotientHotKernel,
        fusionWidthColdKernel] using h
  | y1 a =>
      let C := PreE7EarlierLocalCertificate.ofY1
        (preE7Y1MenuCertificate lit (preE7Y1OwnedMenuIndex a))
      have h := C.local_bound (n - j.1.1)
        (preE7NumericalRankTailPredicate j.1.1 (.y1 a) (n - j.1.1))
        (preE7NumericalRankTailPredicate_natural j.1.1 (.y1 a)
          (n - j.1.1))
        (preE7NumericalRankTailPredicate_implies_broad j.1.1 (.y1 a)
          (n - j.1.1))
      simp only [C, PreE7EarlierLocalCertificate.ofY1] at h
      simpa [Nat.sub_add_cancel hwn, C, preE7NumericalRankTailAction,
        preE7NumericalRankTailActionClass, preE7NumericalRankTailD,
        preE7NumericalRankTailT, preE7NumericalRankTailX,
        preE7NumericalRankTailA, preE7NumericalRankTailV,
        preE7NumericalRankTailEta, preE7NumericalRankTailDelta,
        preE7NumericalRankTailCutoff, preE7NumericalRankTailAlpha,
        preE7NumericalRankTailTheta, preE7Y1MenuCoefficient,
        preE7Y1MenuExceptional, preE7Y1OwnedMenuIndex,
        growingQuotientHotKernel,
        fusionWidthColdKernel] using h
  | sns2 a =>
      let C := PreE7EarlierLocalCertificate.ofSns2
        (preE7Sns2OwnedCertificate a)
      have h := C.local_bound (n - j.1.1)
        (preE7NumericalRankTailPredicate j.1.1 (.sns2 a) (n - j.1.1))
        (preE7NumericalRankTailPredicate_natural j.1.1 (.sns2 a)
          (n - j.1.1))
        (preE7NumericalRankTailPredicate_implies_broad j.1.1 (.sns2 a)
          (n - j.1.1))
      simp only [C, PreE7EarlierLocalCertificate.ofSns2] at h
      simpa [Nat.sub_add_cancel hwn, C, preE7NumericalRankTailAction,
        preE7NumericalRankTailActionClass, preE7NumericalRankTailD,
        preE7NumericalRankTailT, preE7NumericalRankTailX,
        preE7NumericalRankTailA, preE7NumericalRankTailV,
        preE7NumericalRankTailEta, preE7NumericalRankTailDelta,
        preE7NumericalRankTailCutoff, preE7NumericalRankTailAlpha,
        preE7NumericalRankTailTheta, preE7Sns2OwnedCertificate,
        preE7Sns2MenuCoefficient, preE7Sns2MenuSlope,
        preE7Sns2MenuExceptional, growingQuotientHotKernel,
        fusionWidthColdKernel] using h
  | terminal t =>
      have h := (Residual j.1.1 t).local_bound (n - j.1.1)
      simpa [Nat.sub_add_cancel hwn, preE7NumericalRankTailAction,
        preE7NumericalRankTailActionClass, preE7NumericalRankTailD,
        preE7NumericalRankTailT, preE7NumericalRankTailX,
        preE7NumericalRankTailA, preE7NumericalRankTailV,
        preE7NumericalRankTailEta, preE7NumericalRankTailDelta,
        preE7NumericalRankTailCutoff, preE7NumericalRankTailAlpha,
        preE7NumericalRankTailTheta, fusionWidthColdKernel] using h

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

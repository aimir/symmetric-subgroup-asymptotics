import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalCatalogue

/-!
# Local rows for the disjoint numerical/SNS2 catalogue
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The numerically certified package retained by an ordinary owned entry. -/
noncomputable def preE7NumericalOwnedPackage {w : ℕ}
    (j : PreE7NumericalOwnedIndex w) :
    PreE7EarlierNumericalPackage
      (preE7NoPairNoC3EarlierOwnerEquiv j.1) w j.2.1 :=
  Classical.choice j.2.2

/-- Forget the unique SNS2 owner label while retaining its literal source. -/
noncomputable def preE7Sns2OwnedMenuIndex {w : ℕ}
    (j : PreE7Sns2OwnedIndex w) : PreE7Sns2MenuIndex w :=
  ⟨j.2.1, j.2.2.2⟩

noncomputable def preE7Sns2OwnedCertificate {w : ℕ}
    (j : PreE7Sns2OwnedIndex w) :
    PreE7Sns2RankTailCertificate w j.2.1 :=
  preE7Sns2MenuCertificate (preE7Sns2OwnedMenuIndex j)

/-- A terminal row against the enlarged ordinary-plus-SNS2 first-owner
predicate.  A later constructor supplies it from joint Yoneda cells. -/
structure PreE7NumericalSns2ResidualChoice
    (w : ℕ) (U : PreE7NonPairActionClass w) where
  D : ℕ → ℝ
  v : ℕ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  main_total_bound : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  local_bound : ∀ b,
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w U)
      (FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
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
          alpha * ordinarySubgroupRatio b

variable
  (Residual : ∀ w (U : PreE7NonPairActionClass w),
    PreE7NumericalSns2ResidualChoice w U)

def preE7NumericalSns2D (w : ℕ)
    (j : PreE7NumericalSns2Index w) (b : ℕ) : ℝ :=
  match j with
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.D b
  | .inr (.inl _) => 0
  | .inr (.inr U) => (Residual w U).D b

def preE7NumericalSns2T (w : ℕ)
    (j : PreE7NumericalSns2Index w) (b : ℕ) : ℝ :=
  match j with
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.T b
  | .inr (.inl a) =>
      preE7Sns2MenuCoefficient (preE7Sns2OwnedMenuIndex a) b
  | .inr (.inr _) => 0

def preE7NumericalSns2X (w : ℕ)
    (j : PreE7NumericalSns2Index w) (b : ℕ) : ℝ :=
  match j with
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.X b
  | .inr (.inl a) =>
      preE7Sns2MenuExceptional (preE7Sns2OwnedMenuIndex a) b
  | .inr (.inr _) => 0

def preE7NumericalSns2A (w : ℕ)
    (j : PreE7NumericalSns2Index w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NumericalSns2Action w j : Set (Equiv.Perm (Fin w))))

def preE7NumericalSns2V (w : ℕ) :
    PreE7NumericalSns2Index w → ℕ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.v
  | .inr (.inl _) => preE7EmptyCellDegree w
  | .inr (.inr U) => (Residual w U).v

def preE7NumericalSns2Eta (w : ℕ) :
    PreE7NumericalSns2Index w → ℝ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.eta
  | .inr (.inl _) => 0
  | .inr (.inr U) => (Residual w U).eta

def preE7NumericalSns2Delta (w : ℕ) :
    PreE7NumericalSns2Index w → ℝ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.delta
  | .inr (.inl _) => preE7EmptyCellDelta w
  | .inr (.inr U) => (Residual w U).delta

def preE7NumericalSns2Cutoff (w : ℕ) :
    PreE7NumericalSns2Index w → ℝ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.cutoff
  | .inr (.inl _) => preE7EmptyCellCutoff w
  | .inr (.inr U) => (Residual w U).cutoff

def preE7NumericalSns2Alpha (w : ℕ) :
    PreE7NumericalSns2Index w → ℝ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.alpha
  | .inr (.inl _) => preE7EmptyCellAlpha w
  | .inr (.inr U) => (Residual w U).alpha

def preE7NumericalSns2Theta (w : ℕ) :
    PreE7NumericalSns2Index w → ℝ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.theta
  | .inr (.inl a) => preE7Sns2MenuSlope (preE7Sns2OwnedMenuIndex a)
  | .inr (.inr _) => 0

theorem preE7NumericalSns2D_nonneg :
    ∀ w j b, 0 ≤ preE7NumericalSns2D Residual w j b := by
  intro w j b
  rcases j with a | a
  · exact (preE7NumericalOwnedPackage a).package.certificate.D_nonneg b
  · rcases a with a | U
    · exact le_rfl
    · exact (Residual w U).D_nonneg b

theorem preE7NumericalSns2T_nonneg :
    ∀ w j b, 0 ≤ preE7NumericalSns2T w j b := by
  intro w j b
  rcases j with a | a
  · exact (preE7NumericalOwnedPackage a).package.certificate.T_nonneg b
  · rcases a with a | U
    · exact preE7Sns2MenuCoefficient_nonneg _ _
    · exact le_rfl

theorem preE7NumericalSns2A_pos (w : ℕ)
    (j : PreE7NumericalSns2Index w) :
    0 < preE7NumericalSns2A w j := by
  unfold preE7NumericalSns2A
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7NumericalSns2Action w j : Set (Equiv.Perm (Fin w)))))

/-- Every disjoint-menu cell has its exact physical row. -/
theorem preE7NumericalSns2_local_bound :
    GrowingQuotientAdditiveExceptionalLocalPhysicalBound 3
      preE7NumericalSns2Action preE7NumericalSns2Predicate
      (preE7NumericalSns2D Residual) preE7NumericalSns2T
      preE7NumericalSns2X preE7NumericalSns2A
      (preE7NumericalSns2V Residual) (preE7NumericalSns2Eta Residual)
      (preE7NumericalSns2Delta Residual)
      (preE7NumericalSns2Cutoff Residual)
      (preE7NumericalSns2Alpha Residual)
      preE7NumericalSns2Theta := by
  intro n j
  have hwn : j.1.1 ≤ n := growingQuotientPhysicalWidth_le j
  rw [GrowingQuotientCanonicalFamily, fusionWidthCanonicalFamily_card]
  rcases j.2 with a | a
  · let C := preE7NumericalOwnedPackage a
    have h := C.package.certificate.local_bound (n - j.1.1)
      (preE7NumericalSns2Predicate j.1.1 (Sum.inl a) (n - j.1.1))
      (preE7NumericalSns2Predicate_natural j.1.1 (Sum.inl a) (n - j.1.1))
      (preE7NumericalSns2Predicate_implies_broad
        j.1.1 (Sum.inl a) (n - j.1.1))
    simpa [Nat.sub_add_cancel hwn, C, preE7NumericalSns2Action,
      preE7NumericalSns2ActionClass,
      preE7NumericalSns2D, preE7NumericalSns2T, preE7NumericalSns2X,
      preE7NumericalSns2A, preE7NumericalSns2V,
      preE7NumericalSns2Eta, preE7NumericalSns2Delta,
      preE7NumericalSns2Cutoff, preE7NumericalSns2Alpha,
      preE7NumericalSns2Theta] using h
  · rcases a with a | U
    · let C := PreE7EarlierLocalCertificate.ofSns2
        (preE7Sns2OwnedCertificate a)
      have h := C.local_bound (n - j.1.1)
        (preE7NumericalSns2Predicate j.1.1
          (Sum.inr (Sum.inl a)) (n - j.1.1))
        (preE7NumericalSns2Predicate_natural j.1.1
          (Sum.inr (Sum.inl a)) (n - j.1.1))
        (preE7NumericalSns2Predicate_implies_broad j.1.1
          (Sum.inr (Sum.inl a)) (n - j.1.1))
      simp only [C, PreE7EarlierLocalCertificate.ofSns2] at h
      simpa [Nat.sub_add_cancel hwn, C, preE7NumericalSns2Action,
        preE7NumericalSns2ActionClass,
        preE7NumericalSns2D, preE7NumericalSns2T,
        preE7NumericalSns2X, preE7NumericalSns2A,
        preE7NumericalSns2V, preE7NumericalSns2Eta,
        preE7NumericalSns2Delta, preE7NumericalSns2Cutoff,
        preE7NumericalSns2Alpha, preE7NumericalSns2Theta,
        preE7Sns2OwnedCertificate, preE7Sns2MenuCoefficient,
        preE7Sns2MenuSlope, preE7Sns2MenuExceptional,
        growingQuotientHotKernel, fusionWidthColdKernel] using h
    · have h := (Residual j.1.1 U).local_bound (n - j.1.1)
      simpa [Nat.sub_add_cancel hwn, preE7NumericalSns2Action,
        preE7NumericalSns2ActionClass,
        preE7NumericalSns2D, preE7NumericalSns2T,
        preE7NumericalSns2X, preE7NumericalSns2A,
        preE7NumericalSns2V, preE7NumericalSns2Eta,
        preE7NumericalSns2Delta, preE7NumericalSns2Cutoff,
        preE7NumericalSns2Alpha, preE7NumericalSns2Theta,
        fusionWidthColdKernel] using h

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

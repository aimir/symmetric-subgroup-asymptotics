import SymmetricSubgroupAsymptotics.Non2PreE7DirectSecondaryClosure
import SymmetricSubgroupAsymptotics.T1NumericalJointTopClosure
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2Forward
import SymmetricSubgroupAsymptotics.Non2PreE7EmptyCellNumerics

/-!
# The numerical ordinary catalogue with the correlated SNS2 sector

The pointwise numerical owners, the literal SNS2 menu, and the final residual
are indexed as a disjoint sum.  Hence the SNS2 cold/hot theorem is used once
on precisely its own original-action menu.  No per-action SNS2 menu bound is
asserted.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- The frozen owner position of SNS2. -/
def preE7Sns2OwnerIndex : Fin preE7NoPairNoC3EarlierOwnerCount :=
  preE7NoPairNoC3EarlierOwnerEquiv.symm .sns2

@[simp] theorem preE7Sns2OwnerIndex_family :
    preE7NoPairNoC3EarlierOwnerEquiv preE7Sns2OwnerIndex = .sns2 :=
  preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply .sns2

/-- Numerical ordinary owner/action pairs, with the package retained. -/
abbrev PreE7NumericalOwnedIndex (w : ℕ) :=
  Σ k : Fin preE7NoPairNoC3EarlierOwnerCount,
    {U : PreE7NonPairActionClass w //
      preE7NoPairNoC3EarlierNumericalFamilyAction
        (preE7NoPairNoC3EarlierOwnerEquiv k) w U}

/-- SNS2 owner/action pairs retain the literal owner index as well as the
source.  This avoids transporting an orbit witness through an equality of
owner indices in the physical cover. -/
abbrev PreE7Sns2OwnedIndex (w : ℕ) :=
  Σ k : Fin preE7NoPairNoC3EarlierOwnerCount,
    {U : PreE7NonPairActionClass w //
      preE7NoPairNoC3EarlierOwnerEquiv k = .sns2 ∧
        Nonempty (PreE7Sns2SourceData w U)}

/-- Disjoint physical menu: pointwise numerical owners, SNS2, and the final
residual action. -/
abbrev PreE7NumericalSns2Index (w : ℕ) :=
  PreE7NumericalOwnedIndex w ⊕
    (PreE7Sns2OwnedIndex w ⊕ PreE7NonPairActionClass w)

noncomputable instance preE7NumericalOwnedIndexFintype (w : ℕ) :
    Fintype (PreE7NumericalOwnedIndex w) := Fintype.ofFinite _

noncomputable instance preE7NumericalSns2IndexFintype (w : ℕ) :
    Fintype (PreE7NumericalSns2Index w) := instFintypeSum _ _

/-- The family predicate whose first-owner partition is represented by the
disjoint menu. -/
def preE7NoPairNoC3EarlierNumericalSns2FamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (U : PreE7NonPairActionClass w) : Prop :=
  preE7NoPairNoC3EarlierNumericalFamilyAction family w U ∨
    (family = .sns2 ∧ Nonempty (PreE7Sns2SourceData w U))

def preE7NumericalSns2Owner {w : ℕ} :
    PreE7NumericalSns2Index w →
      Fin (preE7NoPairNoC3EarlierOwnerCount + 1)
  | .inl j => j.1.castSucc
  | .inr (.inl i) => i.1.castSucc
  | .inr (.inr _) => Fin.last preE7NoPairNoC3EarlierOwnerCount

def preE7NumericalSns2ActionClass {w : ℕ} :
    PreE7NumericalSns2Index w → PreE7NonPairActionClass w
  | .inl j => j.2.1
  | .inr (.inl i) => i.2.1
  | .inr (.inr U) => U

def preE7NumericalSns2Action (w : ℕ)
    (j : PreE7NumericalSns2Index w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  preE7NonPairAction w (preE7NumericalSns2ActionClass j)

def preE7NumericalSns2Predicate
    (w : ℕ) (j : PreE7NumericalSns2Index w) (b : ℕ) :
    Subgroup (preE7NumericalSns2Action w j × Equiv.Perm (Fin b)) → Prop :=
  preE7NoPairNoC3CertifiedFirstOwnerPredicate
    preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
    (preE7NumericalSns2Owner j, preE7NumericalSns2ActionClass j) b

theorem preE7NumericalSns2Predicate_natural
    (w : ℕ) (j : PreE7NumericalSns2Index w) (b : ℕ) :
    FusionOrbitNatural (preE7NumericalSns2Action w j)
      (preE7NumericalSns2Predicate w j b) := by
  exact preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
    preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
    (preE7NumericalSns2Owner j, preE7NumericalSns2ActionClass j) b

theorem preE7NumericalSns2Predicate_implies_broad
    (w : ℕ) (j : PreE7NumericalSns2Index w) (b : ℕ)
    (H : Subgroup (preE7NumericalSns2Action w j × Equiv.Perm (Fin b))) :
    preE7NumericalSns2Predicate w j b H →
      preE7NoPairNoC3BroadActionPredicate w
        (preE7NumericalSns2ActionClass j) b H := by
  rintro ⟨⟨⟨hordinary, _howner⟩, hnoC3⟩, _hselected⟩
  exact ⟨hordinary, hnoC3⟩

/-- Literal coverage by the disjoint ordinary/SNS2/residual menu. -/
theorem preE7NumericalSns2_physical_cover
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NoPairNoC3ResidualSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := PreE7NumericalSns2Index) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7NumericalSns2Action preE7NumericalSns2Predicate j := by
  let Earlier := preE7NoPairNoC3EarlierFamilyPredicate
    preE7NoPairNoC3EarlierNumericalSns2FamilyAction
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (ownerOrResidualEligible Earlier n) H
      (ownerOrResidualEligible_cover Earlier H)
  by_cases ho : owner.val < preE7NoPairNoC3EarlierOwnerCount
  · let k : Fin preE7NoPairNoC3EarlierOwnerCount := ⟨owner.val, ho⟩
    have howner_eq : owner = k.castSucc := by apply Fin.ext; rfl
    have hearlier : Earlier n k H := by
      simpa only [howner_eq, ownerOrResidualEligible_castSucc] using howner.1
    obtain ⟨W⟩ := hearlier
    have hw : Nat.card W.orbit.orbit = W.width := by
      simpa only [Nat.card_fin] using (Nat.card_congr W.chart).symm
    have hwn : W.width ≤ n := by
      have hcard := Nat.card_le_card_of_injective
        (Subtype.val : W.orbit.orbit → Fin n) Subtype.val_injective
      simpa only [hw, Nat.card_fin] using hcard
    have hmem : W.width ∈ Finset.Ico 3 (n + 1) :=
      Finset.mem_Ico.mpr ⟨W.width_three, Nat.lt_succ_of_le hwn⟩
    have hold := mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier
        (preE7NoPairNoC3EarlierFamilyPredicate_natural _))
      H hH.1.1.1.1 hH.2 owner howner W.orbit hw hwn W.action W.chart
        W.action_eq
    rw [howner_eq] at hold
    rcases W.applies with hordinary | hsns2
    · let a : PreE7NumericalOwnedIndex W.width :=
        ⟨k, W.action, hordinary⟩
      let j : GrowingQuotientPhysicalIndex
          (ι := PreE7NumericalSns2Index) 3 n :=
        ⟨⟨W.width, hmem⟩, Sum.inl a⟩
      refine ⟨j, ?_⟩
      have hselected : preE7NoPairNoC3SelectedActionEligible
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction W.width
            (k.castSucc, W.action) := by
        rw [preE7NoPairNoC3SelectedActionEligible_castSucc]
        exact Or.inl hordinary
      have hpredicate :
          preE7NoPairNoC3CertifiedFirstOwnerPredicate
              preE7NoPairNoC3EarlierNumericalSns2FamilyAction W.width
                (k.castSucc, W.action) (n - W.width) =
          preE7NoPairNoC3FirstOwnerPredicate
              (ownerOrResidualEligible Earlier) W.width
                (k.castSucc, W.action) (n - W.width) := by
        funext L
        simp only [preE7NoPairNoC3CertifiedFirstOwnerPredicate,
          hselected, and_true, Earlier]
      change H ∈ FusionWidthCanonicalFamily
        (preE7NonPairAction W.width W.action) hwn
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierNumericalSns2FamilyAction W.width
              (k.castSucc, W.action) (n - W.width))
      rw [hpredicate]
      simpa only [preE7NonPairFirstOwnerAction] using hold
    · let a : PreE7Sns2OwnedIndex W.width :=
        ⟨k, W.action, hsns2⟩
      let j : GrowingQuotientPhysicalIndex
          (ι := PreE7NumericalSns2Index) 3 n :=
        ⟨⟨W.width, hmem⟩, Sum.inr (Sum.inl a)⟩
      refine ⟨j, ?_⟩
      have hselected : preE7NoPairNoC3SelectedActionEligible
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction W.width
            (k.castSucc, W.action) := by
        rw [preE7NoPairNoC3SelectedActionEligible_castSucc]
        exact Or.inr hsns2
      have hpredicate :
          preE7NoPairNoC3CertifiedFirstOwnerPredicate
              preE7NoPairNoC3EarlierNumericalSns2FamilyAction W.width
                (k.castSucc, W.action) (n - W.width) =
          preE7NoPairNoC3FirstOwnerPredicate
              (ownerOrResidualEligible Earlier) W.width
                (k.castSucc, W.action) (n - W.width) := by
        funext L
        simp only [preE7NoPairNoC3CertifiedFirstOwnerPredicate,
          hselected, and_true, Earlier]
      change H ∈ FusionWidthCanonicalFamily
        (preE7NonPairAction W.width W.action) hwn
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierNumericalSns2FamilyAction W.width
              (k.castSucc, W.action) (n - W.width))
      rw [hpredicate]
      simpa only [preE7NonPairFirstOwnerAction] using hold
  · have howner_eq : owner = Fin.last preE7NoPairNoC3EarlierOwnerCount :=
      Fin.eq_last_of_not_lt ho
    rw [howner_eq] at howner
    obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit H hH.1.1.2
    let w : ℕ := Nat.card o.orbit
    have hw : Nat.card o.orbit = w := rfl
    let outside : OutsideOrbit H := ⟨o, hbad.1, hbad.2.1⟩
    have hw3 : 3 ≤ w := by
      have h := outsideOrbit_card_gt_two H outside
      change 2 < Nat.card o.orbit at h
      omega
    have hwn : w ≤ n := by
      have hcard := Nat.card_le_card_of_injective
        (Subtype.val : o.orbit → Fin n) Subtype.val_injective
      simpa only [hw, Nat.card_fin] using hcard
    obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
      H o hw hbad.1
    have hpre : IsPreE7ActionClass w i :=
      isPreE7ActionClass_of_violation H o hbad i eO himage
    let a : PreE7ActionClass w := ⟨i, hpre⟩
    have hfree : IsPreE7NonPairActionClass w a :=
      isPreE7NonPairActionClass_of_violation H hH.1.1.1.1 hH.1.2 o hbad
        hw hwn i eO himage
    let U : PreE7NonPairActionClass w := ⟨a, hfree⟩
    have hmem : w ∈ Finset.Ico 3 (n + 1) :=
      Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
    let j : GrowingQuotientPhysicalIndex
        (ι := PreE7NumericalSns2Index) 3 n :=
      ⟨⟨w, hmem⟩, Sum.inr (Sum.inr U)⟩
    refine ⟨j, ?_⟩
    have hold := mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier
        (preE7NoPairNoC3EarlierFamilyPredicate_natural _))
      H hH.1.1.1.1 hH.2 (Fin.last preE7NoPairNoC3EarlierOwnerCount)
        howner o hw hwn U eO (by
        simpa only [U, a, preE7NonPairAction, preE7Action] using himage)
    have hselected : preE7NoPairNoC3SelectedActionEligible
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) :=
      (preE7NoPairNoC3SelectedActionEligible_last _ U).2
        (preE7NoPairNoC3TerminalActionEligible_of_violation
          H o hbad U eO (by
            simpa only [U, a, preE7NonPairAction, preE7Action] using himage))
    have hpredicate :
        preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
              (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) (n - w) =
          preE7NoPairNoC3FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w
              (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) (n - w) := by
      funext L
      simp only [preE7NoPairNoC3CertifiedFirstOwnerPredicate,
        hselected, and_true, Earlier]
    change H ∈ FusionWidthCanonicalFamily
      (preE7NonPairAction w U) hwn
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) (n - w))
    rw [hpredicate]
    simpa only [preE7NonPairFirstOwnerAction] using hold

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

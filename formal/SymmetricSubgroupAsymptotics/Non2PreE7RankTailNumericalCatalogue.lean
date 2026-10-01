import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7B6Y1Secondary

/-!
# Numerical catalogue with all three binary rank-tail owners

The ordinary numerical owners, B6, Y1, SNS2, and the terminal retained-cell
lane are kept as a disjoint physical menu.  This prevents any correlated
rank-tail estimate from being coerced into a false pointwise source bound.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

def preE7B6OwnerIndex : Fin preE7NoPairNoC3EarlierOwnerCount :=
  preE7NoPairNoC3EarlierOwnerEquiv.symm .b6

def preE7Y1OwnerIndex : Fin preE7NoPairNoC3EarlierOwnerCount :=
  preE7NoPairNoC3EarlierOwnerEquiv.symm .y1

@[simp] theorem preE7B6OwnerIndex_family :
    preE7NoPairNoC3EarlierOwnerEquiv preE7B6OwnerIndex = .b6 :=
  preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply .b6

@[simp] theorem preE7Y1OwnerIndex_family :
    preE7NoPairNoC3EarlierOwnerEquiv preE7Y1OwnerIndex = .y1 :=
  preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply .y1

abbrev PreE7B6OwnedIndex (w : ℕ) :=
  Σ k : Fin preE7NoPairNoC3EarlierOwnerCount,
    {U : PreE7NonPairActionClass w //
      preE7NoPairNoC3EarlierOwnerEquiv k = .b6 ∧
        Nonempty (PreE7B6SourceData w U)}

abbrev PreE7Y1OwnedIndex (w : ℕ) :=
  Σ k : Fin preE7NoPairNoC3EarlierOwnerCount,
    {U : PreE7NonPairActionClass w //
      preE7NoPairNoC3EarlierOwnerEquiv k = .y1 ∧
        Nonempty (PreE7Y1SourceData w U)}

/-- Ordinary numerical owners, the three correlated rank-tail menus, and
the terminal action.  A named inductive keeps dependent reduction small. -/
inductive PreE7NumericalRankTailIndex (w : ℕ) : Type
  | ordinary : PreE7NumericalOwnedIndex w → PreE7NumericalRankTailIndex w
  | b6 : PreE7B6OwnedIndex w → PreE7NumericalRankTailIndex w
  | y1 : PreE7Y1OwnedIndex w → PreE7NumericalRankTailIndex w
  | sns2 : PreE7Sns2OwnedIndex w → PreE7NumericalRankTailIndex w
  | terminal : PreE7NonPairActionClass w → PreE7NumericalRankTailIndex w
  deriving Fintype

/-- The exact family predicate represented by the disjoint menu. -/
def preE7NoPairNoC3EarlierNumericalRankTailFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (U : PreE7NonPairActionClass w) : Prop :=
  preE7NoPairNoC3EarlierNumericalFamilyAction family w U ∨
    (family = .b6 ∧ Nonempty (PreE7B6SourceData w U)) ∨
    (family = .y1 ∧ Nonempty (PreE7Y1SourceData w U)) ∨
    (family = .sns2 ∧ Nonempty (PreE7Sns2SourceData w U))

def preE7NumericalRankTailOwner {w : ℕ} :
    PreE7NumericalRankTailIndex w →
      Fin (preE7NoPairNoC3EarlierOwnerCount + 1)
  | .ordinary j => j.1.castSucc
  | .b6 j => j.1.castSucc
  | .y1 j => j.1.castSucc
  | .sns2 j => j.1.castSucc
  | .terminal _ =>
      Fin.last preE7NoPairNoC3EarlierOwnerCount

def preE7NumericalRankTailActionClass {w : ℕ} :
    PreE7NumericalRankTailIndex w → PreE7NonPairActionClass w
  | .ordinary j => j.2.1
  | .b6 j => j.2.1
  | .y1 j => j.2.1
  | .sns2 j => j.2.1
  | .terminal U => U

def preE7NumericalRankTailAction (w : ℕ)
    (j : PreE7NumericalRankTailIndex w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  preE7NonPairAction w (preE7NumericalRankTailActionClass j)

def preE7NumericalRankTailPredicate
    (w : ℕ) (j : PreE7NumericalRankTailIndex w) (b : ℕ) :
    Subgroup (preE7NumericalRankTailAction w j ×
      Equiv.Perm (Fin b)) → Prop :=
  preE7NoPairNoC3CertifiedFirstOwnerPredicate
    preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
    (preE7NumericalRankTailOwner j,
      preE7NumericalRankTailActionClass j) b

theorem preE7NumericalRankTailPredicate_natural
    (w : ℕ) (j : PreE7NumericalRankTailIndex w) (b : ℕ) :
    FusionOrbitNatural (preE7NumericalRankTailAction w j)
      (preE7NumericalRankTailPredicate w j b) := by
  cases j with
  | ordinary a =>
      simpa only [preE7NumericalRankTailAction,
        preE7NumericalRankTailPredicate, preE7NumericalRankTailOwner,
        preE7NumericalRankTailActionClass, preE7NonPairFirstOwnerAction] using
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (a.1.castSucc, a.2.1) b)
  | b6 a =>
      simpa only [preE7NumericalRankTailAction,
        preE7NumericalRankTailPredicate, preE7NumericalRankTailOwner,
        preE7NumericalRankTailActionClass, preE7NonPairFirstOwnerAction] using
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (a.1.castSucc, a.2.1) b)
  | y1 a =>
      simpa only [preE7NumericalRankTailAction,
        preE7NumericalRankTailPredicate, preE7NumericalRankTailOwner,
        preE7NumericalRankTailActionClass, preE7NonPairFirstOwnerAction] using
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (a.1.castSucc, a.2.1) b)
  | sns2 a =>
      simpa only [preE7NumericalRankTailAction,
        preE7NumericalRankTailPredicate, preE7NumericalRankTailOwner,
        preE7NumericalRankTailActionClass, preE7NonPairFirstOwnerAction] using
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (a.1.castSucc, a.2.1) b)
  | terminal U =>
      simpa only [preE7NumericalRankTailAction,
        preE7NumericalRankTailPredicate, preE7NumericalRankTailOwner,
        preE7NumericalRankTailActionClass, preE7NonPairFirstOwnerAction] using
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)

theorem preE7NumericalRankTailPredicate_implies_broad
    (w : ℕ) (j : PreE7NumericalRankTailIndex w) (b : ℕ)
    (H : Subgroup (preE7NumericalRankTailAction w j ×
      Equiv.Perm (Fin b))) :
    preE7NumericalRankTailPredicate w j b H →
      preE7NoPairNoC3BroadActionPredicate w
        (preE7NumericalRankTailActionClass j) b H := by
  rintro ⟨⟨⟨hordinary, _⟩, hnoC3⟩, _⟩
  exact ⟨hordinary, hnoC3⟩

private theorem numericalRankTail_selected_castSucc
    {w : ℕ} (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    (U : PreE7NonPairActionClass w)
    (h : preE7NoPairNoC3EarlierNumericalRankTailFamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    preE7NoPairNoC3SelectedActionEligible
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
      (k.castSucc, U) :=
  (preE7NoPairNoC3SelectedActionEligible_castSucc _ k U).2 h

private theorem numericalRankTail_owner_cell
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NoPairNoC3ResidualSubgroupSet n)
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    (hfirst :
      ownerOrResidualEligible
          (preE7NoPairNoC3EarlierFamilyPredicate
            preE7NoPairNoC3EarlierNumericalRankTailFamilyAction) n
          k.castSucc H ∧
        ∀ j, j < k.castSucc →
          ¬ownerOrResidualEligible
            (preE7NoPairNoC3EarlierFamilyPredicate
              preE7NoPairNoC3EarlierNumericalRankTailFamilyAction) n j H)
    (W : PreE7EarlierFamilyOrbit
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) H)
    (a : PreE7NumericalRankTailIndex W.width)
    (haction : preE7NumericalRankTailActionClass a = W.action)
    (haowner : preE7NumericalRankTailOwner a = k.castSucc) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := PreE7NumericalRankTailIndex) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7NumericalRankTailAction preE7NumericalRankTailPredicate j := by
  have hw : Nat.card W.orbit.orbit = W.width := by
    simpa only [Nat.card_fin] using (Nat.card_congr W.chart).symm
  have hwn : W.width ≤ n := by
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : W.orbit.orbit → Fin n) Subtype.val_injective
    simpa only [hw, Nat.card_fin] using hcard
  have hmem : W.width ∈ Finset.Ico 3 (n + 1) :=
    Finset.mem_Ico.mpr ⟨W.width_three, Nat.lt_succ_of_le hwn⟩
  have hold := mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
    (ownerOrResidualEligible
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction))
    (ownerOrResidualEligible_natural
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction)
      (preE7NoPairNoC3EarlierFamilyPredicate_natural
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction))
    H hH.1.1.1.1 hH.2 k.castSucc hfirst W.orbit hw hwn W.action W.chart
      W.action_eq
  let j : GrowingQuotientPhysicalIndex
      (ι := PreE7NumericalRankTailIndex) 3 n :=
    ⟨⟨W.width, hmem⟩, a⟩
  refine ⟨j, ?_⟩
  have hselected := numericalRankTail_selected_castSucc k W.action W.applies
  have hpredicate :
      preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction W.width
            (k.castSucc, W.action) (n - W.width) =
        preE7NoPairNoC3FirstOwnerPredicate
          (ownerOrResidualEligible
            (preE7NoPairNoC3EarlierFamilyPredicate
              preE7NoPairNoC3EarlierNumericalRankTailFamilyAction)) W.width
            (k.castSucc, W.action) (n - W.width) := by
    funext L
    simp only [preE7NoPairNoC3CertifiedFirstOwnerPredicate,
      hselected, and_true]
  change H ∈ FusionWidthCanonicalFamily
    (preE7NumericalRankTailAction W.width a) hwn
      (preE7NumericalRankTailPredicate W.width a (n - W.width))
  rw [← haction, ← haowner] at hold hpredicate
  simpa only [preE7NumericalRankTailAction,
    preE7NumericalRankTailPredicate, hpredicate,
    preE7NonPairFirstOwnerAction] using hold

/-- Literal coverage by the ordinary/B6/Y1/SNS2/terminal menu. -/
theorem preE7NumericalRankTail_physical_cover
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NoPairNoC3ResidualSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := PreE7NumericalRankTailIndex) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7NumericalRankTailAction preE7NumericalRankTailPredicate j := by
  let Earlier := preE7NoPairNoC3EarlierFamilyPredicate
    preE7NoPairNoC3EarlierNumericalRankTailFamilyAction
  obtain ⟨owner, hownerspec⟩ := firstOwned_exists
    (ownerOrResidualEligible Earlier n) H
      (ownerOrResidualEligible_cover Earlier H)
  by_cases ho : owner.val < preE7NoPairNoC3EarlierOwnerCount
  · let k : Fin preE7NoPairNoC3EarlierOwnerCount := ⟨owner.val, ho⟩
    have howner_eq : owner = k.castSucc := by apply Fin.ext; rfl
    have hearlier : Earlier n k H := by
      simpa only [howner_eq, ownerOrResidualEligible_castSucc] using
        hownerspec.1
    obtain ⟨W⟩ := hearlier
    rcases W.applies with hordinary | hb6 | hy1 | hsns2
    · let a : PreE7NumericalOwnedIndex W.width := ⟨k, W.action, hordinary⟩
      exact numericalRankTail_owner_cell H hH k
        (by simpa only [howner_eq] using hownerspec) W (.ordinary a) rfl howner_eq
    · let a : PreE7B6OwnedIndex W.width := ⟨k, W.action, hb6⟩
      exact numericalRankTail_owner_cell H hH k
        (by simpa only [howner_eq] using hownerspec) W (.b6 a)
        rfl howner_eq
    · let a : PreE7Y1OwnedIndex W.width := ⟨k, W.action, hy1⟩
      exact numericalRankTail_owner_cell H hH k
        (by simpa only [howner_eq] using hownerspec) W
        (.y1 a) rfl howner_eq
    · let a : PreE7Sns2OwnedIndex W.width := ⟨k, W.action, hsns2⟩
      exact numericalRankTail_owner_cell H hH k
        (by simpa only [howner_eq] using hownerspec) W
        (.sns2 a) rfl howner_eq
  · have howner_eq : owner = Fin.last preE7NoPairNoC3EarlierOwnerCount :=
      Fin.eq_last_of_not_lt ho
    obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit H hH.1.1.2
    let w : ℕ := Nat.card o.orbit
    let outside : OutsideOrbit H := ⟨o, hbad.1, hbad.2.1⟩
    have hw3 : 3 ≤ w := by
      have h := outsideOrbit_card_gt_two H outside
      change 2 < Nat.card o.orbit at h
      omega
    have hwn : w ≤ n := by
      have hcard := Nat.card_le_card_of_injective
        (Subtype.val : o.orbit → Fin n) Subtype.val_injective
      simpa only [Nat.card_fin] using hcard
    obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
      H o rfl hbad.1
    let a : PreE7ActionClass w :=
      ⟨i, isPreE7ActionClass_of_violation H o hbad i eO himage⟩
    let U : PreE7NonPairActionClass w :=
      ⟨a, isPreE7NonPairActionClass_of_violation H hH.1.1.1.1 hH.1.2
        o hbad rfl hwn i eO himage⟩
    have hmem : w ∈ Finset.Ico 3 (n + 1) :=
      Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
    have hold := mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier
        (preE7NoPairNoC3EarlierFamilyPredicate_natural _))
      H hH.1.1.1.1 hH.2 (Fin.last preE7NoPairNoC3EarlierOwnerCount)
        (by simpa only [← howner_eq] using hownerspec) o rfl hwn U eO
        (by simpa only [U, a, preE7NonPairAction, preE7Action] using himage)
    let x : PreE7NumericalRankTailIndex w :=
      .terminal U
    let j : GrowingQuotientPhysicalIndex
        (ι := PreE7NumericalRankTailIndex) 3 n := ⟨⟨w, hmem⟩, x⟩
    refine ⟨j, ?_⟩
    have hselected := preE7NoPairNoC3SelectedActionEligible_last
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction U
    have hpredicate :
        preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
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
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) (n - w))
    rw [hpredicate]
    simpa only [preE7NonPairFirstOwnerAction] using hold

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

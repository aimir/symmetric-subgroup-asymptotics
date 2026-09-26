import SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16
import SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T26
import SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T27
import SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T35
import SymmetricSubgroupAsymptotics.BinaryCarrierFullMenuHistory

/-! Ordered words in the literal X, J, P and five original degree-sixteen masters.
Every original normal axis is covered by the proved full numerical menu.
Scale one or two belongs to each original factor occurrence, independently
of normal-axis choices. Repeated labels never identify axes or positions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedMenuWord

open BinaryCarrierWord FullSubdirectGoursat JointCapacityRow

inductive Kind
  | x
  | j
  | p
  | degree16 (master : BinaryCarrierMasterWords16.Master)
  deriving DecidableEq, Fintype

/-- This changes no carrier group or permutation tuple. -/
def factor : Kind → Factor
  | .x => BinaryCarrierNormalRows8T26.factor
  | .j => BinaryCarrierNormalRows8T27.factor
  | .p => BinaryCarrierNormalRows8T35.factor
  | .degree16 m => BinaryCarrierMasterWords16.factor m

def word (kinds : List Kind) : List Factor := kinds.map factor

@[simp] theorem word_length (kinds : List Kind) : (word kinds).length = kinds.length := by
  simp only [word, List.length_map]

def factorScale : Kind → ℝ
  | .x => 1
  | .j => 1
  | .p => 1
  | .degree16 _ => 2

def totalScale : List Kind → ℝ
  | [] => 0
  | k :: kinds => factorScale k + totalScale kinds

theorem totalScale_eq_sum (kinds : List Kind) :
    totalScale kinds = (kinds.map factorScale).sum := by
  induction kinds with
  | nil => rfl
  | cons k kinds ih => simp only [totalScale, List.map_cons, List.sum_cons, ih]

/-- The twelve old H16 columns retain their positions; the two additional
star envelopes occupy their specified full-menu positions41 and42. -/
def masterLabel (i : BinaryCarrierMasterMenu.Label) : BinaryCarrierFullMenu.Label :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,41,42] i

theorem masterLabel_envelope (i : BinaryCarrierMasterMenu.Label) :
    BinaryCarrierFullMenu.envelope (masterLabel i) = BinaryCarrierMasterMenu.envelope i := by
  fin_cases i <;> rfl

theorem masterLabel_scale (i : BinaryCarrierMasterMenu.Label) :
    BinaryCarrierFullMenu.physicalScale (masterLabel i) = 2 := by
  fin_cases i <;> rfl

/-- Coverage quantifies the original normal itself. In particular the J
second head is not replaced by its potentially smaller derived maximum. -/
theorem factor_covered (k : Kind) (N : NormalAxis (factor k).Carrier) :
    ∃ label : BinaryCarrierFullMenu.Label,
      (actualRow (A := factor k) N).EffectivelyBoundedBy
        (BinaryCarrierFullMenu.envelope label) ∧
      BinaryCarrierFullMenu.physicalScale label = factorScale k := by
  cases k with
  | x =>
      obtain ⟨i, _, hr, hs⟩ := BinaryCarrierNormalRows8T26.actualRow_displayed N
      refine ⟨BinaryCarrierFullMenu.displayedLabel
        (BinaryCarrierNormalRows8T26.displayedIndex i), ?_, ?_⟩
      · rw [BinaryCarrierFullMenu.envelope_displayed, ← hr]
        exact EffectivelyBoundedBy.refl _
      · exact (BinaryCarrierFullMenu.physicalScale_displayed _).trans hs
  | j =>
      obtain ⟨i, _, hr, hs⟩ := BinaryCarrierNormalRows8T27.actualRow_displayed N
      refine ⟨BinaryCarrierFullMenu.displayedLabel
        (BinaryCarrierNormalRows8T27.displayedIndex i), ?_, ?_⟩
      · rw [BinaryCarrierFullMenu.envelope_displayed, ← hr]
        exact EffectivelyBoundedBy.refl _
      · exact (BinaryCarrierFullMenu.physicalScale_displayed _).trans hs
  | p =>
      obtain ⟨i, _, hr, hs⟩ := BinaryCarrierNormalRows8T35.actualRow_displayed N
      refine ⟨BinaryCarrierFullMenu.displayedLabel
        (BinaryCarrierNormalRows8T35.displayedIndex i), ?_, ?_⟩
      · rw [BinaryCarrierFullMenu.envelope_displayed, ← hr]
        exact EffectivelyBoundedBy.refl _
      · exact (BinaryCarrierFullMenu.physicalScale_displayed _).trans hs
  | degree16 m =>
      obtain ⟨label, hlabel⟩ := BinaryCarrierMasterWords16.covered_factor m N
      refine ⟨masterLabel label, ?_, masterLabel_scale label⟩
      simpa only [masterLabel_envelope] using hlabel

def factorLabel (k : Kind) (N : NormalAxis (factor k).Carrier) :
    BinaryCarrierFullMenu.Label := Classical.choose (factor_covered k N)

theorem factorLabel_bound (k : Kind) (N : NormalAxis (factor k).Carrier) :
    (actualRow (A := factor k) N).EffectivelyBoundedBy
      (BinaryCarrierFullMenu.envelope (factorLabel k N)) :=
  (Classical.choose_spec (factor_covered k N)).1

theorem factorLabel_scale (k : Kind) (N : NormalAxis (factor k).Carrier) :
    BinaryCarrierFullMenu.physicalScale (factorLabel k N) = factorScale k :=
  (Classical.choose_spec (factor_covered k N)).2

/-- A separate choice is made for each original normal in each occurrence. -/
def labels : (kinds : List Kind) → History (word kinds) →
    Fin (word kinds).length → BinaryCarrierFullMenu.Label
  | [], _, i => Fin.elim0 i
  | k :: kinds, h, i => Fin.cases (factorLabel k h.1) (labels kinds h.2) i

def positionScale : (kinds : List Kind) → Fin (word kinds).length → ℝ
  | [], i => Fin.elim0 i
  | k :: kinds, i => Fin.cases (factorScale k) (positionScale kinds) i

theorem labels_bound (kinds : List Kind) : ∀ (h : History (word kinds))
    (i : Fin (word kinds).length),
    (rows h i).EffectivelyBoundedBy (BinaryCarrierFullMenu.envelope (labels kinds h i)) := by
  induction kinds with
  | nil => intro h i; exact Fin.elim0 i
  | cons k kinds ih =>
      intro h i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact factorLabel_bound k h.1
      · exact ih h.2 j

theorem labels_scale (kinds : List Kind) : ∀ (h : History (word kinds))
    (i : Fin (word kinds).length),
    BinaryCarrierFullMenu.physicalScale (labels kinds h i) = positionScale kinds i := by
  induction kinds with
  | nil => intro h i; exact Fin.elim0 i
  | cons k kinds ih =>
      intro h i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact factorLabel_scale k h.1
      · exact ih h.2 j

/-- The total is computed from the original ordered word, not from distinct
labels or from a count of numerical row types. -/
theorem positionScale_sum (kinds : List Kind) :
    (∑ i, positionScale kinds i) = totalScale kinds := by
  induction kinds with
  | nil => change (∑ i : Fin 0, positionScale [] i) = 0; simp
  | cons k kinds ih =>
      change (∑ i : Fin ((word kinds).length + 1),
        Fin.cases (factorScale k) (positionScale kinds) i) =
          factorScale k + totalScale kinds
      rw [Fin.sum_univ_succ]
      exact congrArg (fun t : ℝ => factorScale k + t) ih

theorem labels_scale_sum (kinds : List Kind) (h : History (word kinds)) :
    (∑ i, BinaryCarrierFullMenu.physicalScale (labels kinds h i)) = totalScale kinds := by
  simp only [labels_scale]
  exact positionScale_sum kinds

/-- All numerical hypotheses are supplied by proved actual row coverage and
the structural scale identity, uniformly for every original history. -/
def certifiedHistoryRows (kinds : List Kind) :
    CertifiedHistoryRows (word kinds) (totalScale kinds) :=
  BinaryCarrierFullMenuHistory.certifiedHistoryRows (word kinds) (totalScale kinds)
    (labels kinds) (labels_bound kinds) (labels_scale_sum kinds)

theorem factor_card_le (k : Kind) : Nat.card (factor k).Carrier ≤ 2 ^ 12 := by
  cases k with
  | x =>
      change Nat.card BinaryCarrierNormalRows8T26.Original ≤ 2 ^ 12
      exact BinaryMenuCayley8T26.exact_card.le.trans (by decide)
  | j =>
      change Nat.card BinaryCarrierNormalRows8T27.Original ≤ 2 ^ 12
      exact BinaryMenuCayley8T27.exact_card.le.trans (by decide)
  | p =>
      change Nat.card BinaryCarrierNormalRows8T35.Original ≤ 2 ^ 12
      exact BinaryMenuCayley8T35.exact_card.le.trans (by decide)
  | degree16 m => exact BinaryCarrierMasterWords16.factor_card_le m

theorem orderBound (kinds : List Kind) : OrderBound (word kinds) 12 := by
  induction kinds with
  | nil => exact True.intro
  | cons k kinds ih => exact ⟨factor_card_le k, ih⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedMenuWord

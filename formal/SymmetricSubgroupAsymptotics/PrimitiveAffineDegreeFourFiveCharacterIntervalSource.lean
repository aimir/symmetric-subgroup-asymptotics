import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFiveWholeSocle
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval
import SymmetricSubgroupAsymptotics.CompleteCharacterIntervalTailBound
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge

/-!
# Character-interval wrappers for affine degrees four and five

This file is deliberately thin.  It packages a proved whole-socle normal
generator bound on the literal quotients below the actual translation
intersection.  The finite character coefficient is retained as a constant
tail and discharged by the global bounded-width polynomial envelope, rather
than by a false pointwise normalization on each literal action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev LiteralNormalAxis45 (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- One slot for two and three blocks, and the rounded half-block budget
thereafter. -/
def degreeFourSocleSlots (s : ℕ) : ℕ :=
  if s = 2 ∨ s = 3 then 1 else (s + 1) / 2

@[simp] theorem degreeFourSocleSlots_two : degreeFourSocleSlots 2 = 1 := by
  simp [degreeFourSocleSlots]

@[simp] theorem degreeFourSocleSlots_three : degreeFourSocleSlots 3 = 1 := by
  simp [degreeFourSocleSlots]

theorem degreeFourSocleSlots_cast_le {s : ℕ} (hs : 2 ≤ s) :
    (degreeFourSocleSlots s : ℝ) ≤ ((s : ℝ) + 1) / 2 := by
  by_cases hsmall : s = 2 ∨ s = 3
  · rcases hsmall with rfl | rfl <;> norm_num [degreeFourSocleSlots]
  · simp only [degreeFourSocleSlots, if_neg hsmall]
    calc
      (((s + 1) / 2 : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) / 2 :=
        Nat.cast_div_le
      _ = ((s : ℝ) + 1) / 2 := by norm_num

private theorem logb_two_five_lt_seven_thirds :
    Real.logb 2 5 < (7 : ℝ) / 3 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
    simpa only [mul_comm] using hlog)

/-- Three nonzero vectors per binary affine block. -/
theorem degreeFour_quotientDegree_eq_three_mul
    (hr : Nat.card block.Fibre = 4) :
    quotientDegree block = 3 * Nat.card block.Points := by
  rw [quotientDegree_eq, hr]

/-- Four nonzero vectors per affine block of degree five. -/
theorem degreeFive_quotientDegree_eq_four_mul
    (hr : Nat.card block.Fibre = 5) :
    quotientDegree block = 4 * Nat.card block.Points := by
  rw [quotientDegree_eq, hr]

theorem degreeFour_comparator_margin_of_width
    (s : ℕ) (hs : 2 ≤ s) :
    preE7CharacterRho * (4 * s) ≤
      ((evenWidth (4 * s) : ℝ) - (max 2 (3 * s) : ℕ)) / 8 := by
  have hhalf : halfDegree (4 * s) = 2 * s := by
    unfold halfDegree
    omega
  have heven : evenWidth (4 * s) = 4 * s := by
    unfold evenWidth
    rw [hhalf]
    omega
  have hmax : max 2 (3 * s) = 3 * s := max_eq_right (by omega)
  rw [heven, hmax]
  unfold preE7CharacterRho
  push_cast
  nlinarith

theorem degreeFour_theta_window_of_width
    (s : ℕ) (hs : 2 ≤ s) :
    (degreeFourSocleSlots s : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow (4 * s) := by
  have hlog := logb_two_five_lt_seven_thirds
  have hhalf : halfDegree (4 * s) = 2 * s := by
    unfold halfDegree
    omega
  by_cases hsmall : s = 2 ∨ s = 3
  · rcases hsmall with rfl | rfl
    · norm_num [degreeFourSocleSlots, preE7CharacterWindow,
        preE7CharacterRho, halfDegree] at hlog ⊢
      linarith
    · norm_num [degreeFourSocleSlots, preE7CharacterWindow,
        preE7CharacterRho, halfDegree] at hlog ⊢
      linarith
  · have hs4 : 4 ≤ s := by omega
    have hslots := degreeFourSocleSlots_cast_le hs
    have hlogDiv : Real.logb 2 5 / 3 ≤ (7 : ℝ) / 9 := by
      linarith
    have hlogNonneg : 0 ≤ Real.logb 2 5 / 3 :=
      (div_pos (Real.logb_pos (by norm_num) (by norm_num))
        (by norm_num)).le
    have htheta :
        (degreeFourSocleSlots s : ℝ) * (Real.logb 2 5 / 3) ≤
          (((s : ℝ) + 1) / 2) * ((7 : ℝ) / 9) :=
      mul_le_mul hslots hlogDiv hlogNonneg (by positivity)
    apply htheta.trans
    rw [preE7CharacterWindow, hhalf]
    unfold preE7CharacterRho
    push_cast
    have hs4R : (4 : ℝ) ≤ s := by exact_mod_cast hs4
    nlinarith

/-- Degree-four literal character interval. -/
noncomputable def degreeFourSocleGeneratorInterval
    (hgenerators : ∀ N : LiteralNormalAxis45
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (degreeFourSocleSlots (Nat.card block.Points))) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) where
  E := E block P
  quotientDegree := quotientDegree block
  quotientAction := quotientAction block P
  quotientAction_injective := quotientAction_injective block P
  slots := degreeFourSocleSlots (Nat.card block.Points)
  quotientSocleGenerators := hgenerators

/-- Degree-five literal character interval, using the one-slot whole-socle
bound supplied by the structural lane. -/
noncomputable def degreeFiveSocleGeneratorInterval
    (hgenerators : ∀ N : LiteralNormalAxis45
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 1) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) where
  E := E block P
  quotientDegree := quotientDegree block
  quotientAction := quotientAction block P
  quotientAction_injective := quotientAction_injective block P
  slots := 1
  quotientSocleGenerators := hgenerators

noncomputable def degreeFourCompleteCharacterInterval
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgenerators : ∀ N : LiteralNormalAxis45
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (degreeFourSocleSlots (Nat.card block.Points))) :
    CompleteCharacterIntervalData (preE7NonPairAction w U) :=
  (degreeFourSocleGeneratorInterval block P hgenerators
    ).toCompleteCharacterIntervalData hZmud

noncomputable def degreeFiveCompleteCharacterInterval
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgenerators : ∀ N : LiteralNormalAxis45
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 1) :
    CompleteCharacterIntervalData (preE7NonPairAction w U) :=
  (degreeFiveSocleGeneratorInterval block P hgenerators
    ).toCompleteCharacterIntervalData hZmud

/-- Padded degree of a complete character interval.  This copy of the
standard padding data deliberately does not include a pointwise bound on
the finite tail constant: bounded widths absorb that constant only after
the action catalogue is summed. -/
def boundedCharacterSourceDegree
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U)) : ℕ :=
  max 2 D.quotientDegree

def boundedCharacterDegree
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U)) : ℕ :=
  paddedComparatorDegree preE7CharacterRho
    (boundedCharacterSourceDegree D) w

def boundedCharacterDelta
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U)) : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0
    (boundedCharacterSourceDegree D) w

def boundedCharacterCutoff
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U)) : ℝ :=
  (boundedCharacterDegree D : ℝ) / 8 + boundedCharacterDelta D / 2

theorem boundedCharacter_quotientDegree_le_degree
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U)) :
    D.quotientDegree ≤ boundedCharacterDegree D :=
  (le_max_right 2 D.quotientDegree).trans (le_max_left _ _)

/-- The complete-source comparator underneath the bounded-width wrapper.
Its tail coefficient is the literal finite character constant. -/
noncomputable def boundedCompleteCharacterCertificate
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U))
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7CompleteSourceComparatorCertificate family w U where
  R := preE7NonPairAction w U ⧸ D.E
  groupR := inferInstance
  finiteR := inferInstance
  v := boundedCharacterDegree D
  action :=
    (characterComparatorPadHom
      (boundedCharacter_quotientDegree_le_degree D)).comp D.quotientAction
  action_injective :=
    (characterComparatorPadHom_injective
      (boundedCharacter_quotientDegree_le_degree D)).comp
        D.quotientAction_injective
  D := fun _ => 1
  T := fun _ => D.tailConstant
  eta := 0
  delta := boundedCharacterDelta D
  cutoff := boundedCharacterCutoff D
  alpha := boundedCharacterCutoff D
  theta := D.theta
  alpha_eq := by simp
  D_nonneg := fun _ => zero_le_one
  T_nonneg := fun _ => D.tailConstant_nonneg
  broad_source_envelope := by
    intro b J
    simpa using D.completeSource_envelope lit
      (preE7NoPairNoC3BroadActionPredicate w U b) J

theorem boundedCompleteCharacterParameters
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U))
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
        (boundedCharacterSourceDegree D : ℕ)) / 8)
    (htheta : D.theta ≤ preE7CharacterWindow w) :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (boundedCompleteCharacterCertificate D lit family).v
      (boundedCompleteCharacterCertificate D lit family).eta
      (boundedCompleteCharacterCertificate D lit family).delta
      (boundedCompleteCharacterCertificate D lit family).cutoff
      (boundedCompleteCharacterCertificate D lit family).alpha
      (boundedCompleteCharacterCertificate D lit family).theta := by
  simpa [boundedCompleteCharacterCertificate, boundedCharacterDegree,
    boundedCharacterDelta, boundedCharacterCutoff] using
    (preE7Padded_entryParameters_withTail
      (w := w) (v0 := boundedCharacterSourceDegree D)
      (eta := (0 : ℝ)) (theta := D.theta)
      (by norm_num) (le_max_left 2 D.quotientDegree)
      (by simpa using hmargin) htheta)

/-- Bounded-width numerical package for a complete character interval.
The main coefficient is one.  The literal finite tail constant is retained
as a degree-zero polynomial and absorbed by the global finite-index maximum. -/
noncomputable def boundedCompleteCharacterNumericalPackage
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U))
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
        (boundedCharacterSourceDegree D : ℕ)) / 8)
    (htheta : D.theta ≤ preE7CharacterWindow w)
    (hwidth : w ≤ 12288) :
    PreE7EarlierNumericalPackage family w U := by
  let C := boundedCompleteCharacterCertificate D lit family
  refine
    { package := C.localPackage
      parameters := ?_
      main_total_growth := .inl ?_
      tail_total_growth := .inr ?_ }
  · simpa only [C] using
      boundedCompleteCharacterParameters D lit family hmargin htheta
  · intro b
    change (1 : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
    exact Real.one_le_rpow (by norm_num) (by positivity)
  · refine ⟨hwidth, D.tailConstant, 0, D.tailConstant_nonneg, ?_⟩
    intro b
    change D.tailConstant ≤ D.tailConstant * (1 + (b : ℝ)) ^ 0
    simp

noncomputable def boundedCompleteCharacterSource
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U))
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
        (boundedCharacterSourceDegree D : ℕ)) / 8)
    (htheta : D.theta ≤ preE7CharacterWindow w)
    (hwidth : w ≤ 12288) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inl (.ordinary family (.package
    (boundedCompleteCharacterNumericalPackage D lit family
      hmargin htheta hwidth)))

/-- Final degree-four source.  Its literal finite tail constant is paid by
the global bounded-width maximum, exactly once for the finite affine-frame
band `s ≤ 3072`. -/
noncomputable def degreeFourCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hgenerators : ∀ N : LiteralNormalAxis45
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (degreeFourSocleSlots (Nat.card block.Points)))
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hsUpper : Nat.card block.Points ≤ 3072) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let D := degreeFourCompleteCharacterInterval block P hZmud hgenerators
  apply boundedCompleteCharacterSource D lit family
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    let s := Nat.card block.Points
    have hwNat : w = 4 * s := by
      calc
        w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
        _ = 4 * s := by rw [hr]
    have heven : evenWidth w = evenWidth (4 * s) :=
      congrArg evenWidth hwNat
    have hq : max 2 (quotientDegree block) = max 2 (3 * s) := by
      rw [degreeFour_quotientDegree_eq_three_mul block hr]
    calc
      preE7CharacterRho * (w : ℝ) =
          preE7CharacterRho * (4 * s : ℕ) := by rw [hwNat]
      _ ≤ ((evenWidth (4 * s) : ℝ) - (max 2 (3 * s) : ℕ)) / 8 :=
        by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using
            degreeFour_comparator_margin_of_width s hs
      _ = ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8 := by
        rw [heven, hq]
  · change (degreeFourSocleSlots (Nat.card block.Points) : ℝ) *
      (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w
    let s := Nat.card block.Points
    have hwNat : w = 4 * s := by
      calc
        w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
        _ = 4 * s := by rw [hr]
    have hwindow : preE7CharacterWindow w =
        preE7CharacterWindow (4 * s) :=
      congrArg preE7CharacterWindow hwNat
    exact (degreeFour_theta_window_of_width s hs).trans_eq hwindow.symm
  · calc
      w = 4 * Nat.card block.Points := by
        calc
          w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
          _ = 4 * Nat.card block.Points := by rw [hr]
      _ ≤ 4 * 3072 := Nat.mul_le_mul_left 4 hsUpper
      _ = 12288 := by norm_num

/-- Final degree-five source, with its finite coefficient paid once by the
global bounded-width envelope. -/
noncomputable def degreeFiveCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3)
    (i₀ : block.Points) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  let hgenerators := degreeFive_retainedSocleGeneratorMenu
    hTraceyHalf hTraceyPerm block P hr hs i₀
  let D := degreeFiveCompleteCharacterInterval block P hZmud hgenerators
  apply boundedCompleteCharacterSource D lit family
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    have hw := width_eq block
    have hq := degreeFive_quotientDegree_eq_four_mul block hr
    rcases hs with hs | hs
    · have hw10 : w = 10 := by
        calc
          w = Nat.card block.Fibre * Nat.card block.Points := hw
          _ = 5 * 2 := by rw [hr, hs]
          _ = 10 := by norm_num
      have hq8 : quotientDegree block = 8 := by rw [hq, hs]
      have heven : evenWidth w = evenWidth 10 := congrArg evenWidth hw10
      rw [heven, hq8]
      norm_num [hw10, preE7CharacterRho, evenWidth, halfDegree]
    · have hw15 : w = 15 := by
        calc
          w = Nat.card block.Fibre * Nat.card block.Points := hw
          _ = 5 * 3 := by rw [hr, hs]
          _ = 15 := by norm_num
      have hq12 : quotientDegree block = 12 := by rw [hq, hs]
      have heven : evenWidth w = evenWidth 15 := congrArg evenWidth hw15
      rw [heven, hq12]
      norm_num [hw15, preE7CharacterRho, evenWidth, halfDegree]
  · have htheta :
        Real.logb 2 5 / 3 ≤ preE7CharacterWindow w := by
      have hw := width_eq block
      have hlog := logb_two_five_lt_seven_thirds
      rcases hs with hs | hs
      · have hw10 : w = 10 := by
          calc
            w = Nat.card block.Fibre * Nat.card block.Points := hw
            _ = 5 * 2 := by rw [hr, hs]
            _ = 10 := by norm_num
        have hwindow : preE7CharacterWindow w =
            preE7CharacterWindow 10 := congrArg preE7CharacterWindow hw10
        rw [hwindow]
        norm_num [preE7CharacterWindow, preE7CharacterRho,
          halfDegree] at hlog ⊢
        linarith
      · have hw15 : w = 15 := by
          calc
            w = Nat.card block.Fibre * Nat.card block.Points := hw
            _ = 5 * 3 := by rw [hr, hs]
            _ = 15 := by norm_num
        have hwindow : preE7CharacterWindow w =
            preE7CharacterWindow 15 := congrArg preE7CharacterWindow hw15
        rw [hwindow]
        norm_num [preE7CharacterWindow, preE7CharacterRho,
          halfDegree] at hlog ⊢
        linarith
    simpa only [D, degreeFiveCompleteCharacterInterval,
      SocleGeneratorCharacterIntervalData.toCompleteCharacterIntervalData_theta,
      degreeFiveSocleGeneratorInterval, Nat.cast_one, one_mul] using htheta
  · have hw := width_eq block
    rcases hs with hs | hs
    · calc
        w = 5 * 2 := by simpa only [hr, hs] using hw
        _ ≤ 12288 := by norm_num
    · calc
        w = 5 * 3 := by simpa only [hr, hs] using hw
        _ ≤ 12288 := by norm_num

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

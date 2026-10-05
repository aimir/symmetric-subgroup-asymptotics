import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineNonzeroCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineCoefficient

/-!
# Uniform degree-nine source from the whole linear-core split

The split on the whole actual linear block kernel closes all five bounded
block counts with one slot budget `s + floor(s/3)`.  In the zero-kernel
branch this is the literal ternary filtration.  In the nonzero branch the
whole-kernel Clifford theorem gives the sharper `s` bound, which is padded
to the common budget.  The common numerical window is checked directly for
`s = 2,3,4,6,12`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev LiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem degreeNine_three_logFive_lt_seven :
    3 * Real.logb 2 5 < 7 := by
  have hp : ((5 : ℝ) ^ 3) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  exact_mod_cast hl

/-- The enlarged zero-kernel budget lies inside the cold window at every
exceptional degree-nine block count. -/
theorem degreeNine_wholeCore_theta_window
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12) :
    ((Nat.card block.Points + Nat.card block.Points / 3 : ℕ) : ℝ) *
        (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w := by
  have hw := width_eq block
  have hlog := degreeNine_three_logFive_lt_seven
  have hrF : Fintype.card block.Fibre = 9 := by
    simpa only [Nat.card_eq_fintype_card] using hr
  rcases hs with hs | hs | hs | hs | hs
  all_goals
    rw [Nat.card_eq_fintype_card] at hs
    rw [Nat.card_eq_fintype_card, hs]
    norm_num [hrF, hs] at hw
    norm_num [hw, preE7CharacterWindow, preE7CharacterRho,
      halfDegree] at hlog ⊢
    linarith

/-- Uniform whole-socle tuple for all five degree-nine exceptional cells. -/
theorem degreeNineWholeCore_socleGenerators
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1)
      (Nat.card block.Points + Nat.card block.Points / 3) := by
  by_cases hK : degreeNineLinearBlockKernel block P = ⊥
  · exact degreeNineZeroWholeCore_socleGenerators block P hTraceyHalf
      hTraceyPerm hgen hs hr i₀ hK N
  · have hsharp := degreeNineNonzeroWholeCore_socleGenerators
      block P hClifford hTraceyHalf hTraceyPerm hgen hs hr i₀ hK N
        hretained
    apply (socleNormalGeneratorBound_iff_normalGen_le _ _).2
    exact ((socleNormalGeneratorBound_iff_normalGen_le _ _).1 hsharp).trans
      (Nat.le_add_right _ _)

/-- Uniform generator function in the exact form consumed by the character
interval constructor. -/
theorem degreeNineWholeCore_allNormalAxes
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points) :
    ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
      SocleNormalGeneratorBound
        (preE7NonPairAction w U ⧸ N.1)
        (Nat.card block.Points + Nat.card block.Points / 3) := by
  intro N hretained
  exact degreeNineWholeCore_socleGenerators block P hClifford hTraceyHalf
    hTraceyPerm hgen hs hr i₀ N hretained

/-- Non-coefficient numerics for the uniform whole-core interval. -/
noncomputable def degreeNineWholeCoreCompleteCharacterNumerics
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12)
    (i₀ : block.Points)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7CompleteCharacterIntervalNumerics
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points + Nat.card block.Points / 3)
        (degreeNineWholeCore_allNormalAxes block P hClifford hTraceyHalf
          hTraceyPerm hgen block.degrees_ge_two.2 hr i₀)) := by
  refine
    { comparator_margin := ?_
      theta_window := ?_
      tail_total_bound := ?_ }
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    exact degreeNine_comparator_margin block hr hs
  · change
      ((Nat.card block.Points + Nat.card block.Points / 3 : ℕ) : ℝ) *
          (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w
    exact degreeNine_wholeCore_theta_window block hr hs
  · exact degreeNine_tailConstant_le_menuMass block P _ hgen hr hs

/-- Counting-ready degree-nine source, with no project-owned structural
input beyond the proved whole-kernel split. -/
noncomputable def degreeNineWholeCoreCharacterIntervalSource
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12)
    (i₀ : block.Points) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  (degreeNineWholeCoreCompleteCharacterNumerics block P hClifford
    hTraceyHalf hTraceyPerm hgen hr hs i₀ hZmud
  ).toRankTailSourceOrYonedaTop lit family

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

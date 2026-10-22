import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCoefficient
import SymmetricSubgroupAsymptotics.ActualWreathSemisimpleCoefficientAutSquare

/-! The actual original-block affine component transfer with exactly the
 checked coefficient, from AutSquare rather than a generating-set input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource
variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
include P
/-- The actual local-chief coefficient is bounded by the explicit affine
component exponent.  This is the construction-level estimate later summed
over the growing owner menu. -/
theorem tower_coefficient_le_explicit_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound) (b : ℕ) :
    let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    T.envelope.coefficient b ≤
      (2 : ℝ) ^ affineComponentCoefficientExponent
        (Nat.card block.Fibre) (Nat.card block.Points) w b := by
  let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  let m : ℝ := (Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) ^ 2
  obtain ⟨he, hs⟩ := tower_logBudgets_le_logSquare
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  have he0 := T.elementaryLogBudget_nonneg
  have hs0 := T.semisimpleLogBudget_nonneg
  have hm0 : 0 ≤ m := by positivity
  have hsBlocks : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hraw := T.envelope_coefficient_le_two_rpow_linearSemisimpleBudget_of_autSquare
    hAut hsBlocks b
  have hraw' : T.envelope.coefficient b ≤ (2 : ℝ) ^
        (4 * (Nat.card block.Points : ℝ) ^ 2 /
              Real.sqrt (Real.logb 2 (Nat.card block.Points)) *
                T.elementaryLogBudget ^ 2 +
          (4 * Nat.card block.Points * w /
                Real.sqrt (Real.logb 2 (Nat.card block.Points)) +
              Nat.card block.Points *
                (traceyPermutationGeneratorCeiling w + 2) + w) *
            T.elementaryLogBudget +
          3 * Nat.card block.Points * T.semisimpleLogBudget +
          2 * Nat.card block.Points * T.semisimpleLogBudget *
            Real.logb 2 (b + 1)) := by
    simpa only [Fintype.card_eq_nat_card, initialState] using hraw
  refine hraw'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have hsqrt : 0 < Real.sqrt (Real.logb 2 (Nat.card block.Points)) :=
    Real.sqrt_pos.2 (Real.logb_pos (by norm_num)
      (by exact_mod_cast block.degrees_ge_two.2))
  have hA0 : 0 ≤ 4 * (Nat.card block.Points : ℝ) ^ 2 /
      Real.sqrt (Real.logb 2 (Nat.card block.Points)) := by positivity
  have hB0 : 0 ≤ 4 * (Nat.card block.Points : ℝ) * w /
        Real.sqrt (Real.logb 2 (Nat.card block.Points)) +
      Nat.card block.Points * (traceyPermutationGeneratorCeiling w + 2) + w := by
    positivity
  have hlog0 : 0 ≤ Real.logb 2 (b + 1) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ b + 1 by omega))
  have heSq : T.elementaryLogBudget ^ 2 ≤ m ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left heSq hA0
  have h2 := mul_le_mul_of_nonneg_left he hB0
  have h3 := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 3 * (Nat.card block.Points : ℝ) by positivity)
  have h4 := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * (Nat.card block.Points : ℝ) *
      Real.logb 2 (b + 1) by positivity)
  dsimp [affineComponentCoefficientExponent, m]
  nlinarith

variable (S : ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P)

/-- The finite coefficient is a theorem of the literal affine tower.  Its
width-only part is the standard subquadratic cost used by the global menu. -/
theorem coefficient_bound_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound) (b : ℕ) :
    (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).coefficient b ≤
      (2 : ℝ) ^
        (affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  have hraw := tower_coefficient_le_explicit_of_autSquare
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hAut b
  have hexp := affineComponentCoefficientExponent_le_widthCost
    (Nat.card block.Fibre) (Nat.card block.Points) w b
    block.degrees_ge_two.1 block.degrees_ge_two.2 (width_eq block)
  exact hraw.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

/-- The source margin plus the coefficient theorem give the exact
construction-facing record required by the affine-aware catalogue bridge. -/
noncomputable def preE7Margin_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound) :
    RelativeCompleteSourceEnvelope.PreE7Margin
      (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P) where
  eta_nonneg := by
    simpa only [envelope, tower] using
      ActualWreathCompressionTower.envelope_eta_nonneg
        (tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P)
  seedDegree_two_le := by
    rw [envelope, ActualWreathCompressionTower.envelope_v]
    simpa using block.degrees_ge_two.2
  margin := by
    simpa only [envelope, tower, trace, capacity] using S.margin
  coefficient_bound := coefficient_bound_of_autSquare
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hAut

/-- **Imprimitive affine-component transfer.**  The component-native margin
is transported through the actual block system; the complete coefficient
and its subquadratic menu growth are proved rather than assumed. -/
noncomputable def toAmbientSource_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P)
      (preE7Margin_of_autSquare hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P S hAut)

end ComponentSource

/-- Function spelling used by the primitive-catalogue consumer assembly. -/
noncomputable def imprimitiveAffineComponentTransfer_of_autSquare
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hAut : FiniteSimpleAutomorphismSquareBound)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (S : ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  ComponentSource.toAmbientSource_of_autSquare
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P S hAut

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

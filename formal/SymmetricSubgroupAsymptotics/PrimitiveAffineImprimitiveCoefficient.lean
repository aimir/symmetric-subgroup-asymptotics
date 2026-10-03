import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentTransfer
import SymmetricSubgroupAsymptotics.ActualWreathSemisimpleCoefficient

/-!
# Uniform coefficient of an actual imprimitive affine component

The actual local-chief tower retains the elementary and nonabelian order
budgets separately.  Their sum is the exact base-two logarithm of the
literal primitive component.  The primitive affine order theorem therefore
bounds both budgets by the logarithmic-square expression in the literal
block degree, without replacing the component by a catalogue action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Explicit coefficient exponent for a primitive affine component of local
degree `r`, transported through `s` actual blocks inside ambient degree `w`.
The first two terms are the elementary-chief cost; the last two are the
linear semisimple constant and its source polynomial. -/
noncomputable def affineComponentCoefficientExponent
    (r s w b : ℕ) : ℝ :=
  let m : ℝ := (Nat.log 2 r + 1 : ℕ) ^ 2
  4 * (s : ℝ) ^ 2 / Real.sqrt (Real.logb 2 s) * m ^ 2 +
    (4 * s * w / Real.sqrt (Real.logb 2 s) +
        s * (traceyPermutationGeneratorCeiling w + 2) + w) * m +
    3 * s * m + 2 * s * m * Real.logb 2 (b + 1)

namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

include P

/-- The logarithm of the literal component order is at most the square of
one plus the binary logarithm of the literal block degree. -/
theorem component_logb_card_le_logSquare :
    Real.logb 2 (Nat.card block.Component) ≤
      ((Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) : ℝ) ^ 2 := by
  let x : block.Fibre := ⟨basePoint, block.map_base⟩
  let r := Nat.card block.Fibre
  let l := Nat.log 2 r
  have hrUpper : r ≤ 2 ^ (l + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r).le
  have hcard : Nat.card block.Component ≤
      2 ^ ((Nat.log 2 (Nat.card block.Fibre) + 1) ^ 2) := by
    calc
      Nat.card block.Component ≤ Nat.card block.Fibre *
          Nat.card block.Fibre ^ Nat.log 2 (Nat.card block.Fibre) :=
        P.card_le_domain_pow_log x
      _ = r ^ (l + 1) := by simp [r, l, pow_succ']
      _ ≤ (2 ^ (l + 1)) ^ (l + 1) := Nat.pow_le_pow_left hrUpper _
      _ = 2 ^ ((Nat.log 2 (Nat.card block.Fibre) + 1) ^ 2) := by
        dsimp [l, r]
        rw [pow_two, pow_mul]
  have hposR : (0 : ℝ) < Nat.card block.Component := by
    exact_mod_cast Nat.card_pos (α := block.Component)
  have hcardR : (Nat.card block.Component : ℝ) ≤
      (2 ^ ((Nat.log 2 (Nat.card block.Fibre) + 1) ^ 2) : ℕ) := by
    exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hposR hcardR
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), one_mul, mul_one,
    Nat.cast_add, Nat.cast_one] using hlog

/-- Both retained tower budgets are bounded by the same literal local-order
budget. -/
theorem tower_logBudgets_le_logSquare :
    let T := tower hTraceyHalf hTraceyLog hTraceyPerm block
    T.elementaryLogBudget ≤
        ((Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) : ℝ) ^ 2 ∧
      T.semisimpleLogBudget ≤
        ((Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) : ℝ) ^ 2 := by
  let T := tower hTraceyHalf hTraceyLog hTraceyPerm block
  have hsum := T.elementaryLogBudget_add_semisimpleLogBudget_eq_card
  change T.elementaryLogBudget + T.semisimpleLogBudget =
    Real.logb 2 (Nat.card block.Component) at hsum
  have he0 := T.elementaryLogBudget_nonneg
  have hs0 := T.semisimpleLogBudget_nonneg
  have htotal := component_logb_card_le_logSquare block P
  constructor <;> nlinarith

/-- The actual local-chief coefficient is bounded by the explicit affine
component exponent.  This is the construction-level estimate later summed
over the growing owner menu. -/
theorem tower_coefficient_le_explicit
    (hgen : FiniteSimpleTwoGeneratorBound) (b : ℕ) :
    let T := tower hTraceyHalf hTraceyLog hTraceyPerm block
    T.envelope.coefficient b ≤
      (2 : ℝ) ^ affineComponentCoefficientExponent
        (Nat.card block.Fibre) (Nat.card block.Points) w b := by
  let T := tower hTraceyHalf hTraceyLog hTraceyPerm block
  let m : ℝ := (Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) ^ 2
  obtain ⟨he, hs⟩ := tower_logBudgets_le_logSquare
    hTraceyHalf hTraceyLog hTraceyPerm block P
  have he0 := T.elementaryLogBudget_nonneg
  have hs0 := T.semisimpleLogBudget_nonneg
  have hm0 : 0 ≤ m := by positivity
  have hsBlocks : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hraw := T.envelope_coefficient_le_two_rpow_linearSemisimpleBudget
    hgen hsBlocks b
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

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end

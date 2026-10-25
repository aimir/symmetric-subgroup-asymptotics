import SymmetricSubgroupAsymptotics.CFSGTitsAmbientPairAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.OuterAutomorphismOvergroupNormalization
import SymmetricSubgroupAsymptotics.CFSGTitsLeastIndexFourteen
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! Actual Tits outer classes are bounded by twice the cardinality of
the literal opposed-Sylow pair stabilizer. Ambient conjugation is charged
through the proved derived index at most two. The pair stabilizer's
rigidity is NOT proved or installed as a T1 assumption here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerOuterBound
open PrimitiveSocleRawStructure CFSGTitsAmbientPairAlignment
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourAmbientCentralQuotientAction

private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private instance titsFinite : Finite CFSG.Models.Tits :=
  Finite.of_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)

theorem outer_card_le_twice_pairStabilizer :
    Nat.card (Outer CFSG.Models.Tits) ≤ 2 * Nat.card pairStabilizer := by
  have hinner : ∀ a ∈ commutator (originalModelFixed 0),
      ambientAction 0 a ∈ PrimitiveSocleRawStructure.Inner CFSG.Models.Tits := by
    intro a ha
    exact ⟨derivedReeHom 0 ⟨a, ha⟩,
      (ambientAction_of_derived 0 ⟨a, ha⟩).symm⟩
  have h := OuterAutomorphismOvergroupNormalization.outer_card_le_index_mul_stabilizer
    (ambientAction 0) (commutator (originalModelFixed 0)) hinner
    pairStabilizer ambient_normalization_cover
  exact h.trans (Nat.mul_le_mul_right _ CFSGReeFFourBinarySylowExtensions.derived_index_le_two)

/-- A sufficient remaining finite target, not an assumed T1 input.
The literal pair-stabilizer estimate must still be proved. -/
theorem outer_budget_of_pairStabilizer_card_le_four
    [IsSimpleGroup CFSG.Models.Tits]
    (ell : ℕ) (hell : LeastProperIndex CFSG.Models.Tits ell)
    (hS : Nat.card pairStabilizer ≤ 4) :
    SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Tits)) := by
  have h14 := CFSGTitsLeastIndexFourteen.least_index_fourteen_le ell hell
  have hout : Nat.card (Outer CFSG.Models.Tits) ≤ 8 :=
    outer_card_le_twice_pairStabilizer.trans
      (by simpa only [show (2:ℕ)*4=8 by decide] using Nat.mul_le_mul_left 2 hS)
  have h8R : (8:ℝ) ≤ (ell:ℝ) := by exact_mod_cast (show 8 ≤ ell by omega)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (by norm_num : (0:ℝ) < 8) h8R
  have hthree : (3:ℝ) ≤ Real.logb 2 (ell:ℝ) := by
    simpa only [show (8:ℝ)=(2:ℝ)^3 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), mul_one] using hlog
  apply SufficientOuterOrderBudget.of_sharp (by omega)
  have houtR : (Nat.card (Outer CFSG.Models.Tits):ℝ) ≤ 8 := by exact_mod_cast hout
  linarith

end SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerOuterBound

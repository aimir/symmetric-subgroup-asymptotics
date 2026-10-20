import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkedMoment
import SymmetricSubgroupAsymptotics.LMMSubquadraticSolubleContainersMoment

/-! The global marked moment needs only a subquadratic soluble-container
menu. The retained labelled transitive-count input supplies it; the sharper
Pyber representative estimate is not an input to this assembly. -/

set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics.MarkedC4.SubquadraticContainersGlobal

open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerOrder

theorem solubleGlobal_of_smallSource
    (h62 : PublishedProposition62)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hDixon : PublishedDixonOrder)
    (hsmall : ∀ C : ℕ, 2 ≤ C → ∀ ε : ℝ, 0 < ε → ∀ K : ℝ,
      ∀ᶠ b : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ K * b →
        OrbitCutoffFamilies.solubleCount C b r ≤
          (2 : ℝ) ^ (markedF b r + ε * ((b : ℝ) + r) ^ 2)) :
    SolubleGlobalMarkedC4MomentBound := by
  intro ε hε K
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨C, hC, hlarge⟩ := LMMSubquadraticSolubleContainers.marked_bound
    h62 hLMM hDixon (ε / 3) hthird
  filter_upwards [hlarge, hsmall C hC (ε / 3) hthird K] with b hb hsmallb
  intro r hr
  calc
    solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ ((ε / 3) * ((b : ℝ) + r) ^ 2) *
          OrbitCutoffFamilies.solubleCount C b r := hb r
    _ ≤ (2 : ℝ) ^ ((ε / 3) * ((b : ℝ) + r) ^ 2) *
        (2 : ℝ) ^ (markedF b r + (ε / 3) * ((b : ℝ) + r) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsmallb r hr) (by positivity)
    _ ≤ (2 : ℝ) ^ (markedF b r + ε * ((b : ℝ) + r) ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [sq_nonneg ((b : ℝ) + r)]

/-- The same global marked conclusion, without a Pyber hypothesis. -/
theorem marked_bound
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hgen : KovacsPraegerAbelianizationBound)
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration) :
    Non2UnipotentPrefixFiniteMenu.GlobalMarkedC4MomentBound := by
  apply globalMarkedC4MomentBound_of_soluble
    (rdtOneGeneratorSolubleInput_of_aschbacherGuralnick hAG)
  apply solubleGlobal_of_smallSource h62 hLMM hDixon
  intro C hC
  exact ActualFixedCutoffMarkedBound.marked_bound hsub hseven hgen hKP h55 h53 h57
    h8 hderived rdt46 hodd (by omega : 1 < C)

end SymmetricSubgroupAsymptotics.MarkedC4.SubquadraticContainersGlobal

end

import SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodeCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterNormalization
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenMinimumIndex
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! Actual fixed-generator counting retains the original centralizer of
order eight. The separately certified accepted images have cardinal at
most eight, so the original outer quotient has cardinal at most one.
The pinned presentation receives this result only through the checked
actual equivalence and inherited simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterBound
open CFSG.Certificates.Mathieu11 PrimitiveSocleRawStructure
open CFSGMathieuElevenPresentationWords CFSGMathieuElevenOuterNormalization

theorem original_outer_card_le_one
    [IsSimpleGroup CFSG.Models.Presentations.M11.Model] : Nat.card (Outer M11) ≤ 1 := by
  letI : Finite M11 := Finite.of_injective
    (fun g : M11 => (g : Perm11)) Subtype.val_injective
  have h := OuterFixedElementEvaluationBound.outer_mul_centralizer_le_accepted
    x y closure_pair_eq_top conj_injective normalize_originalB
    CFSGMathieuElevenAcceptedCodeCapacity.acceptedElements (by
      intro f
      exact CFSGMathieuElevenAcceptedCodeCapacity.accepts_mem_acceptedElements (f.val x)
        (CFSGMathieuElevenFourTransversalSeedImages.accepts_map_of_fixed_y f.val f.property))
  have hc : Nat.card (Subgroup.centralizer ({y} : Set M11)) = 8 :=
    CFSGMathieuElevenOrderFourConjugacy.originalB_centralizer_card
  rw [hc] at h
  have h8 := h.trans CFSGMathieuElevenAcceptedCodeCapacity.acceptedElements_card_le_eight
  omega

theorem outer_card_le_one [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Nat.card (Outer CFSG.Models.Presentations.M11.Model) ≤ 1 := by
  rw [CFSGReduction.outer_card_congr CFSGMathieuElevenActualEquivalence.actualEquivalence]
  exact original_outer_card_le_one

theorem sufficient_outer_budget [Finite CFSG.Models.Presentations.M11.Model]
    [IsSimpleGroup CFSG.Models.Presentations.M11.Model] (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Presentations.M11.Model ell) :
    SufficientOuterOrderBudget ell
      (Nat.card (Outer CFSG.Models.Presentations.M11.Model)) := by
  have he := CFSGMathieuElevenMinimumIndex.least_index_eq_eleven ell hell
  rw [he]
  have hlog : (1 : ℝ) ≤ Real.logb 2 (11 : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 11)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  have hout : (Nat.card (Outer CFSG.Models.Presentations.M11.Model) : ℝ) ≤ 1 := by
    exact_mod_cast outer_card_le_one
  exact SufficientOuterOrderBudget.of_sharp (by decide) (by
    norm_num only [Nat.cast_ofNat]
    linarith)

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterBound

import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleOvergroupExtraction
import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection

/-! Every strict overgroup of the actual positive normalizer contains
one of the two literal relative Weyl elements. Actual fixed Bruhat
factors are stripped inside the overgroup; a lattice-identity word is
retained in the already-proved diagonal subgroup, not declared trivial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBorelOvergroupExtraction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourSimpleOvergroupExtraction
open CFSGReeFFourPairedModelWords CFSGReeFFourOriginalWeylWords
open CFSGReeFFourFixedWordClassification CFSGFFourOriginalBruhatCells
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6WeylChamber

theorem exists_simple_relative_weyl_mem_of_borel_lt (m : ℕ)
    (H : Subgroup (originalModelFixed m)) (hBH : fixedBorel m<H) :
    ∃middle : Bool,fixedPairedWord m [middle]∈H := by
  obtain ⟨g,hgH,hgB⟩ := SetLike.exists_of_lt hBH
  obtain ⟨u,hu,d,hdD,s,v,hv,he⟩ := exists_fixed_four_factor_cell m g
  have huB := positive_le_borel m hu
  have hdB := diagonal_le_borel m hdD
  have hvB := positive_le_borel m hv
  have hWH : fixedPairedWord m s∈H := by
    have hh := H.mul_mem
      (H.mul_mem (H.mul_mem (H.inv_mem (hBH.le hdB)) (H.inv_mem (hBH.le huB))) hgH)
      (H.inv_mem (hBH.le hvB))
    have hc : (d⁻¹*u⁻¹)*g*v⁻¹=fixedPairedWord m s := by rw [he];group
    exact hc ▸ hh
  have hne : linearAction (expandRelative (expandPaired s))≠1 := by
    intro hi
    have hWdiag : fixedPairedWord m s∈fixedDiagonal m := by
      have hh := equal_action_model_residual_mem (Field m) (expandPaired s) [] hi
      change CFSGReeFFourOriginalWeylWords.modelWeylWord (Field m) (expandPaired s)∈
        modelDiagonalPart (Field m)
      simpa only [modelWeylWord,inv_one,mul_one] using hh
    apply hgB
    rw [he]
    exact (fixedBorel m).mul_mem
      ((fixedBorel m).mul_mem ((fixedBorel m).mul_mem huB hdB)
        (diagonal_le_borel m hWdiag)) hvB
  exact exists_simple_relative_weyl_mem m H ((positive_le_borel m).trans hBH.le) s hWH hne

end SymmetricSubgroupAsymptotics.CFSGReeFFourBorelOvergroupExtraction

import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpMathieuTopRefinement
import SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoElementarySylowExclusion

/-! The SAME elementary-Sylow top obstruction also excludes the pinned
Co2 factor: its actual cyclic involution orbit would force solvability.
The Mathieu22 and nine prime-product exclusions remain attached to the
same witness. The global failed-half witness is unchanged; it carries no
inferred elementary-Sylow property and no Co2 exclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open TraceySharpHalfDegreeNumerics
open OriginalAffineBoundedSharpPrimeProductSporadicReduction
open OriginalAffineBoundedSharpMathieuTopRefinement

abbrev CoTwoFreeActualTopObstruction {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :=
  {w : MathieuFreeActualTopObstruction (G := G) (X := X) //
    w.val.val.obstruction.sporadic ≠ CFSG.Sporadic.co2}

private def modelEquivCoTwo (s : CFSG.Sporadic) (hs : s = CFSG.Sporadic.co2) :
    s.Model ≃* CFSG.Models.Presentations.Co2.Model := by
  subst s
  exact MulEquiv.refl _

def refine_actual_top {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (w : MathieuFreeActualTopObstruction (G := G) (X := X)) :
    CoTwoFreeActualTopObstruction (G := G) (X := X) :=
  ⟨w,by
    intro hs
    let v := w.val.val
    have htag : v.obstruction.sporadic = CFSG.Sporadic.co2 := hs
    let e : v.obstruction.socle.Simple ≃* CFSG.Models.Presentations.Co2.Model :=
      v.obstruction.equiv.trans (modelEquivCoTwo v.obstruction.sporadic htag)
    exact PrimitiveSocleCoTwoElementarySylowExclusion.not_co_two
      v.obstruction.socle v.sylow v.obstruction.elementary e⟩

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_co_two_free_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (CoTwoFreeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases OriginalAffineBoundedSharpMathieuTopRefinement.genRank_le_sharpFloor_or_mathieu_free_actual_top_or_refined_global
    J block P hCFSG hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top w⟩⟩)
  · exact Or.inr (Or.inr hglobal)

include P in
theorem exists_generating_finset_or_co_two_free_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (CoTwoFreeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_co_two_free_actual_top_or_refined_global J block P hCFSG hsmall with
    hpaid | htop | hglobal
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement

import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleElementarySylowOrderFourExclusion

/-! The SAME elementary-Sylow top obstruction cannot have the pinned
Mathieu22 factor, since that actual model has an element of order four.
This additional exclusion applies ONLY to the original top witness.
The global failed-half witness remains unchanged with its nine proved
prime-product exclusions; no elementary-Sylow property is inferred for it. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpMathieuTopRefinement
open TraceySharpHalfDegreeNumerics
open OriginalAffineBoundedSharpPrimeProductSporadicReduction

abbrev MathieuFreeActualTopObstruction {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :=
  {w : RefinedActualTopObstruction (G := G) (X := X) //
    w.val.obstruction.sporadic ≠ CFSG.Sporadic.m22}

private def modelEquivMathieu (s : CFSG.Sporadic) (hs : s = CFSG.Sporadic.m22) :
    s.Model ≃* CFSG.Models.Mathieu22 := by
  subst s
  exact MulEquiv.refl _

def refine_actual_top {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (w : RefinedActualTopObstruction (G := G) (X := X)) :
    MathieuFreeActualTopObstruction (G := G) (X := X) :=
  ⟨w,by
    intro hs
    let v := w.val
    have htag : v.obstruction.sporadic = CFSG.Sporadic.m22 := hs
    let e : v.obstruction.socle.Simple ≃* CFSG.Models.Mathieu22 :=
      v.obstruction.equiv.trans (modelEquivMathieu v.obstruction.sporadic htag)
    exact PrimitiveSocleElementarySylowOrderFourExclusion.not_mathieu_twenty_two
      v.obstruction.socle v.sylow v.obstruction.elementary e⟩

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_mathieu_free_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (MathieuFreeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases OriginalAffineBoundedSharpPrimeProductSporadicReduction.genRank_le_sharpFloor_or_refined_actual_top_or_refined_global
    J block P hCFSG hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top w⟩⟩)
  · exact Or.inr (Or.inr hglobal)

include P in
theorem exists_generating_finset_or_mathieu_free_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (MathieuFreeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_mathieu_free_actual_top_or_refined_global J block P hCFSG hsmall with
    hpaid | htop | hglobal
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpMathieuTopRefinement

import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpMathieuTopRefinement
import SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoElementarySylowExclusion
import SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreeDegreeEightExclusion
import SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreeSmallActionExclusion
import SymmetricSubgroupAsymptotics.PrimitiveSocleMathieuTwentyTwoSmallActionExclusion

/-! The SAME elementary-Sylow top obstruction also excludes the pinned
Co2 factor: its actual cyclic involution orbit would force solvability.
The Mathieu22 and nine prime-product exclusions remain attached to the
same witness. The final cumulative predicate additionally excludes actual Co3 on8points
using its checked period14 word. The old Co2 APIs remain compatible.
The separate cumulative global predicate excludes Co3 by the checked
even-permutation period14 obstruction and M22 by its checked prime11
word orbit on at most10points. It preserves
the SAME global failed-half action, without an inferred elementary-Sylow
property, Co2 exclusion or degree8 assumption. All earlier APIs remain
compatible. -/
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

/-- The single cumulative exclusion predicate for the SAME actual top.
Further independently proved top exclusions belong here, rather than in
another label-specific facade. This predicate is not used for the global
failed-half witness. -/
def ActualTopExcluded (s : CFSG.Sporadic) : Prop :=
  CFSGSmallActionPrimeProductExclusion.Excluded s ∨ s = CFSG.Sporadic.m22 ∨
    s = CFSG.Sporadic.co2 ∨ s = CFSG.Sporadic.co3

abbrev CumulativeActualTopObstruction {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :=
  {w : ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction (G := G) (X := X) //
    ¬ActualTopExcluded w.obstruction.sporadic}

private def modelEquivCoThree (s : CFSG.Sporadic) (hs : s = CFSG.Sporadic.co3) :
    s.Model ≃* CFSG.Models.MatrixGroups.Co3.Model := by
  subst s
  exact MulEquiv.refl _

def refine_actual_top_cumulative {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (w : CoTwoFreeActualTopObstruction (G := G) (X := X)) :
    CumulativeActualTopObstruction (G := G) (X := X) :=
  ⟨w.val.val.val,by
    let v := w.val.val.val
    intro hs
    change ActualTopExcluded v.obstruction.sporadic at hs
    rcases hs with hprime | hm22 | hco2 | hco3
    · exact w.val.val.property hprime
    · exact w.val.property hm22
    · exact w.property hco2
    · let e : v.obstruction.socle.Simple ≃* CFSG.Models.MatrixGroups.Co3.Model :=
        v.obstruction.equiv.trans (modelEquivCoThree v.obstruction.sporadic hco3)
      exact PrimitiveSocleCoThreeDegreeEightExclusion.not_co_three v.obstruction.socle
        (by simpa only [Nat.card_fin] using (le_refl 8)) e⟩

include P in
theorem genRank_le_sharpFloor_or_cumulative_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_co_two_free_actual_top_or_refined_global
    J block P hCFSG hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top_cumulative w⟩⟩)
  · exact Or.inr (Or.inr hglobal)

include P in
theorem exists_generating_finset_or_cumulative_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_cumulative_actual_top_or_refined_global J block P hCFSG hsmall with
    hpaid | htop | hglobal
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

/-- Only exclusions proved for arbitrary faithful actions on at most10
points belong to the global predicate. The Co2 top exclusion still
requires elementary Sylows and does not occur here. -/
def GlobalExcluded (s : CFSG.Sporadic) : Prop :=
  CFSGSmallActionPrimeProductExclusion.Excluded s ∨ s = CFSG.Sporadic.co3 ∨
    s = CFSG.Sporadic.m22

private def modelEquivMathieuTwentyTwo (s : CFSG.Sporadic)
    (hs : s = CFSG.Sporadic.m22) : s.Model ≃* CFSG.Models.Mathieu22 := by
  subst s
  exact MulEquiv.refl _

abbrev CumulativeGlobalCounterexample (b : ℕ) :=
  {w : EightPointHalfDegreeFiniteModelReduction.PrimitiveSporadicCounterexample b //
    ¬GlobalExcluded w.sporadic}

def refine_global_cumulative {b : ℕ} (hb : b ≤ 10) (w : RefinedGlobalCounterexample b) :
    CumulativeGlobalCounterexample b :=
  ⟨w.val,by
    let v := w.val
    intro hs
    change GlobalExcluded v.sporadic at hs
    rcases hs with hprime | hco3 | hm22
    · exact w.property hprime
    · let e : v.socle.Simple ≃* CFSG.Models.MatrixGroups.Co3.Model :=
        v.equiv.trans (modelEquivCoThree v.sporadic hco3)
      exact PrimitiveSocleCoThreeSmallActionExclusion.not_co_three v.socle
        (by simpa only [Nat.card_fin] using v.degree_le.trans hb) e
    · let e : v.socle.Simple ≃* CFSG.Models.Mathieu22 :=
        v.equiv.trans (modelEquivMathieuTwentyTwo v.sporadic hm22)
      exact PrimitiveSocleMathieuTwentyTwoSmallActionExclusion.not_mathieu_twenty_two v.socle
        (by simpa only [Nat.card_fin] using v.degree_le.trans hb) e⟩

include P in
theorem genRank_le_sharpFloor_or_cumulative_sporadic_obstructions
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (CumulativeGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_cumulative_actual_top_or_refined_global
    J block P hCFSG hsmall with hpaid | htop | hglobal
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl htop)
  · obtain ⟨w⟩ := hglobal
    exact Or.inr (Or.inr ⟨refine_global_cumulative (by decide : 10 ≤ 10) w⟩)

include P in
theorem exists_generating_finset_or_cumulative_sporadic_obstructions
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (CumulativeGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_cumulative_sporadic_obstructions J block P hCFSG hsmall with
    hpaid | htop | hglobal
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement

import SymmetricSubgroupAsymptotics.PrimitiveSocleJankoTwoHeisenbergSingerExclusion
import SymmetricSubgroupAsymptotics.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual

/-! Close the last actual bounded-sharp sporadic case using its SAME
original simple factor. Both residual branches retain the predecessor's
actual witnesses, all exclusion guards, and the original degree bounds.
The resulting bounded-sharp theorem has only the CFSG input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail OriginalAffineBoundedSharpCoTwoTopRefinement
open BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
open BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

private theorem tag_eq_jankoTwo (s : CFSG.Sporadic) (h : RemainingOne s) : s=.j2 := by
  cases s <;> simp_all [RemainingOne]

theorem not_primitive_residual (hhi : n ≤ 21) : ¬PrimitiveSporadicResidual J := by
  intro h
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hm,hc,hj,hh,ht,hl,ho,hco,hco2⟩ := h
  have hs := tag_eq_jankoTwo s
    (tag_of_guards s hY hnew hlarge hm hc hj hh ht hl ho hco hco2)
  subst s
  exact PrimitiveSocleJankoTwoHeisenbergSingerExclusion.not_jankoTwo_of_degree_le_twentyOne
    D (by simpa only [Nat.card_fin] using hhi) e

theorem not_original_nonaffine_residual : ¬OriginalNonaffineSporadicResidual J := by
  intro h
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hm,hc,hj,hh,hth,hl,ho,hco,hco2⟩ := hr
  have hs := tag_eq_jankoTwo s
    (tag_of_guards s hY hnew hlarge hm hc hj hh hth hl ho hco hco2)
  subst s
  exact PrimitiveSocleJankoTwoHeisenbergSingerExclusion.not_jankoTwo_of_degree_le_ten
    D hdegree e

theorem not_actual_residual (hhi : n ≤ 21) : ¬ActualResidual J := by
  rintro (hp | hb)
  · exact not_primitive_residual J hhi hp
  · exact not_original_nonaffine_residual J hb

theorem genRank_le_sharpFloor
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  rcases BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hbad
  · exact hpaid
  · exact False.elim (not_actual_residual J hhi hbad)

theorem exists_generating_finset
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    ∃ U : Finset J,Subgroup.closure (U : Set J)=⊤ ∧ U.card ≤ sharpFloor n := by
  obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨U,hgen,hcard.le.trans (genRank_le_sharpFloor J hCFSG hlo hhi ht)⟩

end SymmetricSubgroupAsymptotics.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG

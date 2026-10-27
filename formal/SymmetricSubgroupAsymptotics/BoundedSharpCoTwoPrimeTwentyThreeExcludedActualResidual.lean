import SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoPrimeTwentyThreeExclusion
import SymmetricSubgroupAsymptotics.BoundedSharpCoOnePrimeElevenExcludedActualResidual

/-! Refine the SAME original primitive/minimal-block witnesses after Co1.
Every prior guard is retained. The remaining literal tag is J2 alone. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail OriginalAffineBoundedSharpCoTwoTopRefinement
open BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def RemainingOne : CFSG.Sporadic → Prop
  | .j2 => True
  | _ => False

theorem tag_of_guards (s : CFSG.Sporadic)
    (hY : ¬IsYSectionModel s) (hnew : ¬NewlyExcluded s)
    (hlarge : ¬ExpandedLargePrimePairTag s) (hm : s ≠ .monster)
    (hc : s ≠ .co3) (hj : s ≠ .j1) (hh : s ≠ .hn) (ht : s ≠ .th)
    (hl : s ≠ .ly) (ho : s ≠ .onan) (hco : s ≠ .co1) (hco2 : s ≠ .co2) :
    RemainingOne s := by
  have htwo := BoundedSharpCoOnePrimeElevenExcludedActualResidual.tag_of_guards
    s hY hnew hlarge hm hc hj hh ht hl ho hco
  cases s <;> simp_all [RemainingOne,BoundedSharpCoOnePrimeElevenExcludedActualResidual.RemainingTwo]

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n ≤ 10 → ¬GlobalExcluded s) ∧ ¬IsYSectionModel s ∧
          ¬NewlyExcluded s ∧ ¬ExpandedLargePrimePairTag s ∧
            s ≠ .monster ∧ s ≠ .co3 ∧ s ≠ .j1 ∧ s ≠ .hn ∧ s ≠ .th ∧
              s ≠ .ly ∧ s ≠ .onan ∧ s ≠ .co1 ∧ s ≠ .co2

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre ≤ 10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
            ¬GlobalExcluded s ∧ ¬IsYSectionModel s ∧ ¬NewlyExcluded s ∧
              ¬ExpandedLargePrimePairTag s ∧ s ≠ .monster ∧ s ≠ .co3 ∧
                s ≠ .j1 ∧ s ≠ .hn ∧ s ≠ .th ∧ s ≠ .ly ∧ s ≠ .onan ∧
                  s ≠ .co1 ∧ s ≠ .co2

def ActualResidual : Prop := PrimitiveSporadicResidual J ∨ OriginalNonaffineSporadicResidual J

theorem refine_primitive (hhi : n ≤ 21)
    (h : BoundedSharpCoOnePrimeElevenExcludedActualResidual.PrimitiveSporadicResidual J) :
    PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,hco1⟩ := h
  refine ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,hco1,?_⟩
  intro hs
  subst s
  exact PrimitiveSocleCoTwoPrimeTwentyThreeExclusion.not_coTwo_of_degree_le_twentyOne
    D (by simpa only [Nat.card_fin] using hhi) e

theorem refine_original_nonaffine
    (h : BoundedSharpCoOnePrimeElevenExcludedActualResidual.OriginalNonaffineSporadicResidual J) :
    OriginalNonaffineSporadicResidual J := by
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,hco1⟩ := hr
  refine ⟨ht,x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,hco1,?_⟩
  intro hs
  subst s
  exact PrimitiveSocleCoTwoPrimeTwentyThreeExclusion.not_coTwo_of_degree_le_ten D hdegree e

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpCoOnePrimeElevenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    (∃ U : Finset J,Subgroup.closure (U : Set J)=⊤ ∧ U.card ≤ sharpFloor n) ∨
      ActualResidual J := by
  rcases genRank_le_sharpFloor_or_actual_residual J hCFSG hlo hhi ht with hpaid | hbad
  · obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual

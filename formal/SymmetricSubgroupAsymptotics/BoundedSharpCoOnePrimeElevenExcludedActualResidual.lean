import SymmetricSubgroupAsymptotics.PrimitiveSocleCoOnePrimeElevenBoundedSharp
import SymmetricSubgroupAsymptotics.BoundedSharpLyONExcludedActualResidual

/-! Retain the same original-D and original minimal-block witnesses and all
previous guards; pay/exclude actual Co1 by its original positive-word prime11
certificate. The remaining literal tags are J2 and Co2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpCoOnePrimeElevenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail OriginalAffineBoundedSharpCoTwoTopRefinement
open BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def RemainingTwo : CFSG.Sporadic → Prop
  | .j2 | .co2 => True
  | _ => False

theorem tag_of_guards (s : CFSG.Sporadic)
    (hY : ¬IsYSectionModel s) (hnew : ¬NewlyExcluded s)
    (hlarge : ¬ExpandedLargePrimePairTag s) (hm : s ≠ .monster)
    (hc : s ≠ .co3) (hj : s ≠ .j1) (hh : s ≠ .hn) (ht : s ≠ .th)
    (hl : s ≠ .ly) (ho : s ≠ .onan) (hco : s ≠ .co1) : RemainingTwo s := by
  have h3 := BoundedSharpLyONExcludedActualResidual.tag_of_guards
    s hY hnew hlarge hm hc hj hh ht hl ho
  cases s <;> simp_all [RemainingTwo,BoundedSharpLyONExcludedActualResidual.RemainingThree]

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n ≤ 10 → ¬GlobalExcluded s) ∧ ¬IsYSectionModel s ∧
          ¬NewlyExcluded s ∧ ¬ExpandedLargePrimePairTag s ∧
            s ≠ .monster ∧ s ≠ .co3 ∧ s ≠ .j1 ∧ s ≠ .hn ∧ s ≠ .th ∧ s ≠ .ly ∧ s ≠ .onan ∧ s ≠ .co1

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre ≤ 10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
            ¬GlobalExcluded s ∧ ¬IsYSectionModel s ∧ ¬NewlyExcluded s ∧
              ¬ExpandedLargePrimePairTag s ∧ s ≠ .monster ∧ s ≠ .co3 ∧ s ≠ .j1 ∧ s ≠ .hn ∧ s ≠ .th ∧ s ≠ .ly ∧ s ≠ .onan ∧ s ≠ .co1

def ActualResidual : Prop := PrimitiveSporadicResidual J ∨ OriginalNonaffineSporadicResidual J

theorem refine_primitive (hCFSG : CFSG.CFSGClassification) (hhi : n ≤ 21)
    (h : BoundedSharpLyONExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon⟩ := h
  by_cases hs : s=.co1
  · subst s
    have hg := PrimitiveSocleCoOnePrimeElevenBoundedSharp.genRank_le_sharpFloor_of_coOne
      D hCFSG (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,hs⟩

theorem refine_original_nonaffine
    (h : BoundedSharpLyONExcludedActualResidual.OriginalNonaffineSporadicResidual J) :
    OriginalNonaffineSporadicResidual J := by
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon⟩ := hr
  refine ⟨ht,x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,?_⟩
  intro hs
  subst s
  exact PrimitiveSocleCoOnePrimeElevenBoundedSharp.not_coOne_of_degree_le_ten D hdegree e

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpLyONExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hCFSG hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
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

end SymmetricSubgroupAsymptotics.BoundedSharpCoOnePrimeElevenExcludedActualResidual

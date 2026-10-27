import SymmetricSubgroupAsymptotics.PrimitiveSocleONPrimeElevenBoundedSharp
import SymmetricSubgroupAsymptotics.PrimitiveSocleLyPrimeSixtySevenExclusion
import SymmetricSubgroupAsymptotics.BoundedSharpThPrimeNineteenExcludedActualResidual

/-! Retain the same original-D witnesses and every earlier guard, while
excluding Ly by prime67 and paying ON through its actual prime11 divisor.
The remaining literal tags are J2, Co1 and Co2. No order or capacity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpLyONExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail OriginalAffineBoundedSharpCoTwoTopRefinement
open BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def RemainingThree : CFSG.Sporadic → Prop
  | .j2 | .co1 | .co2 => True
  | _ => False

theorem tag_of_guards (s : CFSG.Sporadic)
    (hY : ¬IsYSectionModel s) (hnew : ¬NewlyExcluded s)
    (hlarge : ¬ExpandedLargePrimePairTag s) (hm : s ≠ .monster)
    (hc : s ≠ .co3) (hj : s ≠ .j1) (hh : s ≠ .hn) (ht : s ≠ .th)
    (hl : s ≠ .ly) (ho : s ≠ .onan) : RemainingThree s := by
  have h5 := BoundedSharpThPrimeNineteenExcludedActualResidual.tag_of_guards
    s hY hnew hlarge hm hc hj hh ht
  cases s <;> simp_all [RemainingThree,BoundedSharpThPrimeNineteenExcludedActualResidual.RemainingFive]

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n ≤ 10 → ¬GlobalExcluded s) ∧ ¬IsYSectionModel s ∧
          ¬NewlyExcluded s ∧ ¬ExpandedLargePrimePairTag s ∧
            s ≠ .monster ∧ s ≠ .co3 ∧ s ≠ .j1 ∧ s ≠ .hn ∧ s ≠ .th ∧ s ≠ .ly ∧ s ≠ .onan

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre ≤ 10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
            ¬GlobalExcluded s ∧ ¬IsYSectionModel s ∧ ¬NewlyExcluded s ∧
              ¬ExpandedLargePrimePairTag s ∧ s ≠ .monster ∧ s ≠ .co3 ∧ s ≠ .j1 ∧
                s ≠ .hn ∧ s ≠ .th ∧ s ≠ .ly ∧ s ≠ .onan

def ActualResidual : Prop := PrimitiveSporadicResidual J ∨ OriginalNonaffineSporadicResidual J

theorem refine_primitive (hCFSG : CFSG.CFSGClassification) (hhi : n ≤ 21)
    (h : BoundedSharpThPrimeNineteenExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth⟩ := h
  by_cases hl : s=.ly
  · subst s
    exact (PrimitiveSocleLyPrimeSixtySevenExclusion.not_ly_of_degree_le_twentyOne
      D (by simpa only [Nat.card_fin] using hhi) e).elim
  by_cases ho : s=.onan
  · subst s
    have hg := PrimitiveSocleONPrimeElevenBoundedSharp.genRank_le_sharpFloor_of_onan
      D hCFSG (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hl,ho⟩

theorem refine_original_nonaffine
    (h : BoundedSharpThPrimeNineteenExcludedActualResidual.OriginalNonaffineSporadicResidual J) :
    OriginalNonaffineSporadicResidual J := by
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth⟩ := hr
  refine ⟨ht,x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,?_,?_⟩
  · intro hs
    subst s
    exact PrimitiveSocleLyPrimeSixtySevenExclusion.not_ly_of_degree_le_twentyOne D (by omega) e
  · intro hs
    subst s
    exact PrimitiveSocleONPrimeElevenBoundedSharp.not_onan_of_degree_le_ten D hdegree e

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpThPrimeNineteenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
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

end SymmetricSubgroupAsymptotics.BoundedSharpLyONExcludedActualResidual

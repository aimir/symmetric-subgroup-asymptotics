import SymmetricSubgroupAsymptotics.BoundedSharpTenClosedYExcludedActualResidual
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterBound
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBound
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterComplete

/-! One shared actual-pair packet pays M11/M12/M22 in degree11..21;
actual prime23 divisibility excludes M23/M24/J4. The same original
primitive or block witnesses and all existing guards are preserved.
No expected outer orders or new numerical callback are assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail OriginalAffineBoundedSharpCoTwoTopRefinement

def SmallMathieu : CFSG.Sporadic → Prop
  | .m11 | .m12 | .m22 => True
  | _ => False

def PrimeTwentyThree : CFSG.Sporadic → Prop
  | .m23 | .m24 | .j4 => True
  | _ => False

def NewlyExcluded (s : CFSG.Sporadic) : Prop := SmallMathieu s ∨ PrimeTwentyThree s

theorem newlyExcluded_global (s : CFSG.Sporadic) (hs : NewlyExcluded s) : GlobalExcluded s := by
  cases s <;> simp_all [NewlyExcluded,SmallMathieu,PrimeTwentyThree,GlobalExcluded,
    CFSGSmallActionPrimeProductExclusion.Excluded]

theorem small_mathieu_twoGenerated (s : CFSG.Sporadic) (hs : SmallMathieu s) :
    CFSGGeneration.TwoGenerated s.Model := by
  cases s <;> try exact False.elim hs
  case m11 => exact CFSGGeneration.m11_twoGenerated
  case m12 => exact CFSGGeneration.m12_twoGenerated
  case m22 => exact CFSGGeneration.mathieu22_twoGenerated

theorem small_mathieu_packet (s : CFSG.Sporadic) (hs : SmallMathieu s)
    [hfinite : Finite s.Model] [hsimple : IsSimpleGroup s.Model]
    (ell : ℕ) (hell : LeastProperIndex s.Model ell) :
    ell^2 < Nat.card s.Model ∧ SufficientOuterOrderBudget ell (Nat.card (Outer s.Model)) := by
  cases s <;> try exact False.elim hs
  case m11 =>
    exact ⟨@CFSGMathieuElevenActualIndexSquare.index_square hfinite hsimple ell hell,
      @CFSGMathieuElevenOuterBound.sufficient_outer_budget hfinite hsimple ell hell⟩
  case m12 =>
    exact ⟨@CFSGMathieuTwelveActualIndexSquare.index_square hfinite hsimple ell hell,
      @CFSGMathieuTwelveOuterBound.sufficient_outer_budget hfinite hsimple ell hell⟩
  case m22 =>
    exact ⟨@CFSGMathieuTwentyTwoActualIndexSquare.index_square hsimple ell hell,
      @CFSGMathieuTwentyTwoOuterComplete.sufficient_outer_budget hsimple ell hell⟩

theorem small_mathieu_genRank_le_sharpFloor
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (s : CFSG.Sporadic) (hs : SmallMathieu s)
    (e : D.Simple ≃* s.Model) (hlo : 11 ≤ Nat.card X) (hhi : Nat.card X ≤ 21) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  letI : Finite s.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup s.Model := e.symm.isSimpleGroup
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm (small_mathieu_twoGenerated s hs)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := small_mathieu_packet s hs ell (leastProperIndex_of_mulEquiv e ell hell)
  have horder : ell^2 < Nat.card D.Simple := by
    simpa only [Nat.card_congr e.toEquiv] using hm.1
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [outer_card_congr e]
    exact hm.2
  exact (PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.genRank_le_five_of_actual_pair_packet
    D (by omega) S hS hcard ell hell horder houter).trans
    (PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band
      (Nat.card X) hlo hhi)

theorem prime_twentyThree_dvd (s : CFSG.Sporadic) (hs : PrimeTwentyThree s)
    (hn : ¬IsMulCommutative s.Model) : 23 ∣ Nat.card s.Model := by
  cases s <;> try exact False.elim hs
  case m23 => exact CFSGSporadicPrimeProductDivisors.m23_prime_dvd_order hn
  case m24 => exact CFSGSporadicPrimeProductDivisors.m24_prime_dvd_order hn
  case j4 => exact CFSGJ4TwentyThreeDivisor.twenty_three_dvd_order hn

theorem not_prime_twentyThree_of_degree_le_twentyOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (s : CFSG.Sporadic) (e : D.Simple ≃* s.Model)
    (hhi : Nat.card X ≤ 21) : ¬PrimeTwentyThree s := by
  intro hs
  have hn : ¬IsMulCommutative s.Model := fun hc =>
    D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  have h23 : 23 ≤ Nat.card X := (show Nat.Prime 23 by decide).dvd_factorial.mp
    ((prime_twentyThree_dvd s hs hn).trans hd)
  omega

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n ≤ 10 → ¬GlobalExcluded s) ∧ ¬IsYSectionModel s ∧ ¬NewlyExcluded s

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre ≤ 10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
            ¬GlobalExcluded s ∧ ¬IsYSectionModel s ∧ ¬NewlyExcluded s

def ActualResidual : Prop := PrimitiveSporadicResidual J ∨ OriginalNonaffineSporadicResidual J

theorem refine_primitive (hhi : n ≤ 21)
    (h : BoundedSharpTenClosedYExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY⟩ := h
  by_cases hs : SmallMathieu s
  · have hlo : 11 ≤ n := by
      by_contra hh
      exact (hglobal (by omega)) (newlyExcluded_global s (Or.inl hs))
    have hg := small_mathieu_genRank_le_sharpFloor D s hs e
      (by simpa only [Nat.card_fin] using hlo) (by simpa only [Nat.card_fin] using hhi)
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · have hprime : ¬PrimeTwentyThree s :=
      not_prime_twentyThree_of_degree_le_twentyOne D s e
        (by simpa only [Nat.card_fin] using hhi)
    exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,fun hx => hx.elim hs hprime⟩

theorem refine_original_nonaffine
    (h : BoundedSharpTenClosedYExcludedActualResidual.OriginalNonaffineSporadicResidual J) :
    OriginalNonaffineSporadicResidual J := by
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY⟩ := hr
  exact ⟨ht,x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,
    fun hs => hglobal (newlyExcluded_global s hs)⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpTenClosedYExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hhi hp with hpaid | hres
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

end SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual

import SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpTitsCompleteCFSGReduction
import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
import SymmetricSubgroupAsymptotics.PrimitiveSocleThirteenPointTitsExclusion
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenEightPointSharpReduction

/-! Cumulative bounded transitive sharp reduction on the original action.
Primitive, original-block, and global failed-half witnesses are distinct.
The twelve actual-top and eleven global small-action exclusions are kept.
No new classification callback or bounded permutation estimate is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BoundedSharpTitsCompleteActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open OriginalAffineBoundedSharpCoTwoTopRefinement

theorem small_action_not_global_excluded
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (s : CFSG.Sporadic)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model)
    (hdegree : Nat.card X ≤ 10) : ¬GlobalExcluded s := by
  intro hs
  rcases hs with hprime | hco3 | hm22
  · exact CFSGSmallActionPrimeProductExclusion.not_excluded_of_degree_le_ten
      D s e hdegree hprime
  · subst s
    exact PrimitiveSocleCoThreeSmallActionExclusion.not_co_three D hdegree e
  · subst s
    exact PrimitiveSocleMathieuTwentyTwoSmallActionExclusion.not_mathieu_twenty_two D hdegree e

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def PrimitiveAffineResidual : Prop :=
  n = 16 ∧ MulAction.IsPreprimitive J (Fin n) ∧
    Nonempty (PrimitiveAffineProfile J (Fin n)) ∧
      Nonempty (CumulativeGlobalCounterexample 8)

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n ≤ 10 → ¬GlobalExcluded s)

/-- The top belongs to this original affine block, not to the independent
global failed-half action. Its cumulative predicate retains twelve tags. -/
def OriginalAffineTopResidual : Prop :=
  n = 16 ∧ ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nonempty (PrimitiveAffineProfile block.Component block.Fibre) ∧
        Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre ≤ 10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧ ¬GlobalExcluded s

/-- Every disjunct preserves its literal original action or explicitly
retains the independent global failed-half witness. -/
def ActualResidual : Prop :=
  PrimitiveAffineResidual J ∨ PrimitiveSporadicResidual J ∨
    OriginalAffineTopResidual J ∨ Nonempty (CumulativeGlobalCounterexample 10) ∨
      OriginalNonaffineSporadicResidual J

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  letI : MulAction.IsPretransitive J (Fin n) := ht
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  by_cases hp : MulAction.IsPreprimitive J (Fin n)
  · rcases PrimitiveBoundedSharpTitsCompleteCFSGReduction.genRank_le_sharpFloor_or_actual_residual
      hCFSG n hlo hhi J hp with hpaid | haffine | ⟨D,s,⟨e⟩⟩
    · exact Or.inl hpaid
    · obtain ⟨P⟩ := haffine.2
      rcases PrimitiveAffineSixteenEightPointSharpReduction.genRank_le_sharpFloor_or_sporadic_counterexample
          P hCFSG hp (by simpa only [Nat.card_fin] using haffine.1) with hpaid | hbad
      · exact Or.inl (by simpa only [Nat.card_fin] using hpaid)
      · obtain ⟨w⟩ := hbad
        let wprime := OriginalAffineBoundedSharpPrimeProductSporadicReduction.refine_global
          (by decide : 8 ≤ 10) w
        let wcumulative := refine_global_cumulative (by decide : 8 ≤ 10) wprime
        exact Or.inr (Or.inl ⟨haffine.1,hp,⟨P⟩,⟨wcumulative⟩⟩)
    · have hs : n ≤ 10 → ¬GlobalExcluded s := by
        intro hn
        exact small_action_not_global_excluded D s e (by simpa only [Nat.card_fin] using hn)
      exact Or.inr (Or.inr (Or.inl ⟨hp,D,s,⟨e⟩,hs⟩))
  · let x₀ : Fin n := ⟨0,by omega⟩
    obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x₀ hp
    letI : Fintype block.Points := Fintype.ofFinite _
    letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp
      (by have hh := block.degrees_ge_two.1; omega)
    letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
    obtain ⟨P⟩ := publishedONanScottStructure block.Component block.Fibre
    cases P with
    | inr P =>
      rcases OriginalAffineBoundedSharpCoTwoTopRefinement.genRank_le_sharpFloor_or_cumulative_sporadic_obstructions
          J block P hCFSG (by omega) with hpaid | ⟨h16,htop⟩ | hglobal
      · exact Or.inl hpaid
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h16,ht,x₀,block,⟨P⟩,htop⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hglobal))))
    | inl D =>
      have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
        simpa only [Nat.card_fin] using block.degree_product
      have hfibre : Nat.card block.Fibre ≤ 10 := by
        have htwo := block.degrees_ge_two.2
        nlinarith only [hproduct,htwo,hhi]
      rcases OriginalNonaffineBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_remaining_model
          J block D hCFSG (by omega) with hpaid | ⟨j,hj,⟨e⟩⟩
      · exact Or.inl hpaid
      · cases j <;> try exact hj.elim
        ·
          exact (PrimitiveSocleThirteenPointTitsExclusion.not_tits_of_degree_le_thirteen
            D (by omega) e).elim
        ·
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨ht,x₀,block,hfibre,D,_,⟨e⟩,?_⟩))))
          exact small_action_not_global_excluded D _ e hfibre

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      ActualResidual J := by
  rcases genRank_le_sharpFloor_or_actual_residual J hCFSG hlo hhi ht with hpaid | hresidual
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hresidual

end SymmetricSubgroupAsymptotics.BoundedSharpTitsCompleteActualResidual

import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpSporadicReduction
import SymmetricSubgroupAsymptotics.CFSGSmallActionPrimeProductExclusion

/-! Refine the TWO DISTINCT actual sporadic residuals by the proved
prime-product exclusions. The original top witness and global minimal
failed-half witness are preserved literally; only an independently proved
non-exclusion field is appended. Seventeen tags remain unclaimed.
No cardinality, finite-model, or generator callback is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction
open TraceySharpHalfDegreeNumerics EightPointHalfDegreeFiniteModelReduction
open CFSGSmallActionPrimeProductExclusion

abbrev RefinedActualTopObstruction {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :=
  {w : ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction (G := G) (X := X) //
    ¬Excluded w.obstruction.sporadic}

abbrev RefinedGlobalCounterexample (b : ℕ) :=
  {w : PrimitiveSporadicCounterexample b // ¬Excluded w.sporadic}

def refine_actual_top {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (w : ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction (G := G) (X := X)) :
    RefinedActualTopObstruction (G := G) (X := X) :=
  ⟨w,not_excluded_of_degree_le_ten w.obstruction.socle w.obstruction.sporadic
    w.obstruction.equiv (by simp only [Nat.card_fin]; decide)⟩

def refine_global {b : ℕ} (hb : b ≤ 10) (w : PrimitiveSporadicCounterexample b) :
    RefinedGlobalCounterexample b :=
  ⟨w,not_excluded_of_degree_le_ten w.socle w.sporadic w.equiv
    (by simpa only [Nat.card_fin] using w.degree_le.trans hb)⟩

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_refined_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (RefinedActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases OriginalAffineBoundedSharpSporadicReduction.genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    J block P hCFSG hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top w⟩⟩)
  · obtain ⟨w⟩ := hglobal
    exact Or.inr (Or.inr ⟨refine_global (by decide : 10 ≤ 10) w⟩)

include P in
theorem exists_generating_finset_or_refined_actual_top_or_refined_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (RefinedActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_refined_actual_top_or_refined_global J block P hCFSG hsmall with
    hpaid | htop | hglobal
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction

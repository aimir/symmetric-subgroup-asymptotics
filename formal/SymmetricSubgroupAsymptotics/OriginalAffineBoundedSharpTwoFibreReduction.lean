import SymmetricSubgroupAsymptotics.OriginalFourPointCompleteBoundedSharpStep
import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCFSGReduction

/-! Refined bounded affine-block sharp reduction on the SAME original
source and minimal block. A degree-sixteen residual now has literal fibre
size two or eight. The four-point fibre case is paid. The separate global
small sporadic failed action remains explicit and is not called a
subquotient of the given source. No new sharp or half-degree input occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpTwoFibreReduction
open TraceySharpHalfDegreeNumerics EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_two_fibres_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ (Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 8)) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases OriginalAffineBoundedSharpCFSGReduction.affine_fibre_cases J block P hsmall with
    h2 | h3 | h4 | h5 | h7 | h8 | h9
  · rcases OriginalBinaryBoundedSharpStep.genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
      J block hCFSG h2 hsmall with hpaid | h16 | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl ⟨h16,Or.inl h2⟩)
    · exact Or.inr (Or.inr hbad)
  · rcases OriginalTernaryBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block hCFSG h3 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hbad))
  · rcases OriginalFourPointCompleteBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block P hCFSG h4 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr hbad)
  · exact Or.inl (OriginalAffineFiveSevenBoundedSharpStep.genRank_le_sharpFloor J block P (Or.inl h5) hsmall)
  · exact Or.inl (OriginalAffineFiveSevenBoundedSharpStep.genRank_le_sharpFloor J block P (Or.inr h7) hsmall)
  · have hproduct : 8*Nat.card block.Points = n := by
      simpa only [h8,Nat.card_fin] using block.degree_product
    have ht := block.degrees_ge_two.2
    exact Or.inr (Or.inl ⟨by omega,Or.inr h8⟩)
  · rcases OriginalAffineNineBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block P hCFSG h9 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hbad))

include P in
theorem exists_generating_finset_or_two_fibres_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ (Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 8)) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_two_fibres_or_sporadic_counterexample J block P hCFSG hsmall with
    hpaid | h16 | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl h16)
  · exact Or.inr (Or.inr hbad)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpTwoFibreReduction

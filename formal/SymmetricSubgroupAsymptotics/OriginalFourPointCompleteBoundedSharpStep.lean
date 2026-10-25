import SymmetricSubgroupAsymptotics.OriginalFourPointSixteenSharpStep
import SymmetricSubgroupAsymptotics.OriginalFourPointBoundedSharpStep

/-! The complete bounded original four-point affine-block sharp step.
The degree-sixteen class coupling is now paid internally; the only
remaining alternative is the precise existing small sporadic failed
primitive action. That global witness is not asserted to be a subquotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalFourPointCompleteBoundedSharpStep
open TraceySharpHalfDegreeNumerics EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hfour : Nat.card block.Fibre = 4) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases OriginalFourPointBoundedSharpStep.genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    J block P hCFSG hfour hsmall with hpaid | h16 | hbad
  · exact Or.inl hpaid
  · exact Or.inl (OriginalFourPointSixteenSharpStep.genRank_le_sharpFloor J block P hfour h16)
  · exact Or.inr hbad

include P in
theorem exists_generating_finset_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hfour : Nat.card block.Fibre = 4) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_sporadic_counterexample J block P hCFSG hfour hsmall with hpaid | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.OriginalFourPointCompleteBoundedSharpStep

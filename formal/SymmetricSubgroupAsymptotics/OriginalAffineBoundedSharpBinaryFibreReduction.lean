import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpTwoFibreReduction
import SymmetricSubgroupAsymptotics.OriginalAffineEightTwoBlockSharpStep

/-! On the SAME original bounded affine block source, only a binary fibre
at total degree sixteen remains. The affine eight-point/two-block branch
is now paid by its actual translation quotient and two-coordinate bound.
The separate global small sporadic failed action is retained literally;
it is not asserted to be a subquotient of the given source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpBinaryFibreReduction
open TraceySharpHalfDegreeNumerics EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_binary_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nat.card block.Fibre = 2) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases OriginalAffineBoundedSharpTwoFibreReduction.genRank_le_sharpFloor_or_two_fibres_or_sporadic_counterexample
    J block P hCFSG hsmall with
    hpaid | ⟨h16,h2 | h8⟩ | hbad
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl ⟨h16,h2⟩)
  · exact Or.inl (OriginalAffineEightTwoBlockSharpStep.genRank_le_sharpFloor J block P h8 h16)
  · exact Or.inr (Or.inr hbad)

include P in
theorem exists_generating_finset_or_binary_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nat.card block.Fibre = 2) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_binary_sixteen_or_sporadic_counterexample J block P hCFSG hsmall with
    hpaid | h16 | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl h16)
  · exact Or.inr (Or.inr hbad)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpBinaryFibreReduction

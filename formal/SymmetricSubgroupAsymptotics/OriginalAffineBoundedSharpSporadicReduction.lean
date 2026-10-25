import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpBinaryFibreReduction
import SymmetricSubgroupAsymptotics.OriginalBinarySixteenSharpCFSGReduction

/-! Complete bounded original affine-block sharp reduction to literal
sporadic data. There is no unexplained degree-sixteen shape left. The
actual primitive sporadic TOP of a binary degree-sixteen source remains
separate from a global minimal failed-half action of degree at most ten.
The former is an actual point relabeling of the original top and need
not fail the half-degree bound. No finite model bound is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpSporadicReduction
open TraceySharpHalfDegreeNumerics EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty
        (ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
          (G := block.Top) (X := block.Points))) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases OriginalAffineBoundedSharpBinaryFibreReduction.genRank_le_sharpFloor_or_binary_sixteen_or_sporadic_counterexample
      J block P hCFSG hsmall with hpaid | ⟨h16,h2⟩ | hbad
  · exact Or.inl hpaid
  · subst n
    rcases OriginalBinarySixteenSharpCFSGReduction.genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
        J block hCFSG h2 with hpaid | htop | hglobal
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl ⟨rfl,htop⟩)
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hglobal))
  · exact Or.inr (Or.inr hbad)

include P in
theorem exists_generating_finset_or_actual_top_sporadic_or_global_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty
        (ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
          (G := block.Top) (X := block.Points))) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    J block P hCFSG hsmall with hpaid | htop | hglobal
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpSporadicReduction

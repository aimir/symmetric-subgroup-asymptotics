import SymmetricSubgroupAsymptotics.CFSGActualAffineWreathLargeLocal
import SymmetricSubgroupAsymptotics.CFSGActualNonaffineWreathLargeLocal
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! Complete actual primitive-local large-degree tail, from CFSG only.
The source action and actual full-component subgroup family are unchanged
through both branches of the original primitive structure theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGActualPrimitiveWreathLargeLocal
open PrimitiveSocleRawStructure

theorem uniform_large_local (hCFSG : CFSG.CFSGClassification) (ε : ℝ) (hε : 0<ε) :
    ∃ R0 : ℕ, ∀ {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
      [FaithfulSMul R X] [Nontrivial X] [MulAction.IsPreprimitive R X],
      R0≤Nat.card X → 2≤Nat.card X →
      ∀ t : ℕ, 2≤t → ∀ Q : Subgroup (Equiv.Perm (Fin t)),
        MulAction.IsPretransitive Q (Fin t) →
        (Nat.card (ActualFullWreathFamily.Family R Q (Fin t)) : ℝ)≤
          (2 : ℝ)^(ε*((Nat.card X*t : ℕ) : ℝ)^2) := by
  obtain ⟨RA,hA⟩ := CFSGActualAffineWreathLargeLocal.uniform_large_local hCFSG ε hε
  obtain ⟨RN,hN⟩ := CFSGActualNonaffineWreathLargeLocal.uniform_large_local hCFSG ε hε
  refine ⟨max RA RN,?_⟩
  intro R X _ _ _ _ _ _ _ hlarge hr t ht Q hQ
  obtain ⟨D | P⟩ := publishedONanScottStructure R X
  · exact hN D ((le_max_right _ _).trans hlarge) hr t ht Q hQ
  · exact hA P (Classical.choice inferInstance) ((le_max_left _ _).trans hlarge) hr t ht Q hQ

end SymmetricSubgroupAsymptotics.CFSGActualPrimitiveWreathLargeLocal

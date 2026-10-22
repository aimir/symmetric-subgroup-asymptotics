import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear

/-! Every original norm-two root is a literal word of simple reflections
of a negative simple root. This uses the original base's reflection
induction, rather than a root census or a matrix root-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordOrbit
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckColumns
open CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem exists_signed_word (k : Roots A) :
    ∃ (w : List (Fin r)) (j : Fin r),
      k.val=(wordRoot A hs hp b s w (s j)).val ∨
      k.val= -(wordRoot A hs hp b s w (s j)).val := by
  apply b.induction_reflect k
  · intro k hk
    obtain ⟨w,j,hk | hk⟩ := hk
    · refine ⟨w,j,Or.inr ?_⟩
      change (negativeIndex A hs hp k).val= _
      rw [negative_val,hk]
    · refine ⟨w,j,Or.inl ?_⟩
      change (negativeIndex A hs hp k).val= _
      rw [negative_val,hk,neg_neg]
  · intro k hk
    let j : Fin r := s.symm ⟨k,hk⟩
    refine ⟨[],j,Or.inl ?_⟩
    change k.val=(s (s.symm ⟨k,hk⟩):Roots A).val
    rw [s.apply_symm_apply]
  · intro k i hk hi
    obtain ⟨w,j,hk | hk⟩ := hk
    · refine ⟨s.symm ⟨i,hi⟩::w,j,Or.inl ?_⟩
      change reflectionEquiv A i k.val=
        reflectionEquiv A (s (s.symm ⟨i,hi⟩)) (wordRoot A hs hp b s w (s j)).val
      rw [s.apply_symm_apply,hk]
    · refine ⟨s.symm ⟨i,hi⟩::w,j,Or.inr ?_⟩
      change reflectionEquiv A i k.val=
        -reflectionEquiv A (s (s.symm ⟨i,hi⟩)) (wordRoot A hs hp b s w (s j)).val
      rw [s.apply_symm_apply,hk,map_neg]

theorem exists_negative_word (k : Roots A) :
    ∃ (w : List (Fin r)) (j : Fin r),
      k.val= -(wordRoot A hs hp b s w (s j)).val := by
  obtain ⟨w,j,hk | hk⟩ := exists_signed_word A hs hp b s k
  · refine ⟨w++[j],j,?_⟩
    rw [wordRoot_append]
    change k.val= -(wordRoot A hs hp b s w (negativeIndex A hs hp (s j))).val
    rw [wordRoot_negative_val,neg_neg]
    exact hk
  · exact ⟨w,j,hk⟩

theorem exists_word_linear_negative (k : Roots A) :
    ∃ (w : List (Fin r)) (j : Fin r),
      k.val=wordLinear A hs hp b s w (-(s j:Roots A).val) := by
  obtain ⟨w,j,hk⟩ := exists_negative_word A hs hp b s k
  refine ⟨w,j,?_⟩
  rw [map_neg,wordLinear_root]
  exact hk

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordOrbit

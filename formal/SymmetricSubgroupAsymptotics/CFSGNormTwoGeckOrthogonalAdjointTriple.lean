import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalRootColumn
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns

/-! A root unit orthogonal to a selected simple root fixes its entire
adjoint triple. This is a literal matrix-column statement in every
characteristic, suitable for products of orthogonal rank-one factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalAdjointTriple
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckOrthogonalColumns CFSGNormTwoGeckOrthogonalRootColumn
open CFSGNormTwoGeckParameterTripleColumns CFSGNormTwoGeckIntegralRealization
open CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem orthogonal_root_fixes_adjoint_triple (K : Type*) [Field K] (j i : Fin r)
    (hji : integerPairing A (s j : Roots A).val (s i : Roots A).val=0)
    (neg : Bool) (t : K) :
    ((canonicalRoot (realizationData A hs hp b s) K neg j t :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      (Pi.single (Sum.inl (s i)) (1:K) : b.support⊕Roots A→K)=
        Pi.single (Sum.inl (s i)) (1:K)) ∧
    ((canonicalRoot (realizationData A hs hp b s) K neg j t :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      (Pi.single (Sum.inr (s i : Roots A)) (1:K) : b.support⊕Roots A→K)=
        Pi.single (Sum.inr (s i : Roots A)) (1:K)) ∧
    ((canonicalRoot (realizationData A hs hp b s) K neg j t :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      (Pi.single (Sum.inr (negativeIndex A hs hp (s i))) (1:K) : b.support⊕Roots A→K)=
        Pi.single (Sum.inr (negativeIndex A hs hp (s i))) (1:K)) := by
  have hc : b.cartanMatrix (s j) (s i)=0 :=
    (integerPairing_eq_cartan A hs hp b (s j) (s i)).symm.trans hji
  have hn : integerPairing A (s j : Roots A).val (negativeIndex A hs hp (s i)).val=0 := by
    rw [CFSGNormTwoGeckColumns.negative_val,map_neg,hji,neg_zero]
  cases neg
  · refine ⟨?_,positive_fixes_orthogonal_column A hs hp b s K j _ hji t,
      positive_fixes_orthogonal_column A hs hp b s K j _ hn t⟩
    simpa only [hc,abs_zero,Int.cast_zero,mul_zero,zero_smul,add_zero] using
      positive_cartan_general A hs hp b s K j (s i) t
  · refine ⟨?_,negative_fixes_orthogonal_column A hs hp b s K j _ hji t,
      negative_fixes_orthogonal_column A hs hp b s K j _ hn t⟩
    simpa only [hc,abs_zero,Int.cast_zero,mul_zero,zero_smul,add_zero] using
      negative_cartan_general A hs hp b s K j (s i) t

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalAdjointTriple

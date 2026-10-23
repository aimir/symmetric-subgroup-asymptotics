import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGQuadraticRankOneIntertwiner

/-! The inverse-parameter constraint on a literal canonical simple
rank-one word in every norm-two Geck realization. The original adjoint
triple has a coefficient-one Cartan coordinate in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneConstraint
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckParameterizedWeyl
open CFSGNormTwoGeckParameterTripleColumns CFSGSerreQuadraticMatrix
open CFSGQuadraticRankOneIntertwiner
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b₀ : (rootPairing A hs hp).Base) {r : ℕ} (s₀ : Fin r≃b₀.support)

theorem canonical_word_inverse_constraint (K : Type*) [Field K] (i : Fin r)
    (a b t s : K) (hs0 : s≠0)
    (hinter :
      (canonicalRoot (realizationData A hs hp b₀ s₀) K false i a*
        canonicalRoot (realizationData A hs hp b₀ s₀) K true i b*
        canonicalRoot (realizationData A hs hp b₀ s₀) K false i a)*
        canonicalRoot (realizationData A hs hp b₀ s₀) K false i t=
      canonicalRoot (realizationData A hs hp b₀ s₀) K true i s*
        (canonicalRoot (realizationData A hs hp b₀ s₀) K false i a*
        canonicalRoot (realizationData A hs hp b₀ s₀) K true i b*
        canonicalRoot (realizationData A hs hp b₀ s₀) K false i a)) :
    1+a*b=0 := by
  let U := rootOperator A hs hp b₀ s₀ K false i
  let V := rootOperator A hs hp b₀ s₀ K true i
  let u : b₀.support⊕Roots A→K := Pi.single (Sum.inl (s₀ i)) 1
  let p : b₀.support⊕Roots A→K := Pi.single (Sum.inr (s₀ i : Roots A)) 1
  let m : b₀.support⊕Roots A→K := Pi.single (Sum.inr (negativeIndex A hs hp (s₀ i))) 1
  let l : (b₀.support⊕Roots A→K)→ₗ[K]K := LinearMap.proj (Sum.inl (s₀ i))
  have hlu : l u=1 := by
    change (Pi.single (Sum.inl (s₀ i)) (1:K) : b₀.support⊕Roots A→K) (Sum.inl (s₀ i))=1
    simp only [Pi.single_eq_same]
  have hlp : l p=0 := by
    change (Pi.single (Sum.inr (s₀ i : Roots A)) (1:K) :
      b₀.support⊕Roots A→K) (Sum.inl (s₀ i))=0
    simp only [Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  have hlm : l m=0 := by
    change (Pi.single (Sum.inr (negativeIndex A hs hp (s₀ i))) (1:K) :
      b₀.support⊕Roots A→K) (Sum.inl (s₀ i))=0
    simp only [Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  have he := congrArg (fun z : (Matrix (b₀.support⊕Roots A) (b₀.support⊕Roots A) K)ˣ=>
    Matrix.toLinAlgEquiv' (z : Matrix (b₀.support⊕Roots A) (b₀.support⊕Roots A) K)) hinter
  simp only [Units.val_mul,map_mul] at he
  change tripleWord U V a b*U t=V s*tripleWord U V a b at he
  exact one_add_mul_eq_zero_of_intertwines U V u p m
    (positive_cartan A hs hp b₀ s₀ K i) (positive_positive A hs hp b₀ s₀ K i)
    (positive_negative A hs hp b₀ s₀ K i) (negative_cartan A hs hp b₀ s₀ K i)
    (negative_positive A hs hp b₀ s₀ K i) (negative_negative A hs hp b₀ s₀ K i)
    l hlu hlp hlm a b t s hs0 he

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneConstraint

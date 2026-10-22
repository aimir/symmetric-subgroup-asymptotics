import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFunctionalSupport
import SymmetricSubgroupAsymptotics.CFSGWeightedDiagonalConjugation

/-! Conjugation by the literal rank-one torus word scales each original
positive simple-root parameter by its actual integral Cartan pairing.
This is a same-matrix calculation, valid in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckDiagonalTorus
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem torus_mul_positive (K : Type*) [Field K] (i j : Fin r) (t : Kˣ) (a : K) :
    parameterTorus A hs hp b s K i t*canonicalRoot (realizationData A hs hp b s) K false j a=
      canonicalRoot (realizationData A hs hp b s) K false j
        (a*(t:K)^(integerPairing A (s i:Roots A).val (s j:Roots A).val))*
          parameterTorus A hs hp b s K i t := by
  let f : (n→ℤ)→ₗ[ℤ]ℤ := integerPairing A (s i:Roots A).val
  have hE : ∀u v,weight A hs hp b s i u≠
      weight A hs hp b s i v+integerPairing A (s i:Roots A).val (s j:Roots A).val→
      fieldRoot (realizationData A hs hp b s) K false j u v=0 := by
    intro u v huv
    exact CFSGNormTwoGeckFunctionalSupport.field_E_degree A hs hp b s f K j u v huv
  have hD : ∀u v,weight A hs hp b s i u≠
      weight A hs hp b s i v+2*integerPairing A (s i:Roots A).val (s j:Roots A).val→
      fieldSecond (realizationData A hs hp b s) K false j u v=0 := by
    intro u v huv
    exact CFSGNormTwoGeckFunctionalSupport.field_second_degree A hs hp b s f K j u v huv
  apply Units.ext
  change (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalRoot (realizationData A hs hp b s) K false j a : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)=
      (canonicalRoot (realizationData A hs hp b s) K false j
        (a*(t:K)^(integerPairing A (s i:Roots A).val (s j:Roots A).val)) : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (parameterTorus A hs hp b s K i t : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) K)
  simp only [torus_diagonal,canonicalRoot_val]
  exact CFSGWeightedDiagonalConjugation.quadratic_mul_scaled
    (weight A hs hp b s i) t (integerPairing A (s i:Roots A).val (s j:Roots A).val)
    (fieldRoot (realizationData A hs hp b s) K false j)
    (fieldSecond (realizationData A hs hp b s) K false j) hE hD a

theorem torus_conjugate_positive (K : Type*) [Field K] (i j : Fin r) (t : Kˣ) (a : K) :
    parameterTorus A hs hp b s K i t*canonicalRoot (realizationData A hs hp b s) K false j a*
      (parameterTorus A hs hp b s K i t)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false j
        (a*(t:K)^(integerPairing A (s i:Roots A).val (s j:Roots A).val)) := by
  rw [torus_mul_positive,mul_assoc,mul_inv_cancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation

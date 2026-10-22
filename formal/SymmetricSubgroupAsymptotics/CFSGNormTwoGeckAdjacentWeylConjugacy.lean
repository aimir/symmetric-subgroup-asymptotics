import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylNegativeSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterConjugacy

/-! Actual adjacent-root torus-sign conjugacy over every coefficient ring,
proved by the original integer Geck matrices and rational weight strings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylConjugacy
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylUnits
open CFSGNormTwoGeckAdjacentWeylSign CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (i j : Fin r) (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
include hij

theorem rational_adjacent_sign (neg : Bool) :
    (canonicalWeyl (realizationData A hs hp b s) ℚ i : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) ℚ)^2*
      fieldRoot (realizationData A hs hp b s) ℚ neg j=
      -(fieldRoot (realizationData A hs hp b s) ℚ neg j*
        (canonicalWeyl (realizationData A hs hp b s) ℚ i : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) ℚ)^2) := by
  cases neg
  · rw [fieldRoot_false]
    apply Matrix.toLinAlgEquiv'.injective
    simp only [map_mul,map_pow,map_neg,rational_weyl_operator]
    exact weyl_square_e_anticommute A hs hp b (s i) (s j) hij
  · rw [fieldRoot_true]
    apply Matrix.toLinAlgEquiv'.injective
    simp only [map_mul,map_pow,map_neg,rational_weyl_operator]
    exact weyl_square_f_anticommute A hs hp b (s i) (s j) hij

theorem canonical_adjacent_conjugacy (K : Type*) [CommRing K] (neg : Bool) (t : K) :
    (canonicalWeyl (realizationData A hs hp b s) K i)^2*
        canonicalRoot (realizationData A hs hp b s) K neg j t=
      canonicalRoot (realizationData A hs hp b s) K neg j (-t)*
        (canonicalWeyl (realizationData A hs hp b s) K i)^2 :=
  canonical_weyl_square_root (realizationData A hs hp b s) i j neg
    (rational_adjacent_sign A hs hp b s i j hij neg) K t

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylConjugacy

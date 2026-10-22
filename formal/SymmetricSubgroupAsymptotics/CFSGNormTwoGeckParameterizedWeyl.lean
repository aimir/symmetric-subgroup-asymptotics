import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns
import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterStrings

/-! The actual parameterized rank-one Geck word, on its original triple
and every original Cartan column. All formulas work in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeyl
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterTripleColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def rootOperator (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) (t : K) :
    Module.End K (b.support⊕Roots A→K) := Matrix.toLinAlgEquiv'
      (canonicalRoot (realizationData A hs hp b s) K neg i t : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)

def parameterWeyl (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  canonicalRoot (realizationData A hs hp b s) K false i (t:K)*
    canonicalRoot (realizationData A hs hp b s) K true i (-(t:K)⁻¹)*
    canonicalRoot (realizationData A hs hp b s) K false i (t:K)

theorem parameterWeyl_operator (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)=
      CFSGQuadraticWeylParameterStrings.word (rootOperator A hs hp b s K false i)
        (rootOperator A hs hp b s K true i) t := by
  simp only [parameterWeyl,Units.val_mul,map_mul]
  rfl

theorem parameterWeyl_triple (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl (s i)) 1=
        -Pi.single (.inl (s i)) 1 ∧
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (s i:Roots A)) 1=
        ((t:K)⁻¹)^2 • Pi.single (.inr (negativeIndex A hs hp (s i))) 1 ∧
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (negativeIndex A hs hp (s i))) 1=
        (t:K)^2 • Pi.single (.inr (s i:Roots A)) 1 := by
  have hh := CFSGQuadraticWeylParameterStrings.word_triple
    (rootOperator A hs hp b s K false i) (rootOperator A hs hp b s K true i) t
    (Pi.single (.inl (s i)) 1) (Pi.single (.inr (s i:Roots A)) 1)
    (Pi.single (.inr (negativeIndex A hs hp (s i))) 1)
    (positive_cartan A hs hp b s K i) (positive_positive A hs hp b s K i)
    (positive_negative A hs hp b s K i) (negative_cartan A hs hp b s K i)
    (negative_positive A hs hp b s K i) (negative_negative A hs hp b s K i)
  constructor
  · change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)) (Pi.single (.inl (s i)) 1)=_
    rw [parameterWeyl_operator]
    exact hh.1
  · constructor
    · change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)) (Pi.single (.inr (s i:Roots A)) 1)=_
      rw [parameterWeyl_operator]
      exact hh.2.1
    · change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K))
          (Pi.single (.inr (negativeIndex A hs hp (s i))) 1)=_
      rw [parameterWeyl_operator]
      exact hh.2.2

theorem parameterWeyl_cartan (K : Type*) [Field K] (i : Fin r) (t : Kˣ) (j : b.support) :
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
      Pi.single (.inl j) 1-((|b.cartanMatrix (s i) j|:ℤ):K) • Pi.single (.inl (s i)) 1 := by
  have hh := CFSGQuadraticWeylParameterStrings.word_cartan
    (rootOperator A hs hp b s K false i) (rootOperator A hs hp b s K true i) t
    (Pi.single (.inl (s i)) 1) (Pi.single (.inr (s i:Roots A)) 1)
    (Pi.single (.inr (negativeIndex A hs hp (s i))) 1) (Pi.single (.inl j) 1)
    (((|b.cartanMatrix (s i) j|:ℤ):K))
    (positive_cartan A hs hp b s K i) (positive_positive A hs hp b s K i)
    (positive_negative A hs hp b s K i) (negative_cartan A hs hp b s K i)
    (negative_positive A hs hp b s K i) (negative_negative A hs hp b s K i)
    (positive_cartan_general A hs hp b s K i j) (negative_cartan_general A hs hp b s K i j)
  change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)) (Pi.single (.inl j) 1)=_
  rw [parameterWeyl_operator]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeyl

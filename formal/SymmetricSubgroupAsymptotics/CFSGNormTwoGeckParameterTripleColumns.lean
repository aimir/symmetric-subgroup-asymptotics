import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootSteps
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOppositionColumns

/-! Every parameter of the actual simple-root quadratic units on the
Cartan/root/opposite-root triple. No characteristic restriction or half
coefficient is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckFieldRootColumns CFSGNormTwoGeckFieldRootSteps
open CFSGNormTwoGeckFieldOpposition CFSGNormTwoGeckFieldOppositionColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_cartan (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl (s i)) 1=
      Pi.single (.inl (s i)) 1+(2*t) • Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_cartan,second_cartan,smul_zero,add_zero,smul_smul]
  rw [mul_comm t 2]

theorem positive_positive (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (s i:Roots A)) 1=
      Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_positive,second_positive,smul_zero,add_zero]

theorem positive_negative (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (negativeIndex A hs hp (s i))) 1=
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1+t • Pi.single (.inl (s i)) 1+
        t^2 • Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_negative,second_negative]

theorem positive_cartan_general (K : Type*) [CommRing K] (i : Fin r) (j : b.support) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
      Pi.single (.inl j) 1+(t*((|b.cartanMatrix (s i) j|:ℤ):K)) • Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_cartan_general,second_cartan_general,smul_zero,add_zero,smul_smul]

theorem negative_val (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)=
      fieldOmega A hs hp b K*(canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*fieldOmega A hs hp b K := by
  have hh := congrArg (fun u : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ=>
    (u : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))
      (canonicalRoot_conjugate A hs hp b s K false i t)
  exact hh.symm

theorem negative_cartan (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl (s i)) 1=
      Pi.single (.inl (s i)) 1+(2*t) • Pi.single (.inr (negativeIndex A hs hp (s i))) 1 := by
  rw [negative_val,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,omega_cartan,
    positive_cartan,Matrix.mulVec_add,Matrix.mulVec_smul,omega_cartan,omega_root]

theorem negative_positive (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (s i:Roots A)) 1=
      Pi.single (.inr (s i:Roots A)) 1+t • Pi.single (.inl (s i)) 1+
        t^2 • Pi.single (.inr (negativeIndex A hs hp (s i))) 1 := by
  rw [negative_val,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,omega_root,positive_negative,
    Matrix.mulVec_add,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,
    omega_root,CFSGNormTwoRootNegation.negative_negative,omega_cartan,omega_root]

theorem negative_negative (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (negativeIndex A hs hp (s i))) 1=
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1 := by
  rw [negative_val,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,omega_root,
    CFSGNormTwoRootNegation.negative_negative,positive_positive,omega_root]

theorem negative_cartan_general (K : Type*) [CommRing K] (i : Fin r) (j : b.support) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
      Pi.single (.inl j) 1+(t*((|b.cartanMatrix (s i) j|:ℤ):K)) •
        Pi.single (.inr (negativeIndex A hs hp (s i))) 1 := by
  rw [negative_val,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,omega_cartan,
    positive_cartan_general,Matrix.mulVec_add,Matrix.mulVec_smul,omega_cartan,omega_root]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns

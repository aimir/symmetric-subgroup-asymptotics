import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootColumns

/-! Actual arbitrary root-step columns for the integral quadratic unit.
These are transported from the proved norm-two rational Geck columns,
without enumerating roots or reducing rational denominators in the field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootSteps
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckFieldRootColumns
open CFSGSerreQuadraticMatrix CFSGIntegerMatrixColumnTransport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem root_cartan_general (K : Type*) [CommRing K] (i : Fin r) (j : b.support) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥPi.single (.inl j) 1=
      ((|b.cartanMatrix (s i) j|:ℤ):K) • Pi.single (.inr (s i:Roots A)) 1 := by
  have hq : RootPairing.GeckConstruction.e (s i)*ᵥ
      integerVector ℚ (Pi.single (.inl j) (1:ℤ))=
      integerVector ℚ (|b.cartanMatrix (s i) j| • Pi.single (.inr (s i:Roots A)) (1:ℤ)) := by
    simpa only [integerVector_zsmul,integerVector_single,Int.cast_one,Int.cast_smul_eq_zsmul]
      using E_u A hs hp b (s i) j
  simpa only [integerVector_zsmul,integerVector_single,Int.cast_one] using
    root_column A hs hp b s K i _ _ hq

theorem root_add_step (K : Type*) [CommRing K] (i : Fin r) (j k : Roots A)
    (hk : (rootPairing A hs hp).root k=(rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥPi.single (.inr j) 1=Pi.single (.inr k) 1 := by
  have hq : RootPairing.GeckConstruction.e (s i)*ᵥintegerVector ℚ (Pi.single (.inr j) (1:ℤ))=
      integerVector ℚ (Pi.single (.inr k) (1:ℤ)) := by
    simpa only [integerVector_single,Int.cast_one,RootPairing.GeckConstruction.v]
      using E_v_add A hs hp b (s i) j k hk
  simpa only [integerVector_single,Int.cast_one] using root_column A hs hp b s K i _ _ hq

theorem root_zero_step (K : Type*) [CommRing K] (i : Fin r) (j : Roots A)
    (hj : j≠negativeIndex A hs hp (s i))
    (ha : (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j∉Set.range (rootPairing A hs hp).root) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥPi.single (.inr j) 1=0 := by
  have hq : RootPairing.GeckConstruction.e (s i)*ᵥintegerVector ℚ (Pi.single (.inr j) (1:ℤ))=
      integerVector ℚ 0 := by
    simpa only [integerVector_single,Int.cast_one,RootPairing.GeckConstruction.v,
      integerVector,Int.cast_zero] using E_v_zero A hs hp b (s i) j hj ha
  have hc := root_column A hs hp b s K i _ _ hq
  have hz : integerVector (I:=b.support⊕Roots A) K 0=0 := by
    ext k
    simp [integerVector]
  simpa only [integerVector_single,Int.cast_one,hz] using hc

theorem second_cartan_general (K : Type*) [CommRing K] (i : Fin r) (j : b.support) :
    fieldSecond (realizationData A hs hp b s) K false i*ᵥPi.single (.inl j) 1=0 := by
  rw [second_literal,Matrix.mulVec_single_one]
  ext k
  simp [Matrix.single_apply]

theorem second_other (K : Type*) [CommRing K] (i : Fin r) (j : Roots A)
    (hj : j≠negativeIndex A hs hp (s i)) :
    fieldSecond (realizationData A hs hp b s) K false i*ᵥPi.single (.inr j) 1=0 := by
  rw [second_literal,Matrix.mulVec_single_one]
  ext k
  simp [Matrix.single_apply,hj,Ne.symm hj]

theorem unit_cartan_general (K : Type*) [CommRing K] (i : Fin r) (j : b.support) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
      Pi.single (.inl j) 1+((|b.cartanMatrix (s i) j|:ℤ):K) • Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_cartan_general,second_cartan_general,one_smul,one_pow,smul_zero,add_zero]

theorem unit_add_step (K : Type*) [CommRing K] (i : Fin r) (j k : Roots A)
    (hj : j≠negativeIndex A hs hp (s i))
    (hk : (rootPairing A hs hp).root k=(rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
      Pi.single (.inr j) 1+Pi.single (.inr k) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_add_step A hs hp b s K i j k hk,second_other A hs hp b s K i j hj,
    one_smul,one_pow,smul_zero,add_zero]

theorem unit_zero_step (K : Type*) [CommRing K] (i : Fin r) (j : Roots A)
    (hj : j≠negativeIndex A hs hp (s i))
    (ha : (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j∉Set.range (rootPairing A hs hp).root) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=Pi.single (.inr j) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_zero_step A hs hp b s K i j hj ha,second_other A hs hp b s K i j hj,
    one_smul,one_pow,smul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootSteps

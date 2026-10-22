import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixColumnTransport

/-! The same positive-root and quadratic-unit three-string columns over
every coefficient ring. Rational columns recover integer identities first. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralQuadratic CFSGNormTwoGeckWeylBasic
open CFSGSerreQuadraticMatrix CFSGIntegerMatrixColumnTransport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

private theorem integerVector_zero (K : Type*) [CommRing K] :
    integerVector (I:=b.support⊕Roots A) K 0=0 := by ext i;simp [integerVector]

theorem root_column (K : Type*) [CommRing K] (i : Fin r)
    (v w : b.support⊕Roots A→ℤ)
    (hq : RootPairing.GeckConstruction.e (s i)*ᵥintegerVector ℚ v=integerVector ℚ w) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥintegerVector K v=integerVector K w := by
  have hrat : (Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.E b (s i))*ᵥ
      integerVector ℚ v=integerVector ℚ w := by
    rw [CFSGGeckIntegralMatrices.map_E]
    exact hq
  exact column_of_rational K (CFSGGeckIntegralMatrices.E b (s i)) v w hrat

theorem root_cartan (K : Type*) [CommRing K] (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥPi.single (.inl (s i)) 1=
      (2:K) • Pi.single (.inr (s i:Roots A)) 1 := by
  have hq : RootPairing.GeckConstruction.e (s i)*ᵥ
      integerVector ℚ (Pi.single (.inl (s i)) (1:ℤ))=
      integerVector ℚ ((2:ℤ) • Pi.single (.inr (s i:Roots A)) (1:ℤ)) := by
    simp only [integerVector_zsmul,integerVector_single,Int.cast_one,Int.cast_ofNat]
    exact E_u_self A hs hp b (s i)
  simpa only [integerVector_zsmul,integerVector_single,Int.cast_one,Int.cast_ofNat] using
    root_column A hs hp b s K i _ _ hq

theorem root_positive (K : Type*) [CommRing K] (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥPi.single (.inr (s i:Roots A)) 1=0 := by
  have hq : RootPairing.GeckConstruction.e (s i)*ᵥ
      integerVector ℚ (Pi.single (.inr (s i:Roots A)) (1:ℤ))=integerVector ℚ 0 := by
    simp only [integerVector_single,Int.cast_one,integerVector_zero]
    exact E_v_self A hs hp b (s i)
  simpa only [integerVector_single,Int.cast_one,integerVector_zero] using
    root_column A hs hp b s K i _ _ hq

theorem root_negative (K : Type*) [CommRing K] (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) K false i*ᵥ
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1=Pi.single (.inl (s i)) 1 := by
  have hq : RootPairing.GeckConstruction.e (s i)*ᵥ
      integerVector ℚ (Pi.single (.inr (negativeIndex A hs hp (s i))) (1:ℤ))=
      integerVector ℚ (Pi.single (.inl (s i)) (1:ℤ)) := by
    simp only [integerVector_single,Int.cast_one]
    exact E_v_negative A hs hp b (s i)
  simpa only [integerVector_single,Int.cast_one] using root_column A hs hp b s K i _ _ hq

theorem second_literal (K : Type*) [CommRing K] (i : Fin r) :
    fieldSecond (realizationData A hs hp b s) K false i=
      Matrix.single (.inr (s i:Roots A)) (.inr (negativeIndex A hs hp (s i))) 1 := by
  ext j k
  simp [fieldSecond,realizationData,integerSecond,positiveSecond,Matrix.single_apply]

theorem second_cartan (K : Type*) [CommRing K] (i : Fin r) :
    fieldSecond (realizationData A hs hp b s) K false i*ᵥPi.single (.inl (s i)) 1=0 := by
  rw [second_literal,Matrix.mulVec_single_one]
  ext j
  simp [Matrix.single_apply]

theorem second_positive (K : Type*) [CommRing K] (i : Fin r) :
    fieldSecond (realizationData A hs hp b s) K false i*ᵥPi.single (.inr (s i:Roots A)) 1=0 := by
  have hne : (s i:Roots A)≠negativeIndex A hs hp (s i) :=
    RootPairing.ne_neg (rootPairing A hs hp) (s i)
  rw [second_literal,Matrix.mulVec_single_one]
  ext j
  simp [Matrix.single_apply,hne,Ne.symm hne]

theorem second_negative (K : Type*) [CommRing K] (i : Fin r) :
    fieldSecond (realizationData A hs hp b s) K false i*ᵥ
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1=Pi.single (.inr (s i:Roots A)) 1 := by
  rw [second_literal,Matrix.mulVec_single_one]
  ext j
  simp [Matrix.single_apply,Pi.single_apply,eq_comm]

theorem unit_cartan (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inl (s i)) 1=
      Pi.single (.inl (s i)) 1+(2:K) • Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_cartan,second_cartan,one_smul,one_pow,smul_zero,add_zero]

theorem unit_positive (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr (s i:Roots A)) 1=Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_positive,second_positive,one_smul,one_pow,smul_zero,add_zero]

theorem unit_negative (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1=
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1+Pi.single (.inl (s i)) 1+
        Pi.single (.inr (s i:Roots A)) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_negative,second_negative,one_smul,one_pow]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootColumns

import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylColumns

/-! Every Cartan column of the actual integral Geck Weyl word, over an
arbitrary coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckWeylBasic
open CFSGNormTwoGeckFieldWeylColumns CFSGNormTwoGeckIntegralRealization
open CFSGSerreQuadraticMatrix CFSGIntegerMatrixColumnTransport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_cartan_general (K : Type*) [CommRing K] (i : Fin r) (j : b.support) :
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
      Pi.single (.inl j) 1-((|b.cartanMatrix (s i) j|:ℤ):K) • Pi.single (.inl (s i)) 1 := by
  have hq : weylOperator A hs hp b (s i)
      (integerVector ℚ (Pi.single (.inl j) (1:ℤ)))=
      integerVector ℚ (Pi.single (.inl j) (1:ℤ)+
        (-|b.cartanMatrix (s i) j|) • Pi.single (.inl (s i)) (1:ℤ)) := by
    simpa only [integerVector_add,integerVector_zsmul,integerVector_neg,integerVector_single,Int.cast_one,
      Int.cast_neg,neg_smul,sub_eq_add_neg,RootPairing.GeckConstruction.u]
      using weyl_on_cartan A hs hp b (s i) j
  have hc := field_column A hs hp b s K i _ _ hq
  simpa only [integerVector_add,integerVector_zsmul,integerVector_neg,integerVector_single,Int.cast_one,
    Int.cast_neg,neg_smul,sub_eq_add_neg] using hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan

import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixColumnTransport

/-! The actual Weyl three-string columns in every coefficient ring.
They descend through the same integer word, not by reducing a rational
denominator in the coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylBasic CFSGNormTwoGeckWeylUnits
open CFSGSerreQuadraticMatrix CFSGIntegerMatrixColumnTransport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem field_column (K : Type*) [CommRing K] (i : Fin r)
    (v w : b.support⊕Roots A→ℤ)
    (hq : weylOperator A hs hp b (s i) (integerVector ℚ v)=integerVector ℚ w) :
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      integerVector K v=integerVector K w := by
  have hrat : (Int.castRingHom ℚ).mapMatrix
      (canonicalWeyl (realizationData A hs hp b s) ℤ i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℤ)*ᵥ
        integerVector ℚ v=integerVector ℚ w := by
    rw [map_canonicalWeyl_val,←Matrix.toLinAlgEquiv'_apply,rational_weyl_operator]
    exact hq
  have hfield := column_of_rational K
    (canonicalWeyl (realizationData A hs hp b s) ℤ i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℤ) v w hrat
  rw [map_canonicalWeyl_val] at hfield
  exact hfield

theorem weyl_cartan (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inl (s i)) 1= -Pi.single (.inl (s i)) 1 := by
  have hq : weylOperator A hs hp b (s i)
      (integerVector ℚ (Pi.single (.inl (s i)) (1:ℤ)))=
      integerVector ℚ (-Pi.single (.inl (s i)) (1:ℤ)) := by
    simpa only [integerVector_single,integerVector_neg,Int.cast_one,RootPairing.GeckConstruction.u]
      using (weyl_on_triple A hs hp b (s i)).1
  simpa only [integerVector_single,integerVector_neg,Int.cast_one] using
    field_column A hs hp b s K i _ _ hq

theorem weyl_positive (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr (s i:Roots A)) 1=Pi.single (.inr (negativeIndex A hs hp (s i))) 1 := by
  have hq : weylOperator A hs hp b (s i)
      (integerVector ℚ (Pi.single (.inr (s i:Roots A)) (1:ℤ)))=
      integerVector ℚ (Pi.single (.inr (negativeIndex A hs hp (s i))) (1:ℤ)) := by
    simpa only [integerVector_single,Int.cast_one,RootPairing.GeckConstruction.v]
      using (weyl_on_triple A hs hp b (s i)).2.1
  simpa only [integerVector_single,Int.cast_one] using field_column A hs hp b s K i _ _ hq

theorem weyl_negative (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr (negativeIndex A hs hp (s i))) 1=Pi.single (.inr (s i:Roots A)) 1 := by
  have hq : weylOperator A hs hp b (s i)
      (integerVector ℚ (Pi.single (.inr (negativeIndex A hs hp (s i))) (1:ℤ)))=
      integerVector ℚ (Pi.single (.inr (s i:Roots A)) (1:ℤ)) := by
    simpa only [integerVector_single,Int.cast_one,RootPairing.GeckConstruction.v]
      using (weyl_on_triple A hs hp b (s i)).2.2
  simpa only [integerVector_single,Int.cast_one] using field_column A hs hp b s K i _ _ hq

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylColumns

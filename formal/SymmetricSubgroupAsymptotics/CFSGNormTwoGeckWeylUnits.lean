import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylRootStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl

/-! The actual quadratic unit Weyl word has fourth power one over every
coefficient ring. The proof uses its SAME rational norm-two root columns
and then the actual integral coefficient polynomial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylBasic
open CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem fieldRoot_false (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) ℚ false i=RootPairing.GeckConstruction.e (s i) :=
  CFSGGeckIntegralMatrices.map_E b (s i)

theorem fieldRoot_true (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) ℚ true i=RootPairing.GeckConstruction.f (s i) :=
  CFSGGeckIntegralMatrices.map_F b (s i)

theorem rational_weyl_operator (i : Fin r) :
    Matrix.toLinAlgEquiv' (canonicalWeyl (realizationData A hs hp b s) ℚ i :
      Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=weylOperator A hs hp b (s i) := by
  rw [canonicalWeyl_operator,fieldRoot_false,fieldRoot_true]
  rfl

theorem rational_weyl_four (i : Fin r) : (canonicalWeyl (realizationData A hs hp b s) ℚ i)^4=1 := by
  apply Units.ext
  apply Matrix.toLinAlgEquiv'.injective
  rw [Units.val_pow_eq_pow_val,map_pow,rational_weyl_operator,Units.val_one,map_one]
  exact CFSGNormTwoGeckWeylRootStrings.weyl_four A hs hp b (s i)

theorem weyl_four (K : Type*) [CommRing K] (i : Fin r) :
    (canonicalWeyl (realizationData A hs hp b s) K i)^4=1 :=
  canonicalWeyl_four_of_rational (realizationData A hs hp b s) K i
    (rational_weyl_four A hs hp b s i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits

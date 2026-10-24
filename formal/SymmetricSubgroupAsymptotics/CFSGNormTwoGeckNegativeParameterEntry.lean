import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns

/-! A coefficient-one entry reads the actual negative simple-root
parameter in every characteristic. This uses the original quadratic
unit's Cartan/root triple, with no polynomial interpolation or division. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeParameterEntry
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckParameterTripleColumns
open CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem negative_parameter_entry (K : Type*) [CommRing K] (i : Fin r) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t :
      Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
        (.inl (s i)) (.inr (s i : Roots A))=t := by
  have h := congrFun (negative_positive A hs hp b s K i t) (.inl (s i))
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.add_apply,Pi.smul_apply,
    Pi.single_eq_same,Pi.single_apply,Sum.inl_ne_inr,Sum.inr_ne_inl,if_false,
    smul_eq_mul,mul_one,mul_zero,zero_add,add_zero] using h

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeParameterEntry

import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive

/-! The actual square Weyl word is the actual rank-one torus at -1.
Its adjacent simple-root action is therefore the parameter sign,
including in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareTorus
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckTorusConjugation CFSGNormTwoGeckWeylUnits
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem parameterWeyl_one (K : Type*) [Field K] (i : Fin r) :
    parameterWeyl A hs hp b s K i 1=canonicalWeyl (realizationData A hs hp b s) K i := by
  simp only [parameterWeyl,canonicalWeyl,Units.val_one,inv_one]

theorem parameterWeyl_neg_one (K : Type*) [Field K] (i : Fin r) :
    parameterWeyl A hs hp b s K i (-1)=
      (parameterWeyl A hs hp b s K i 1)⁻¹ := by
  simp only [parameterWeyl,Units.val_neg,Units.val_one,inv_neg,inv_one,neg_neg,
    _root_.mul_inv_rev,canonicalRoot_inverse,mul_assoc]

theorem torus_neg_one_eq_square (K : Type*) [Field K] (i : Fin r) :
    parameterTorus A hs hp b s K i (-1)=
      (canonicalWeyl (realizationData A hs hp b s) K i)^2 := by
  rw [parameterTorus,parameterWeyl_neg_one,parameterWeyl_one]
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  have hsq : w^2*w^2=1 := by
    simpa only [←pow_add] using weyl_four A hs hp b s K i
  calc
    w⁻¹*w⁻¹=(w^2)⁻¹ := by rw [pow_two,_root_.mul_inv_rev]
    _=w^2 := inv_eq_of_mul_eq_one_right hsq

theorem square_conjugate_adjacent (K : Type*) [Field K] (i j : Fin r)
    (hij : cartan b s i j= -1) (a : K) :
    (canonicalWeyl (realizationData A hs hp b s) K i)^2*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      ((canonicalWeyl (realizationData A hs hp b s) K i)^2)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false j (-a) := by
  have hpij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1 := by
    rw [integer_symmetric A hs,
      ←CFSGNormTwoGeckOffDiagonalCollecting.cartan_eq_integer_pairing A hs hp b s]
    exact hij
  have hh := torus_conjugate_positive A hs hp b s K i j (-1) a
  rw [torus_neg_one_eq_square,hpij] at hh
  simpa only [Units.val_neg,Units.val_one,zpow_neg_one,inv_neg,inv_one,mul_neg_one] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareTorus

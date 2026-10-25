import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseRootOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Sparse evaluation of one actual signed root matrix. The sum visits
only its displayed coefficient positions; no word matrix is built. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseAction
open CFSGFFourNormCertificateRootOperators CFSGFFourNormCertificateSparseRootOperators
open scoped BigOperators

def sparseStep (K : Type) [CommRing K] (neg : Bool) (i : Fin 4) (t : K)
    (v : Fin 26 → K) : Fin 26 → K := fun j =>
  v j + t * (∑ k ∈ firstRows neg i j, v k) +
    t^2 * (∑ k ∈ secondRows neg i j, v k)

theorem sparseStep_eq_mulVec (K : Type) [CommRing K] [CharP K 2]
    (neg : Bool) (i : Fin 4) (t : K) (v : Fin 26 → K) :
    sparseStep K neg i t v = (rootOperator K neg i t).mulVec v := by
  funext j
  symm
  change (∑ k : Fin 26, rootOperator K neg i t j k * v k) = _
  simp [rootOperator_entry, sparseStep, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum]

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseAction

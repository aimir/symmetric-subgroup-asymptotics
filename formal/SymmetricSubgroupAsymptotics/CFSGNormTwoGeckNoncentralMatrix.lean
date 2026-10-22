import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylColumns
import SymmetricSubgroupAsymptotics.CFSGQuadraticThreeStringNoncentral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Noncommutation is detected on the actual original root-matrix image.
No assertion about the full natural matrix commutant is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

private def unitEquiv {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (g : (Matrix I I K)ˣ) : (I→K)≃ₗ[K](I→K) :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv

theorem root_does_not_fix_weyl_root (K : Type) [Field K] (i : Fin r) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
        fieldRoot (realizationData A hs hp b s) K false i*
        (↑((canonicalWeyl (realizationData A hs hp b s) K i)⁻¹):Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*
      (↑((canonicalRoot (realizationData A hs hp b s) K false i 1)⁻¹):Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)≠
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      fieldRoot (realizationData A hs hp b s) K false i*
      (↑((canonicalWeyl (realizationData A hs hp b s) K i)⁻¹):Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  let U := canonicalRoot (realizationData A hs hp b s) K false i 1
  let W := canonicalWeyl (realizationData A hs hp b s) K i
  let e := fieldRoot (realizationData A hs hp b s) K false i
  let u : b.support⊕Roots A→K := Pi.single (.inl (s i)) 1
  let p : b.support⊕Roots A→K := Pi.single (.inr (s i:Roots A)) 1
  let m : b.support⊕Roots A→K := Pi.single (.inr (negativeIndex A hs hp (s i))) 1
  let l : (b.support⊕Roots A→K)→ₗ[K]K := LinearMap.proj (.inl (s i))
  have hn := CFSGQuadraticThreeStringNoncentral.conjugated_root_not_fixed
    (unitEquiv U) (unitEquiv W) (Matrix.toLinAlgEquiv' e) u p m l
    (CFSGNormTwoGeckFieldRootColumns.unit_cartan A hs hp b s K i)
    (CFSGNormTwoGeckFieldRootColumns.unit_positive A hs hp b s K i)
    (CFSGNormTwoGeckFieldRootColumns.unit_negative A hs hp b s K i)
    (CFSGNormTwoGeckFieldWeylColumns.weyl_cartan A hs hp b s K i)
    (CFSGNormTwoGeckFieldWeylColumns.weyl_positive A hs hp b s K i)
    (CFSGNormTwoGeckFieldWeylColumns.weyl_negative A hs hp b s K i)
    (CFSGNormTwoGeckFieldRootColumns.root_cartan A hs hp b s K i)
    (CFSGNormTwoGeckFieldRootColumns.root_positive A hs hp b s K i)
    (CFSGNormTwoGeckFieldRootColumns.root_negative A hs hp b s K i)
    (by simp [l,u,Pi.single_apply]) (by simp [l,m,Pi.single_apply])
  intro h
  apply hn
  have hh := congrArg Matrix.toLinAlgEquiv' h
  simpa only [map_mul] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix

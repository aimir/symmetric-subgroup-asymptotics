import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoLatticeReflections

/-! The SAME Geck matrices carry the full original integer-lattice
grading, not just a scalar height. Scalar coordinate functionals detect
this support without reducing any lattice coordinate modulo the field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckArbitraryHeightSupport CFSGSerreQuadraticMatrix
open CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def latticeWeight : b.support⊕Roots A→(n→ℤ)
  | .inl _=>0
  | .inr k=>k.val

theorem weight_proj (t : n) (j : b.support⊕Roots A) :
    weight A hs hp b (LinearMap.proj t) j=latticeWeight A hs hp b j t := by
  cases j <;> rfl

theorem support_of_coordinate_functionals {K : Type*} [Semiring K]
    (M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) (d : n→ℤ)
    (h : ∀t : n,Supported (weight A hs hp b (LinearMap.proj t))
      (fun w=>w+d t) M) :
    Supported (latticeWeight A hs hp b) (fun w=>w+d) M := by
  classical
  intro j k hjk
  by_contra hM
  apply hjk
  funext t
  by_contra ht
  apply hM
  apply h t j k
  simpa only [weight_proj,Pi.add_apply] using ht

def reflectionEquiv (i : Roots A) : (n→ℤ)≃+(n→ℤ) where
  toFun := CFSGNormTwoLatticeReflections.reflection (integerPairing A) i.val
  invFun := CFSGNormTwoLatticeReflections.reflection (integerPairing A) i.val
  left_inv := CFSGNormTwoLatticeReflections.reflection_involutive _ _ i.property
  right_inv := CFSGNormTwoLatticeReflections.reflection_involutive _ _ i.property
  map_add' := by
    intro x y
    simp only [CFSGNormTwoLatticeReflections.reflection,map_add,LinearMap.add_apply,add_smul]
    abel

variable [(rootPairing A hs hp).IsIrreducible] {r : ℕ} (s : Fin r≃b.support)

theorem field_E_lattice_support (K : Type*) [CommRing K] (i : Fin r) :
    Supported (latticeWeight A hs hp b) (fun w=>w+(s i:Roots A).val)
      (fieldRoot (realizationData A hs hp b s) K false i) := by
  apply support_of_coordinate_functionals
  intro t
  exact field_E_support A hs hp b s (LinearMap.proj t) K i

theorem field_second_lattice_support (K : Type*) [CommRing K] (i : Fin r) :
    Supported (latticeWeight A hs hp b) (fun w=>w+2 • (s i:Roots A).val)
      (fieldSecond (realizationData A hs hp b s) K false i) := by
  apply support_of_coordinate_functionals
  intro t
  simpa only [Pi.smul_apply,smul_eq_mul] using
    field_second_support A hs hp b s (LinearMap.proj t) K i

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
